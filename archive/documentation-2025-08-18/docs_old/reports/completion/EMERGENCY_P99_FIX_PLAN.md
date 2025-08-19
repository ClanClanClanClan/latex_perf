# Emergency P99 Fix Implementation Plan
*Based on Expert Analysis - August 16, 2025*

## Phase 1: Emergency Tail Latency Stabilization (24-48 hours)

### Task 1: Persistent Worker Implementation ⚡ CRITICAL
```ocaml
(* latex_perfectionist_resident_worker.ml *)
open Unix

let serve ~sock_path ~handler =
  (try Unix.unlink sock_path with _ -> ());
  let s = socket PF_UNIX SOCK_STREAM 0 in
  bind s (ADDR_UNIX sock_path); 
  listen s 32;
  
  (* Warm up critical paths *)
  Gc.full_major ();
  
  let rec loop () =
    let (c, _) = accept s in
    let ic = in_channel_of_descr c in
    let oc = out_channel_of_descr c in
    
    (* Length-prefixed protocol *)
    let len_bytes = really_input_string ic 4 in
    let msg_len = (* decode 4-byte length *) in
    let payload = really_input_string ic msg_len in
    
    let response = handler payload in
    output_string oc response; 
    flush oc;
    close c; 
    loop ()
  in loop ()
```

**Expected Impact**: Removes 10ms process spawn overhead immediately

### Task 2: Pre-fault Memory Pages
```ocaml
(* prepage.ml *)
open Bigarray

let prepage (ba : (char, int8_unsigned_elt, c_layout) Array1.t) =
  let len = Array1.dim ba in
  let step = 4096 in  (* Page size *)
  let acc = ref 0 in
  let get = Array1.unsafe_get in
  let rec loop i =
    if i < len then begin
      acc := !acc land (Char.code (get ba i)); 
      loop (i + step)
    end
  in
  loop 0;
  Sys.opaque_identity !acc |> ignore
```

**Expected Impact**: Eliminates 10-80ms page fault spikes

### Task 3: GC Fence Critical Section
```ocaml
(* gc_guard.ml *)
let with_quiet_gc f =
  let old = Gc.get () in
  let tuned = { old with
    Gc.minor_heap_size = 128 * 1024 * 1024;  (* 128MB *)
    space_overhead = 10_000;
    max_overhead = 1_000_000;
  } in
  Gc.full_major ();  (* Clear debt before entering *)
  Gc.set tuned;
  try
    let r = f () in
    Gc.set old; r
  with e -> 
    Gc.set old; raise e
```

**Expected Impact**: Prevents rare GC spikes during processing

### Task 4: Fix Measurement
```ocaml
let time_user_visible f =
  let t0 = Unix.gettimeofday () in
  let result = f () in
  let t1 = Unix.gettimeofday () in
  (result, (t1 -. t0) *. 1000.0)

(* In handler *)
let handle_request payload =
  let (doc_path, _flags) = decode_request payload in
  let (json, user_ms) = time_user_visible (fun () ->
    let mapped = map_file doc_path in
    prepage mapped;
    with_quiet_gc (fun () ->
      let tokens = tokenize_to_soa mapped in
      let issues = validate tokens in
      encode_json { issues; tokens = tokens.count }
    )
  ) in
  log_metrics { user_ms; tokens; bytes = file_size };
  json
```

### Task 5: Capacity Sentinel
```ocaml
(* After lexing *)
if produced_tokens >= soa_capacity then
  failwith (Printf.sprintf 
    "SoA capacity exceeded: %d tokens >= %d capacity" 
    produced_tokens soa_capacity);

if produced_tokens <> 276331 (* for canonical corpus *) then
  log_warning "Token count drift: expected 276331, got %d" produced_tokens;
```

---

## Expected Results After Phase 1

| Metric | Current | After Phase 1 | Target |
|--------|---------|---------------|--------|
| P50 | ~14ms | **9-12ms** | <15ms |
| P95 | ~30ms | **13-16ms** | <18ms |
| P99 | 86.6ms | **≤20ms** | <20ms |
| Max outlier | 280ms | <35ms | <50ms |

---

## Phase 2: L1 Integration (Days 3-5)

### Zero-Copy Expansion Iterator
```ocaml
(* Avoid allocating expanded token arrays *)
type expansion_view = 
  | Original of int (* index in SoA *)
  | Synthetic of string * int * int (* macro expansion, start, len *)

let expand_zero_copy soa macro_table =
  (* Return iterator that yields expansion_views *)
  (* Use off-heap scratch ring for synthetic tokens *)
  (* No intermediate arrays allocated *)
```

---

## Phase 3: Production Hardening (Days 6-10)

### Monitoring Output
```json
{
  "ts": 1729184000.123,
  "commit": "abc123",
  "corpus": "perf_smoke_big.tex",
  "bytes": 1101324,
  "tokens": 276331,
  "user_ms": 11.2,
  "p50_ms": 10.8,
  "p95_ms": 15.3,
  "p99_ms": 19.1,
  "gc_major_delta": 0,
  "rss_mb": 42.3,
  "platform": "macOS_14_M2",
  "build": "flambda2"
}
```

---

## What to Retract/Correct Immediately

### Retract
- ❌ "Guaranteed P99 < 10ms"
- ❌ "3-4ms for 1.1MB" (internal timing)
- ❌ "645x better than target"

### Replace With
- ✅ "P99 < 20ms on 1.1MB corpus (user-visible latency)"
- ✅ "Measured via persistent worker, 1000 iterations"
- ✅ "Platform: macOS 14, OCaml 5.2, flambda2"

---

## 72-Hour Sprint

### Day 1 (Today)
- [ ] Implement persistent worker with Unix socket
- [ ] Add prepage function to all file operations
- [ ] Wrap critical path in with_quiet_gc
- [ ] Switch ALL metrics to user-visible timing

### Day 2
- [ ] Add capacity overflow detection
- [ ] Publish corrected performance claims
- [ ] Add CI gate: fail if P99_user > 20ms

### Day 3-5
- [ ] Implement zero-copy L1 expansion
- [ ] Scale to 10+ validator families
- [ ] Document exact reproduction steps

---

## Success Criteria

✅ P99 < 20ms on 1.1MB corpus (500+ iterations)
✅ No silent token truncation
✅ L1 macros actually expanded
✅ User-visible metrics only
✅ Reproducible benchmarks

---

## Commands to Test Success

```bash
# Start persistent worker
./latex_perfectionist_resident_worker --serve /tmp/lp.sock &

# Run benchmark (expect P99 < 20ms)
for i in {1..500}; do
  ./latex_perfectionist_client /tmp/lp.sock \
    corpora/perf/perf_smoke_big.tex
done | analyze_p99

# Verify token count
./latex_perfectionist_client /tmp/lp.sock \
  corpora/perf/perf_smoke_big.tex --json | \
  jq '.tokens' # Must be 276331

# Check GC quiet
./latex_perfectionist_client /tmp/lp.sock \
  corpora/perf/perf_smoke_big.tex --gc-stats | \
  jq '.gc_major_delta' # Should be 0
```