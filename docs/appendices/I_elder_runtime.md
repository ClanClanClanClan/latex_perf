# Appendix I -- Incremental Elder Runtime Architecture

Revision 2026-04-05. The Elder runtime is the incremental analysis engine that
manages document state across edits. It orchestrates the five-layer pipeline
(L0--L4), maintains cross-layer consistency via version vectors, and enables
sub-millisecond response times on keystroke edits.

---

## I-1 Design Principles

1. **Bounded delta-propagation.** Each layer has a locality lemma; only O(delta)
   work per edit.
2. **Layer-pure / cache-impure.** Validator kernels are pure functions; Elder
   owns all mutation (caching, generation counters, snapshots).
3. **Strong invariants or rollback.** On violation, roll back the child layer
   only; parent artefacts remain valid.
4. **Always non-blocking.** Hot path uses OCaml 5.x `Atomic` + lock-free queue.
5. **Proof-carrying snapshots.** Cache entries include `.vo` certificate hashes
   (spec; not yet fully implemented).

---

## I-2 Core Components

### I-2.1 Layer Sync (`layer_sync.ml`)

Ensures validators observe consistent snapshots across layers.

**Types:**

```ocaml
(* latex-parse/src/layer_sync.ml *)
type layer_id = L0 | L1 | L2 | L3 | L4

type version_vector = { gen : int; parent_gen : int }

type 'a layer_state = {
  layer   : layer_id;
  version : version_vector;
  data    : 'a;
}

type 'a snapshot = {
  generation : int;
  states     : 'a layer_state list;
}
```

**Generation counter (atomic for cross-domain safety):**

```ocaml
let _generation = Atomic.make 0
let next_gen () = Atomic.fetch_and_add _generation 1
let current_gen () = Atomic.get _generation
```

**Version vector operations:**

```ocaml
let accepts_delta (parent : version_vector) (child : version_vector) : bool =
  child.parent_gen = parent.gen

let advance (parent : version_vector) : version_vector =
  { gen = next_gen (); parent_gen = parent.gen }
```

Layer N accepts deltas from Layer N-1 if and only if `child.parent_gen =
parent.gen`. This ensures no stale deltas are applied.

**Consistency check:**

```ocaml
let is_consistent (snap : 'a snapshot) : bool =
  (* Sort states by layer ordinal, then check each adjacent pair *)
  let rec check_pairs = function
    | [] | [_] -> true
    | parent :: (child :: _ as rest) ->
        accepts_delta parent.version child.version && check_pairs rest
  in
  check_pairs sorted
```

**Rollback:**

```ocaml
type rollback_result = Rolled_back | No_rollback_needed

let rollback_child (snap : 'a snapshot) (child_layer : layer_id) :
    'a snapshot * rollback_result =
  let new_states = List.filter (fun s -> s.layer <> child_layer) snap.states in
  if List.length new_states < List.length snap.states then
    ({ generation = snap.generation; states = new_states }, Rolled_back)
  else (snap, No_rollback_needed)
```

**Proof:** `proofs/SnapshotConsistency.v` -- snapshot reads are consistent
(either old or new, never interleaved).

### I-2.2 Event Bus (`event_bus.ml`)

Pub/sub event dispatch for semantic deltas.

**Event type:**

```ocaml
(* latex-parse/src/event_bus.ml *)
type event =
  | LabelDefined     of { key : string; position : int }
  | RefUsed          of { key : string; position : int; command : string }
  | SectionStarted   of { level : int; title : string; position : int }
  | EnvironmentOpened of { name : string; position : int }
  | EnvironmentClosed of { name : string; position : int }
  | DocumentBegin    of int
  | DocumentEnd      of int
```

**Bus type:**

```ocaml
type handler = event -> unit

type bus = {
  mutable handlers    : (string * handler) list;
  mutable event_count : int;
}
```

**Operations:**

```ocaml
let subscribe (bus : bus) (name : string) (handler : handler) : unit
let unsubscribe (bus : bus) (name : string) : unit
let publish (bus : bus) (event : event) : unit
```

**Event generation:** `scan_and_publish` scans source text for `\label`, `\ref`,
`\section`, `\begin`, `\end` and publishes corresponding events.

**Global bus:** A singleton `_global_bus` provides module-level `publish_global`
and `subscribe_global` for convenience.

### I-2.3 Lock-Free Queue (`lockfree_queue.ml`)

MPMC (multi-producer, multi-consumer) bounded ring buffer using OCaml 5.x
`Atomic` for compare-and-swap.

```ocaml
(* latex-parse/src/lockfree_queue.ml *)
type 'a slot = { mutable data : 'a option; seq : int Atomic.t }

type 'a t = {
  buffer : 'a slot array;
  mask   : int;              (* capacity - 1, for fast modulo *)
  head   : int Atomic.t;     (* consumer reads from head *)
  tail   : int Atomic.t;     (* producer writes to tail *)
}
```

**Design:** Power-of-two ring buffer with per-slot sequence numbers for ABA
protection.

**Key operations:**

```ocaml
let try_push (q : 'a t) (v : 'a) : bool =
  let rec loop () =
    let tail = Atomic.get q.tail in
    let idx = tail land q.mask in
    let slot = q.buffer.(idx) in
    let seq = Atomic.get slot.seq in
    let diff = seq - tail in
    if diff = 0 then                            (* slot available *)
      if Atomic.compare_and_set q.tail tail (tail + 1) then (
        slot.data <- Some v;
        Atomic.set slot.seq (tail + 1);
        true)
      else loop ()                              (* CAS failed, retry *)
    else if diff < 0 then false                 (* queue full *)
    else loop ()                                (* another producer, retry *)
  in loop ()

let try_pop (q : 'a t) : 'a option =
  (* Symmetric: CAS on head, check seq = head + 1 *)
```

**Blocking variants:** `push` and `pop` spin with `Domain.cpu_relax()`.

**Target throughput:** 8M events/sec on 4 cores.

**Capacity:** Always rounded up to the next power of two for mask-based modulo.

### I-2.4 Dirty-Region Detection

#### Suffix Array (`suffix_array.ml`)

O(n log^2 n) construction, O(log n) search:

```ocaml
(* latex-parse/src/suffix_array.ml *)
type t = { text : string; sa : int array }

let build (text : string) : t =
  let sa = Array.init n (fun i -> i) in
  Array.sort (fun i j -> (* lexicographic suffix comparison *)) sa;
  { text; sa }

let search (arr : t) (pattern : string) : int list =
  (* Binary search for first and last occurrence *)
```

#### Dirty Region Computation

```ocaml
type dirty_region = { start_pos : int; end_pos : int }

let find_dirty_regions (old_text : string) (new_text : string) :
    dirty_region list =
  (* Scan forward from start: find first differing byte *)
  (* Scan backward from end: find last differing byte *)
  [{ start_pos = !start; end_pos = !new_end + 1 }]
```

Returns the minimal `[start, end)` byte range that differs between old and new
source. Only the dirty region needs re-processing.

### I-2.5 Cache System (`cache_key.ml`)

**Cache key:**

```ocaml
(* latex-parse/src/cache_key.ml *)
type cache_key = {
  source_hash     : string;    (* DJB2 hash of source *)
  validator_count : int;
  language        : string;
}
```

**Hash computation:**

```ocaml
let hash_string (s : string) : string =
  let h = ref 5381 in
  String.iter (fun c -> h := (!h * 33) + Char.code c) s;
  Printf.sprintf "%016x" !h
```

DJB2 hash -- fast, sufficient for cache indexing.

**Cache entry with TTL:**

```ocaml
type 'a cache_entry = {
  _key       : cache_key;
  results    : 'a;
  created_at : float;
  ttl_seconds: float;
}

type 'a cache = {
  tbl         : (string, 'a cache_entry) Hashtbl.t;
  mutable hits   : int;
  mutable misses : int;
  default_ttl : float;    (* default: 3600.0 seconds *)
}
```

**Lookup with TTL enforcement:**

```ocaml
let lookup (c : 'a cache) (key : cache_key) : 'a option =
  match Hashtbl.find_opt c.tbl (key_to_string key) with
  | Some entry ->
      if Unix.gettimeofday () -. entry.created_at < entry.ttl_seconds then
        (c.hits <- c.hits + 1; Some entry.results)
      else
        (Hashtbl.remove c.tbl ks; c.misses <- c.misses + 1; None)
  | None -> (c.misses <- c.misses + 1; None)
```

**Statistics:**

```ocaml
let stats (c : 'a cache) : string =
  Printf.sprintf "hits=%d misses=%d rate=%.1f%% entries=%d"
    c.hits c.misses (hit_rate c *. 100.0) (Hashtbl.length c.tbl)
```

**Global cache:** A singleton instance of type `Validators_common.result list cache`
for the validator engine.

---

## I-3 Dependency DAG (`validator_dag.ml`)

### I-3.1 Validator Metadata

```ocaml
(* latex-parse/src/validator_dag.ml *)
type phase = L0 | L1 | L2 | L3 | L4

type validator_meta = {
  id        : string;
  phase     : phase;
  provides  : string list;
  requires  : string list;
  conflicts : string list;
}
```

### I-3.2 DAG Construction (Kahn's Algorithm)

```ocaml
let build_dag (metas : validator_meta list) : (dag, string) result =
  (* 1. Build capability -> provider index *)
  (* 2. Build edges: if A requires C and B provides C, edge (A, B) *)
  (* 3. Topological sort via Kahn's algorithm *)
  (*    - Initialize queue with in-degree-0 nodes *)
  (*    - Pop node, reduce in-degree of dependents *)
  (*    - If all nodes visited: Ok; else: Error "Cycle detected" *)
```

### I-3.3 Conflict Resolution

```ocaml
type conflict = { rule_a : string; rule_b : string; reason : string }

let resolve_conflict a b severity_a severity_b : string =
  (* Priority tuple: (severity DESC, phase_ordinal ASC, id_lex ASC) *)
```

### I-3.4 Phase Ordering

```ocaml
let phase_ordinal = function
  | L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4

let phase_of_string = function
  | "L0" | "L0_Lexer"      -> L0
  | "L1" | "L1_Expanded"   -> L1
  | "L2" | "L2_Ast"        -> L2
  | "L3" | "L3_Semantics"  -> L3
  | "L4" | "L4_Style"      -> L4
  | _ -> L0
```

---

## I-4 Semantic State (`semantic_state.ml`)

### I-4.1 Data Model

```ocaml
(* latex-parse/src/semantic_state.ml *)
type label_entry = {
  key      : string;
  position : int;
  prefix   : string;    (* "fig:", "eq:", "sec:", "tab:", or "" *)
}

type ref_entry = {
  key      : string;
  position : int;
  command  : string;    (* "ref", "eqref", "autoref", "cref", "Cref" *)
}

type semantic_state = {
  labels           : label_entry list;
  refs             : ref_entry list;
  duplicate_labels : string list;
  undefined_refs   : string list;
  forward_refs     : string list;
}
```

### I-4.2 Analysis

`analyze : string -> semantic_state` extracts all labels and refs, then computes:

- **Duplicate labels:** Same key appears more than once
- **Undefined refs:** Ref key not found in any label
- **Forward refs:** Ref appears before its label in source order

Reference commands scanned: `\ref`, `\eqref`, `\autoref`, `\cref`, `\Cref`.

### I-4.3 Thread-Local State

```ocaml
let _state_tbl : (int, semantic_state) Hashtbl.t = Hashtbl.create 4

let set_state (st : semantic_state) : unit =
  Hashtbl.replace _state_tbl (Thread.id (Thread.self ())) st

let get_state () : semantic_state option =
  Hashtbl.find_opt _state_tbl (Thread.id (Thread.self ()))
```

Thread-local storage ensures validators running in parallel do not interfere
with each other's semantic state.

---

## I-5 Evidence Scoring (`evidence_scoring.ml`)

### I-5.1 Confidence Levels

```ocaml
(* latex-parse/src/evidence_scoring.ml *)
type confidence = High | Medium | Low

type scored_result = {
  id              : string;
  severity        : Validators_common.severity;
  message         : string;
  count           : int;
  confidence      : confidence;
  evidence_weight : float;   (* 0.0 to 1.0 *)
}
```

### I-5.2 Scoring Logic

```ocaml
let confidence_of_rule (id : string) (vpd_ids : string list) : confidence =
  if List.mem id vpd_ids then High      (* VPD-certified: proven correct *)
  else match prefix with
  | "TYPO" | "ENC" | "CHAR" | "SPC" -> High    (* lexical, exact patterns *)
  | "MATH" | "DELIM" | "SCRIPT" | "CHEM" -> Medium  (* structural *)
  | "STYLE" | "LANG" -> Low                    (* heuristic *)
  | _ -> Medium

let weight_of_confidence = function
  | High   -> 1.0
  | Medium -> 0.7
  | Low    -> 0.4
```

### I-5.3 Filtering

```ocaml
type scoring_config = {
  min_confidence  : confidence;
  min_weight      : float;
  boost_vpd_rules : bool;
}
```

Users can filter results by minimum confidence level or weight threshold.

---

## I-6 Float Tracking (`float_tracking.ml`)

Tracks distance between `\begin{figure}` and `\ref{fig:...}`:

```ocaml
(* latex-parse/src/float_tracking.ml *)
type float_entry = {
  kind     : string;       (* "figure", "table" *)
  label    : string option;
  position : int;
  line     : int;
}

type float_distances = {
  entries          : (float_entry * ref_entry * int) list;
  max_distance     : int;
  before_first_ref : float_entry list;
}
```

Used by:
- FIG-018: float distance > 3 pages
- FIG-015: figure before first reference

---

## I-7 Section Rebalance (`section_rebalance.ml`)

Section tree extraction and renumbering:

```ocaml
(* latex-parse/src/section_rebalance.ml *)
type section_node = {
  level         : int;    (* 0=chapter, 1=section, 2=subsection, 3=subsubsection *)
  title         : string;
  number        : int;    (* ordinal within parent *)
  label         : string option;
  children      : section_node list;
  source_offset : int;
}

type violation = {
  v_title              : string;
  v_expected_max_level : int;
  v_actual_level       : int;
  v_offset             : int;
}
```

Detects level-skip violations (e.g., `\section` directly followed by
`\subsubsection` without an intervening `\subsection`).

---

## I-8 Execution Flow

```
Edit event (keystroke)
  |
  +-- find_dirty_regions(old_src, new_src)
  |     -> { start_pos = 142; end_pos = 156 }
  |
  +-- cache_key.compute(new_src, validators, lang)
  |     -> hash = 0x7F3A2B1C
  |     -> cache miss (source changed)
  |
  +-- layer_sync.next_gen()
  |     -> generation = 47
  |
  +-- L0 tokenize (full document via tokenizer_lite.ml)
  +-- L1 expand (macro catalogue via simple_expander.ml)
  +-- L2 parse (PEG recursive descent via parser_l2.ml)
  +-- semantic_state.analyze(src)
  |     +-- extract labels/refs
  |     +-- compute duplicates/undefined/forward
  +-- event_bus.scan_and_publish(bus, src)
  +-- run_all validators
  |     +-- validator_dag.build_dag (startup only)
  |     +-- iterate in topological order
  |     +-- evidence_scoring.score_result per result
  |     +-- collect results
  |
  +-- cache_key.store(hash, results)
  |
  +-- Return diagnostics
```

---

## I-9 Cross-Layer Consistency Protocol

Resolves Moderate Concern #1 from spec audit.

| Concept | Decision |
|---------|----------|
| Version Vector | `{ gen; parent_gen }` per artefact |
| Memory Barrier | `Atomic` generation counter; `fetch_and_add` |
| Rollback | On error, roll back child layer only |
| Consistency Window | At most one generation |
| Proof | `proofs/SnapshotConsistency.v` |

---

## I-10 Performance Characteristics

### I-10.1 Measured Results (M2 Pro, 3.5 GHz, 32 GiB, 2026-02-22)

| Operation | Target | Measured |
|-----------|--------|----------|
| Full document (1.1 MB) p95 | <= 25 ms | 3.25 ms |
| Edit window (4 KB) p95 | <= 1 ms | 0.075 ms |
| First-token p95 | <= 350 us | 27 us |
| Cache hit | O(1) | < 1 us |
| Dirty-region detection | O(n) | < 0.1 ms |

### I-10.2 Per-Layer Budget (Spec Targets)

| Layer | Max Latency | Notes |
|-------|------------|-------|
| L0 | 80 us / 4 KiB edit | Tokenizer + catcode |
| L1 | 200 us | Fuel-bounded expansion |
| L2 | 300 us | Window re-parse |
| L3 | 250 us | Semantic state |
| L4 | 120 us / paragraph | Style heuristics |
| Elder dispatch | <= 40 us | Dispatch + telemetry |
| Elder total | <= 1 ms | End-to-end budget |

---

## I-11 Error Handling

### I-11.1 Error Propagation

Each validator returns `result option`. Validators that crash (uncaught
exception) are disabled for the current run; other validators continue.

### I-11.2 Recovery Strategies

| Fault | Detection | Resolution |
|-------|-----------|------------|
| Cache key mismatch | Hash comparison | Re-run full pipeline |
| Validator exception | `try`/`with` | Disable validator; log error |
| Layer version mismatch | `accepts_delta` check | Rollback child; re-compute |
| Cycle in DAG | Kahn's sort incomplete | Bootstrap failure (startup) |

### I-11.3 Error Collection

```ocaml
(* Errors collected in document.errors list *)
type error = { source : string; message : string; position : int option }
```

---

## I-12 Proof Obligations

| File | Theorem | Status |
|------|---------|--------|
| `proofs/ElderProofs.v` | `update_preserves_length` | QED |
| `proofs/ElderProofs.v` | `update_at_correct` | QED |
| `proofs/SnapshotConsistency.v` | Snapshot read consistency | QED |
| `proofs/ValidatorGraphProofs.v` | DAG acyclicity | QED |
| `proofs/SplitPreservesOrder.v` | Sentence split preserves order | QED |
| `proofs/SectionRebalance.v` | Renumbering preserves structure | QED |
| `proofs/Arena_safe.v` | Arena memory safety | QED |
| `proofs/InterpLocality.v` | Interpreter locality | QED |
| `proofs/ListWindow.v` | List windowing correctness | QED |
| `proofs/LabelsUnique.v` | Label uniqueness | QED |

---

## I-13 Key Source Files

| File | Lines | Purpose |
|------|-------|---------|
| `latex-parse/src/layer_sync.ml` | 72 | Version vectors, snapshots, rollback |
| `latex-parse/src/event_bus.ml` | 72 | Pub/sub event dispatch |
| `latex-parse/src/lockfree_queue.ml` | 103 | MPMC ring buffer (Atomic CAS) |
| `latex-parse/src/cache_key.ml` | 93 | DJB2 hash, TTL cache |
| `latex-parse/src/validator_dag.ml` | 139 | Kahn's topo sort, conflict resolution |
| `latex-parse/src/semantic_state.ml` | 142 | Label/ref tracking, thread-local state |
| `latex-parse/src/evidence_scoring.ml` | 73 | Confidence-weighted results |
| `latex-parse/src/suffix_array.ml` | 104 | O(n log^2 n) build, dirty regions |
| `latex-parse/src/float_tracking.ml` | 113 | Float/ref distance tracking |
| `latex-parse/src/section_rebalance.ml` | ~120 | Section tree extraction |
| `latex-parse/src/sentence_split.ml` | ~80 | High-throughput sentence splitter |
| `latex-parse/src/xxh64.ml` | 117 | Scalar xxHash64 + SIMD FFI |

---

## I-14 Spec Features Not Yet Implemented

The spec describes several features that are not yet in the codebase:

| Feature | Spec Section | Status |
|---------|-------------|--------|
| 4 KiB chunk store with BLAKE3 Merkle tree | I-3 | Not implemented; using dirty-region scan |
| EDF scheduler with utilisation bound | I-6 | Not implemented; sequential execution |
| Proof-Carrying Snapshot (PCS) binary format | I-10 | Not implemented |
| gRPC IPC API | I-11 | Not implemented |
| GPU off-load plugin trait | I-12 | Not implemented |
| Remote cache (Redis/S3) | I-12 | Not implemented |
| Bump arenas for AST nodes | I-8 | Not implemented; standard OCaml GC |

---

## I-15 Roadmap (v25 to v26)

| Milestone | Target | Description |
|-----------|--------|-------------|
| Chunk store | v26 | BLAKE3 Merkle tree for fine-grained caching |
| EDF scheduler | v26 | Real-time scheduling with utilisation bound |
| gRPC IPC | v26 | Streaming Validate/SnapshotSave/SnapshotLoad |
| Snapshot compression | v26 | Zstd-dict on CBOR payload |
| Causal CRDT bridge | v27 | Real-time collaborative editing |

---

End of Appendix I.
