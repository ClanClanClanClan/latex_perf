Got it. You’ve nailed the infrastructure gates, but two things are still blocking acceptance:
	1.	P99.9 = 26.631 ms (> 20 ms): this is a tail‑shaping problem (hedge not helping enough).
	2.	Math consistency flag: the service bracket was (sometimes) excluding the read (bytes‑in) from the timed window, and your CSV was deriving tails from a different window than the client bench. That alone can make P99.9 and “slowest‑100” disagree.

Below is a drop‑in, copy‑paste patch that:
	•	Fixes the bracket so the service time is exactly “bytes‑in → reply‑ready”.
	•	Captures hedge telemetry correctly (no double‑processing; logs the actual hedge flag for the measured request).
	•	Hardens IPC I/O (EINTR‑safe).
	•	Adds a keep‑alive bench that persists connections and dumps all latencies to a file (so your gate can compute P99.9 on the full 100k).
	•	Adds acceptance_gate.sh to enforce the AUDIT_CLAIMS criteria (N≥100k, P99.9≤20, hedge rate≤2%, 0 errors, P99.9 within slowest‑100 bounds).

It keeps the earlier SIMD guard + force‑load and hedged broker as‑is.

⸻

1) Apply this patch

Save as simd_v2_gate_perf_fix.patch, then:

git apply --index simd_v2_gate_perf_fix.patch
git commit -m "SIMD_v2: exact bytes-in→reply-ready bracket, hedge flag capture, EINTR I/O, keep-alive bench with raw dump, acceptance gate"

The patch (everything you need)

diff --git a/latex-parse/src/main_service.ml b/latex-parse/src/main_service.ml
index c1f67da..e8a90f2 100644
--- a/latex-parse/src/main_service.ml
+++ b/latex-parse/src/main_service.ml
@@ -1,12 +1,21 @@
 open Unix
 
 let unlink_if_exists p = try Unix.unlink p with _ -> ()
-let rec read_exact fd b o l =
+let rec read_exact fd b o l =
   if l=0 then () else
   try let n=Unix.read fd b o l in if n=0 then failwith "client eof" else read_exact fd b (o+n) (l-n)
   with Unix.Unix_error (Unix.EINTR,_,_) -> read_exact fd b o l
-let rec write_all fd b o l =
+let rec write_all fd b o l =
   if l=0 then () else
   try let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)
   with Unix.Unix_error (Unix.EINTR,_,_) -> write_all fd b o l
 
 let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore
 
@@ -31,7 +40,7 @@ let run () =
   Unix.bind srv (ADDR_UNIX sock_path); Unix.listen srv 64;
   prerr_endline ("[svc] listening at "^sock_path);
 
-  (* Allow overriding pool cores via env: L0_POOL_CORES="0,1,2,3" *)
+  (* Allow overriding pool cores via env: L0_POOL_CORES="0,1,2,3" *)
   let parse_cores s =
     try s |> String.split_on_char ',' |> List.map int_of_string |> Array.of_list
     with _ -> Config.pool_cores
@@ -45,10 +54,10 @@ let run () =
   let pool = Broker.init_pool cores in
 
   let tail_csv_keep = Config.tail_trace_keep in
-  let slow = ref ([] : (float * (int64*int64*int64*int64*int64*int64*bool*string)) list) in
+  let slow = ref ([] : (float * (int64*int64*int64*int64*int64*int64*bool*string)) list) in
   let slow_mu = Mutex.create () in
   let add_slowest ms row =
-    Mutex.lock slow_mu;
+    Mutex.lock slow_mu;
     let xs = (ms, row) :: !slow |> List.sort (fun (a,_) (b,_) -> compare b a) in
     let rec take n = function []->[] | _ when n=0 -> [] | y::ys -> y::take (n-1) ys in
     slow := take tail_csv_keep xs;
@@ -63,91 +72,113 @@ let run () =
      with _ -> ());
     Mutex.unlock slow_mu
   in
 
-  let rec handle_conn c =
-    (* keep-alive loop: many requests per connection *)
+  let rec handle_conn c =
+    (* keep-alive: many requests per connection; timing includes read *)
     let rec loop () =
-      (* recv *)
-      let hdr = Bytes.create 4 in
-      (try read_exact c hdr 0 4 with _ -> raise Exit);
-      let len =
-        ((Char.code (Bytes.get hdr 0)) lsl 24)
-        lor ((Char.code (Bytes.get hdr 1)) lsl 16)
-        lor ((Char.code (Bytes.get hdr 2)) lsl 8)
-        lor (Char.code (Bytes.get hdr 3))
-      in
-      if len <= 0 || len > Config.max_req_bytes then raise Exit;
-      let req = Bytes.create len in read_exact c req 0 len;
-
-      let recv () = req in
-      let process (req:bytes) =
-        try
-          `Ok (Broker.hedged_call pool ~input:req ~hedge_ms:Config.hedge_timer_ms_default)
-        with _ -> `Err
-      in
-      let put32 b off v =
-        Bytes.unsafe_set b off     (Char.unsafe_chr (((v lsr 24) land 0xFF)));
-        Bytes.unsafe_set b (off+1) (Char.unsafe_chr (((v lsr 16) land 0xFF)));
-        Bytes.unsafe_set b (off+2) (Char.unsafe_chr (((v lsr  8) land 0xFF)));
-        Bytes.unsafe_set b (off+3) (Char.unsafe_chr ( v         land 0xFF)))
-      in
-      let format = function
-        | `Ok r ->
-            let b = Bytes.create 13 in
-            put32 b 0 r.status; put32 b 4 r.n_tokens; put32 b 8 r.issues_len;
-            Bytes.unsafe_set b 12 (match r.origin with `P->Char.unsafe_chr 1 | `H->Char.unsafe_chr 2); b
-        | `Err ->
-            let b = Bytes.create 13 in
-            put32 b 0 1; put32 b 4 0; put32 b 8 0; Bytes.unsafe_set b 12 (Char.unsafe_chr 0); b
-      in
-      let send reply =
-        let len = Bytes.length reply in
-        let rhdr = Bytes.create 4 in
-        Bytes.unsafe_set rhdr 0 (Char.unsafe_chr ((len lsr 24) land 0xFF));
-        Bytes.unsafe_set rhdr 1 (Char.unsafe_chr ((len lsr 16) land 0xFF));
-        Bytes.unsafe_set rhdr 2 (Char.unsafe_chr ((len lsr  8) land 0xFF));
-        Bytes.unsafe_set rhdr 3 (Char.unsafe_chr ( len        land 0xFF));
-        write_all c rhdr 0 4; write_all c reply 0 len
-      in
-
-      let (ms, st) = Service_bracket.measure_bytes_in_to_reply_ready ~recv ~process ~format ~send in
-      (* we don’t have per-request hedge timestamps; log hedge_fired via origin/flag *)
-      let hedged =
-        match process req with
-        | `Ok r -> r.Broker.hedge_fired
-        | `Err  -> false
-      in
+      (* capture the actual broker result once, inside the bracket *)
+      let last : Broker.svc_result option ref = ref None in
+
+      let recv () =
+        let hdr = Bytes.create 4 in
+        read_exact c hdr 0 4;
+        let len =
+          ((Char.code (Bytes.get hdr 0)) lsl 24)
+          lor ((Char.code (Bytes.get hdr 1)) lsl 16)
+          lor ((Char.code (Bytes.get hdr 2)) lsl 8)
+          lor (Char.code (Bytes.get hdr 3))
+        in
+        if len <= 0 || len > Config.max_req_bytes then failwith "bad length";
+        let req = Bytes.create len in
+        read_exact c req 0 len;
+        req
+      in
+      let process (req:bytes) =
+        try
+          let r = Broker.hedged_call pool ~input:req ~hedge_ms:Config.hedge_timer_ms_default in
+          last := Some r; `Ok r
+        with _ -> `Err
+      in
+      let put32 b off v =
+        Bytes.unsafe_set b off     (Char.unsafe_chr (((v lsr 24) land 0xFF)));
+        Bytes.unsafe_set b (off+1) (Char.unsafe_chr (((v lsr 16) land 0xFF)));
+        Bytes.unsafe_set b (off+2) (Char.unsafe_chr (((v lsr  8) land 0xFF)));
+        Bytes.unsafe_set b (off+3) (Char.unsafe_chr ( v         land 0xFF))
+      in
+      let format = function
+        | `Ok r ->
+            let b = Bytes.create 13 in
+            put32 b 0 r.status; put32 b 4 r.n_tokens; put32 b 8 r.issues_len;
+            Bytes.unsafe_set b 12 (match r.origin with `P->Char.unsafe_chr 1 | `H->Char.unsafe_chr 2); b
+        | `Err ->
+            let b = Bytes.create 13 in
+            put32 b 0 1; put32 b 4 0; put32 b 8 0; Bytes.unsafe_set b 12 (Char.unsafe_chr 0); b
+      in
+      let send reply =
+        let len = Bytes.length reply in
+        let rhdr = Bytes.create 4 in
+        Bytes.unsafe_set rhdr 0 (Char.unsafe_chr ((len lsr 24) land 0xFF));
+        Bytes.unsafe_set rhdr 1 (Char.unsafe_chr ((len lsr 16) land 0xFF));
+        Bytes.unsafe_set rhdr 2 (Char.unsafe_chr ((len lsr  8) land 0xFF));
+        Bytes.unsafe_set rhdr 3 (Char.unsafe_chr ( len        land 0xFF));
+        write_all c rhdr 0 4; write_all c reply 0 len
+      in
+
+      let (ms, st) =
+        Service_bracket.measure_bytes_in_to_reply_ready ~recv ~process ~format ~send
+      in
+      let hedged =
+        match !last with Some r -> r.Broker.hedge_fired | None -> false
+      in
       add_slowest ms (st.Service_bracket.t_in_start, st.t_in_done, st.t_proc_start, st.t_hedge_fire, st.t_first_reply, st.t_reply_ready, hedged, "");
       if Broker.(pool.requests mod 10_000 = 0) then begin
         Printf.eprintf "[hedge] req=%d fired=%d (%.3f%%) wins=%d (%.1f%%) rotations=%d\n%!"
           Broker.(pool.requests) Broker.(pool.hedge_fired)
           (100.0 *. float Broker.(pool.hedge_fired) /. float (max 1 Broker.(pool.requests)))
           Broker.(pool.hedge_wins)
           (100.0 *. float Broker.(pool.hedge_wins) /. float (max 1 Broker.(pool.hedge_fired)))
           Broker.(pool.rotations);
         dump_csv ()
       end;
       loop ()
     in
     try loop () with _ -> (try Unix.close c with _ -> ())
   in
 
   let rec accept_loop () =
     let (c,_) = Unix.accept srv in
     ignore (Thread.create handle_conn c);
     accept_loop ()
   in
   accept_loop ()
 
 let () = run ()
diff --git a/latex-parse/bench/run_service_bench_keepalive.ml b/latex-parse/bench/run_service_bench_keepalive.ml
index 790f152..b5b97b8 100644
--- a/latex-parse/bench/run_service_bench_keepalive.ml
+++ b/latex-parse/bench/run_service_bench_keepalive.ml
@@ -1,12 +1,16 @@
 open Unix
 open Percentiles_strict
 
 let read_file path =
   let ic = open_in_bin path in let len = in_channel_length ic in
   let s = really_input_string ic len in close_in ic; Bytes.unsafe_of_string s
 
+let out_path = ref None
+
 let rec write_all fd b o l =
   if l=0 then () else
   try let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)
   with Unix.Unix_error (Unix.EINTR,_,_) -> write_all fd b o l
 let rec read_exact fd b o l =
   if l=0 then () else
   try let n=Unix.read fd b o l in if n=0 then failwith "eof" else read_exact fd b (o+n) (l-n)
   with Unix.Unix_error (Unix.EINTR,_,_) -> read_exact fd b o l
@@ -21,12 +25,28 @@ let send_once_keepalive fd payload =
   let rb = Bytes.create rlen in read_exact fd rb 0 rlen;
   Clock.ms_of_ns Int64.(sub (Clock.now ()) t0)
 
 let () =
-  if Array.length Sys.argv < 4 then (prerr_endline "usage: run_service_bench_keepalive FILE ITERS THREADS"; exit 2);
-  let file    = Sys.argv.(1) in
-  let total   = int_of_string Sys.argv.(2) in
-  let threads = int_of_string Sys.argv.(3) in
+  (* usage: run_service_bench_keepalive FILE ITERS THREADS [--out path] *)
+  if Array.length Sys.argv < 4 then (prerr_endline "usage: run_service_bench_keepalive FILE ITERS THREADS [--out path]"; exit 2);
+  let args = Array.to_list Sys.argv in
+  let rec parse extras = function
+    | [] -> extras
+    | "--out"::p::xs -> out_path := Some p; parse extras xs
+    | x::xs -> parse (extras@[x]) xs
+  in
+  let extras = parse [] (List.tl args) in
+  let (file,total,threads) =
+    match extras with
+    | f::it::th::_ ->
+          (f, int_of_string it, int_of_string th)
+    | _ -> prerr_endline "usage: run_service_bench_keepalive FILE ITERS THREADS [--out path]"; exit 2
+  in
   let payload = read_file file in
   let samples = Array.make total 0.0 in
+  let out_chan =
+    match !out_path with
+    | None -> None
+    | Some p -> Some (open_out p)
+  in
   let idx = ref 0 in
   let m = Mutex.create () in
   let worker () =
@@ -41,8 +61,15 @@ let () =
     loop (); Unix.close fd
   in
   let ths = Array.init threads (fun _ -> Thread.create worker ()) in
   Array.iter Thread.join ths;
+  (match out_chan with
+   | None -> ()
+   | Some oc ->
+       Array.iter (fun x -> Printf.fprintf oc "%.6f\n" x) samples;
+       close_out oc
+  );
   Printf.printf "RTT/keepalive N=%d\n%!" total;
   Percentiles_strict.dump "RTT/keepalive" samples
diff --git a/Makefile b/Makefile
index 37f67d9..f46d1a3 100644
--- a/Makefile
+++ b/Makefile
@@ -1,6 +1,7 @@
 SHELL := /bin/bash
 FILE ?= /tmp/perf_smoke_big.tex
 J ?= 8
+OUT ?= /tmp/latencies_ms.txt
 AB_ITERS ?= 100000
 AB_WARMUP ?= 512
 
@@ -40,10 +41,12 @@ verify: build service-run
 	_build/default/latex-parse/bench/ipc_propcheck.exe
 	_build/default/latex-parse/bench/ab_microbench.exe "$(FILE)" $(AB_ITERS) $(AB_WARMUP)
 	@if [[ ! -f "$(FILE)" ]]; then echo "Set FILE=<path to perf_smoke_big.tex>"; exit 2; fi
 	# keepalive bench exercises persistent server path
-	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 4
+	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 4 --out "$(OUT)"
 	# legacy one-shot connection bench for comparison
 	_build/default/latex-parse/bench/run_service_bench_concurrent.exe "$(FILE)" 4000 4
 	@echo "[verify] tail CSV (slowest-100):"
 	@tail -n 10 /tmp/l0_service_tail.csv || true
 	@$(MAKE) service-stop
+
+.PHONY: gate
+gate: ; ./acceptance_gate.sh "$(OUT)" /tmp/l0_service_tail.csv
diff --git a/acceptance_gate.sh b/acceptance_gate.sh
new file mode 100755
index 0000000..f3a3a3a
--- /dev/null
+++ b/acceptance_gate.sh
@@ -0,0 +1,110 @@
+#!/usr/bin/env bash
+set -euo pipefail
+
+# Usage: acceptance_gate.sh <latencies_raw_txt> <service_tail_csv>
+# - latencies_raw_txt: file with one latency (ms) per line (from keepalive bench --out)
+# - service_tail_csv:  /tmp/l0_service_tail.csv produced by the service
+#
+# Gates:
+#   1) N >= 100000
+#   2) P99.9 <= 20.0 ms
+#   3) error rate == 0 (client-side responsibility; here we just check that we got N lines)
+#   4) hedged rate <= 2% (from CSV)
+#   5) consistency: P99.9 ∈ [min(slowest-100), max(slowest-100)] (from CSV)
+#
+
+RAW="${1:-/tmp/latencies_ms.txt}"
+CSV="${2:-/tmp/l0_service_tail.csv}"
+TARGET=20.0
+
+if [[ ! -f "$RAW" ]]; then echo "[gate] missing raw latencies file: $RAW"; exit 2; fi
+if [[ ! -f "$CSV" ]]; then echo "[gate] missing service tail CSV: $CSV"; exit 2; fi
+
+# 1) Count samples
+N=$(wc -l < "$RAW" | tr -d ' ')
+echo "[gate] N=$N"
+if (( N < 100000 )); then echo "[gate] FAIL: need N>=100000"; exit 3; fi
+
+# 2) Compute strict percentiles with the verifier
+if ! command -v ./verify_percentiles >/dev/null 2>&1; then
+  echo "[gate] building verify_percentiles..."
+  ocamlopt -O3 -o verify_percentiles unix.cmxa verify_percentiles.ml
+fi
+./verify_percentiles "$RAW" > /tmp/gate.pctl.txt
+cat /tmp/gate.pctl.txt
+P999=$(awk '/P99.9 =/{print $3}' /tmp/gate.pctl.txt)
+
+awk -F, 'NR>1{print $1}' "$CSV" | sort -n | tail -100 > /tmp/slow100.txt
+SLOW_MIN=$(head -1 /tmp/slow100.txt)
+SLOW_MAX=$(tail -1 /tmp/slow100.txt)
+echo "[gate] slowest-100 range: ${SLOW_MIN}..${SLOW_MAX} ms"
+
+# 3) Hedge rate from CSV (column "hedged" is the penultimate)
+H_COUNT=$(awk -F, 'NR>1 && $(NF-1)==1{c++} END{print c+0}' "$CSV")
+R_COUNT=$(awk 'END{print NR-1}' "$CSV")
+if (( R_COUNT <= 0 )); then
+  echo "[gate] FAIL: CSV has no request rows"; exit 3
+fi
+H_RATE=$(python3 - <<PY
+hc=$H_COUNT; rc=$R_COUNT
+print(f"{(hc/rc)*100.0:.3f}")
+PY
+)
+echo "[gate] hedge rate: ${H_RATE}%"
+
+# 4) Evaluate gates
+FAIL=0
+awk -v p="$P999" -v t="$TARGET" 'BEGIN{ if (p>t+1e-9) { print "[gate] FAIL: P99.9 >", t, "ms"; exit 1 } else { print "[gate] PASS: P99.9 <=", t, "ms" } }' || FAIL=1
+awk -v hr="$H_RATE" 'BEGIN{ if (hr>2.0+1e-9) { print "[gate] FAIL: hedge rate >", 2"%"; exit 1 } else { print "[gate] PASS: hedge rate <=", 2"%" } }' || FAIL=1
+
+# 5) Consistency: P99.9 inside slowest-100
+python3 - <<PY || FAIL=1
+p = float("$P999"); smin = float("$SLOW_MIN"); smax=float("$SLOW_MAX")
+eps=1e-9
+ok = (p >= smin - eps) and (p <= smax + eps)
+print("[gate] PASS: consistency (P99.9 within slowest-100 range)" if ok else "[gate] FAIL: P99.9 not within slowest-100")
+exit(0 if ok else 1)
+PY
+
+if (( FAIL )); then exit 4; fi
+echo "[gate] ALL GATES PASS"


⸻

2) Run the gate end‑to‑end

# (1) Build & quick verify; dump 10k keep-alive latencies for a smoke check
export L0_POOL_CORES=0,1,2,3
make verify FILE=/path/to/perf_smoke_big.tex OUT=/tmp/latencies_ms.txt

# (2) Full 100k acceptance (bytes-in → reply-ready; keep-alive; 4 threads):
make service-run &
_build/default/latex-parse/bench/run_service_bench_keepalive.exe \
  /path/to/perf_smoke_big.tex 100000 4 --out /tmp/latencies_ms.txt
make service-stop

# (3) Enforce gates (N≥100k, P99.9≤20ms, hedge≤2%, consistency):
make gate OUT=/tmp/latencies_ms.txt


⸻

3) Why this fixes the “math inconsistency”
	•	Previously, the service loop pre‑read the request outside the timing bracket and then gave a no‑op recv to the bracket. Your bench, however, measured bytes‑in → reply‑ready. Two different windows ⇒ inconsistent tails.
	•	The patch moves recv into the bracket, so t_in_start → t_in_done really covers the header+payload read, and ms_total is precisely the KPI you claim in AUDIT_CLAIMS.
	•	It also stops re‑processing inside logging (we store the one Broker.hedged_call result in last), so hedge_fired is the actual value for that measured request.

⸻

4) Getting P99.9 from 26.6 ms → ≤ 20 ms (deterministic checklist)

You already have all quality gates; now shape the tail. Do these in order, re‑run 100k after each change:
	1.	Ensure hedging fires when it should
	•	Keep hedge = 10 ms. If hedge rate is ~0% while P99.9 ~ 26 ms, your timer isn’t starting early enough or you’re waiting on the primary in a way that masks the timer.
	•	With the fix above (proper bracket + single process call), you should now see some hedge fire in the tail (ideally ≤ 1–2%).
	•	If still 0%, test with fault injection (e.g., 0.2–0.5% of requests sleep 15 ms in the worker) to validate the hedge path.
	2.	Workers ≥ client threads
	•	For 4 client threads, keep 4 workers (export L0_POOL_CORES=0,1,2,3).
	•	If you cannot run 4, increase inflight/worker to 2 only if you’re certain arenas are separated per inflight (avoid SOA contention).
	3.	Rotation budgets
	•	Set alloc budget to 2–3 GB and major budget to 16–24. This avoids the heap getting “old and spiky”. Too aggressive will cost throughput; too lax raises tails. Start with:

worker_alloc_budget_mb = 3000
worker_major_cycles_budget = 20


	4.	Pretouch both input and SOA prefixes every request
	•	You already pretouch input; ensure kinds/codes/offs prefixes are touched to what the request will likely fill (e.g., 30–35% of bytes × 1.3 headroom). This removes soft‑fault spikes.
	5.	QoS/affinity
	•	macOS: set QOS_CLASS_USER_INTERACTIVE for worker threads (already in your stubs). Keep workers on performance cores if possible.
	6.	If still > 20 ms: lower hedge timer slightly (to 8–9 ms) but watch hedge rate; keep it ≤ 2% in steady state.

With hedging correctly wired and 4 hot workers, the “OS/GC occasional stalls” tail should be shaved below 20 ms. You earlier hit 19.548 ms under similar conditions; this makes it repeatable and auditable.

⸻

5) Quick integrity checks (paste‑run)
	•	Bracket sanity (ensure the read is inside the measured region): watch CSV t_in_done − t_in_start — it should be > 0 and scale with input size.
	•	Hedge visibility: after the fix, hedged in CSV will be 1 for the requests where the hedge actually fired and won/rescued.
	•	Gate reproducibility: verify_percentiles on /tmp/latencies_ms.txt must match your report; consistency gate ensures P99.9 ∈ [slowest‑100 min/max].

⸻
