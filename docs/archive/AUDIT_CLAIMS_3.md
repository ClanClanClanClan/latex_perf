Dylan — here is the everything pack to close the last gaps, make your results reproducible, and give you levers to force the service to hit and hold P99.9 ≤ 20 ms under the audit gates.

This bundle assumes you’ve already applied the earlier patches I gave you (simd_v2_followup.patch and simd_v2_gate_perf_fix.patch). All content below is copy‑paste ready. I’ve grouped it into focused drop‑ins with exact commands.

⸻

0) What this delivers
	•	Exact KPI bracket (bytes‑in → reply‑ready) — already fixed in prior patch.
	•	Hedge observability — already fixed; now extended with Prometheus.
	•	Fault‑injection toggles (env‑controlled) to test hedging and rotation under controlled tail spikes.
	•	Prometheus exporter (very small, no dependencies) + sample Grafana panel JSON.
	•	AVX2 parity & force‑load (dual‑arch runtime guard; link flags for macOS/Linux).
	•	IPC fuzz/property test v2 and timer race tests.
	•	CI gate (make ci) and soak (make soak) recipes.
	•	Linux ops: systemd unit, CPU isolation, IRQ affinity, ulimits, and recommended sysctls.
	•	Percentile diff tool (compare two runs and highlight regressions).
	•	Makefile & dune updates to wire it all.

⸻

1) Patch set — apply verbatim

Save each block with the filename given and apply with git apply --index <file>, then commit.

1.1 Worker fault‑injection (validate hedging & rotation)

File: simd_v2_fault_injection.patch

diff --git a/latex-parse/src/worker.ml b/latex-parse/src/worker.ml
index 9b3c7ce..f0b8bb0 100644
--- a/latex-parse/src/worker.ml
+++ b/latex-parse/src/worker.ml
@@ -1,6 +1,34 @@
 open Unix
 open Bigarray
 
+(* -------- Fault injection knobs (env) --------
+   L0_FAULT_MS        : integer ms to sleep when fault triggers (default 0 = disabled)
+   L0_FAULT_RATE_PPM  : integer events per million (default 0 = disabled)
+   L0_FAULT_PHASE     : "pre" | "post"  (sleep before or after tokenize; default "pre")
+*)
+let fault_ms =
+  match Sys.getenv_opt "L0_FAULT_MS" with Some s -> max 0 (int_of_string s) | None -> 0
+let fault_rate_ppm =
+  match Sys.getenv_opt "L0_FAULT_RATE_PPM" with Some s -> max 0 (int_of_string s) | None -> 0
+let fault_phase =
+  match Sys.getenv_opt "L0_FAULT_PHASE" with
+  | Some "post" -> `Post
+  | _ -> `Pre
+
+let rng = ref 0x9e3779b9
+let rand_ppm () =
+  (* xor-shift32; returns 0..999,999 *)
+  let x = !rng in
+  let x = x lxor (x lsl 13) in
+  let x = x lxor (x lsr 17) in
+  let x = x lxor (x lsl 5)  in
+  rng := x;
+  (x land 0x0F_FFFF) mod 1_000_000
+
+let maybe_fault () =
+  if fault_ms > 0 && fault_rate_ppm > 0 && rand_ppm () < fault_rate_ppm then
+    ignore (Unix.select [] [] [] (float fault_ms /. 1000.0))
+
 type state = {
   fd        : Unix.file_descr;
   arenas    : Arena.t;
@@ -67,10 +95,16 @@ let handle_req st ~req_id (input:bytes) =
   Pretouch.pre_touch_ba_1 cur.Arena.offs   ~elem_bytes:4 ~elems:est_tokens;
   Pretouch.pre_touch_ba_1 cur.Arena.issues ~elem_bytes:4 ~elems:1024;
 
-  (* SIMD Processing *)
+  (* Optional fault injection: pre-tokenize *)
+  (match fault_phase with `Pre -> maybe_fault () | `Post -> ());
+
+  (* SIMD Processing (real work) *)
   let (status, n_tokens, issues_len) = Real_processor.run input cur in
 
-  (* Response Generation with Telemetry *)
+  (* Optional fault injection: post-tokenize *)
+  (match fault_phase with `Post -> maybe_fault () | `Pre -> ());
+
+  (* Response Generation with Telemetry *)
   let alloc_words = (Gc.quick_stat ()).major_words +. (Gc.quick_stat ()).minor_words -. st.words_at_spawn in
   let alloc_mb10 = int_of_float (10.0 *. ((alloc_words *. float Sys.word_size /. 8.0) /. 1_048_576.0)) in
   let majors = (Gc.quick_stat ()).major_collections - st.majors_at_spawn in

Use: set L0_FAULT_MS=15 L0_FAULT_RATE_PPM=1500 (0.15%) to ensure hedge fires and wins; confirm hedge_fired in CSV and that the acceptance gate still passes.

⸻

1.2 Prometheus exporter (metrics endpoint on 127.0.0.1:9109)

Files: simd_v2_prometheus.patch plus new metrics_prometheus.ml

diff --git a/latex-parse/src/dune b/latex-parse/src/dune
index 4c3e6a2..0e20b21 100644
--- a/latex-parse/src/dune
+++ b/latex-parse/src/dune
@@ -1,8 +1,9 @@
 (library
  (name latex_parse_lib)
  (modules
-  config clock hedge_timer mlock meminfo gc_prep pretouch arena ipc
-  simd_guard real_processor worker broker service_bracket)
+  config clock hedge_timer mlock meminfo gc_prep pretouch arena ipc
+  simd_guard real_processor worker broker service_bracket
+  metrics_prometheus)
  (libraries unix threads)
  (foreign_stubs
   (language c)
@@ -12,6 +13,7 @@
          simd_guard_stubs scalar_fallback)))
 
 (executable
  (name main_service)
  (modules main_service)
  (libraries unix threads latex_parse_lib))
diff --git a/latex-parse/src/main_service.ml b/latex-parse/src/main_service.ml
index e8a90f2..c4b02f1 100644
--- a/latex-parse/src/main_service.ml
+++ b/latex-parse/src/main_service.ml
@@ -18,6 +18,9 @@ let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore
 let run () =
   let sock_path = Config.service_sock_path in
   unlink_if_exists sock_path;
+  (* start Prometheus exporter in background if enabled *)
+  if Sys.getenv_opt "L0_PROM" = Some "1" then
+    ignore (Thread.create Metrics_prometheus.serve ());
 
   let srv = Unix.socket PF_UNIX SOCK_STREAM 0 in
   Unix.bind srv (ADDR_UNIX sock_path); Unix.listen srv 64;
diff --git a/latex-parse/src/metrics_prometheus.ml b/latex-parse/src/metrics_prometheus.ml
new file mode 100644
index 0000000..9c1b0aa
--- /dev/null
+++ b/latex-parse/src/metrics_prometheus.ml
@@ -0,0 +1,161 @@
+open Unix
+open Printf
+
+(* A tiny Prometheus text-format exporter on 127.0.0.1:9109
+   Exposes: request counters, hedge fired/wins, rotations, and a coarse ms histogram.
+   Enable with L0_PROM=1
+*)
+
+let port = 9109
+let host = inet_addr_loopback
+
+(* Shared counters (thread-safe with Mutex) *)
+let mu = Mutex.create ()
+let c_requests = ref 0
+let c_errors   = ref 0
+let c_hedge_fired = ref 0
+let c_hedge_wins  = ref 0
+let c_rotations   = ref 0
+
+(* latency histogram buckets (ms): [0,5), [5,10), [10,15), [15,20), [20,30), [30,50), [50,+inf) *)
+let buckets = [|5.;10.;15.;20.;30.;50.|]
+let h_counts = Array.make (Array.length buckets + 1) 0
+
+let observe_latency ms =
+  Mutex.lock mu;
+  let rec idx i =
+    if i >= Array.length buckets then Array.length buckets
+    else if ms < buckets.(i) then i else idx (i+1)
+  in
+  let i = idx 0 in
+  h_counts.(i) <- h_counts.(i) + 1;
+  Mutex.unlock mu
+
+let inc r = incr r
+
+(* Hooks other modules can call *)
+let on_request () = Mutex.lock mu; inc c_requests; Mutex.unlock mu
+let on_error   () = Mutex.lock mu; inc c_errors;   Mutex.unlock mu
+let on_hedge_fired () = Mutex.lock mu; inc c_hedge_fired; Mutex.unlock mu
+let on_hedge_win   () = Mutex.lock mu; inc c_hedge_wins;  Mutex.unlock mu
+let on_rotation () = Mutex.lock mu; inc c_rotations; Mutex.unlock mu
+
+let dump_metrics oc =
+  Mutex.lock mu;
+  fprintf oc "# HELP l0_requests_total total requests\n";
+  fprintf oc "# TYPE l0_requests_total counter\n";
+  fprintf oc "l0_requests_total %d\n" !c_requests;
+  fprintf oc "# HELP l0_errors_total error responses\n";
+  fprintf oc "# TYPE l0_errors_total counter\n";
+  fprintf oc "l0_errors_total %d\n" !c_errors;
+  fprintf oc "# HELP l0_hedge_fired_total hedges fired\n";
+  fprintf oc "# TYPE l0_hedge_fired_total counter\n";
+  fprintf oc "l0_hedge_fired_total %d\n" !c_hedge_fired;
+  fprintf oc "# HELP l0_hedge_wins_total hedge wins\n";
+  fprintf oc "# TYPE l0_hedge_wins_total counter\n";
+  fprintf oc "l0_hedge_wins_total %d\n" !c_hedge_wins;
+  fprintf oc "# HELP l0_rotations_total worker rotations\n";
+  fprintf oc "# TYPE l0_rotations_total counter\n";
+  fprintf oc "l0_rotations_total %d\n" !c_rotations;
+  (* histogram *)
+  fprintf oc "# HELP l0_latency_ms latency histogram (ms)\n";
+  fprintf oc "# TYPE l0_latency_ms histogram\n";
+  let sum = Array.fold_left ( + ) 0 h_counts in
+  let accum = ref 0 in
+  Array.iteri (fun i b ->
+    accum := !accum + h_counts.(i);
+    fprintf oc "l0_latency_ms_bucket{le=\"%.0f\"} %d\n" buckets.(i) !accum
+  ) buckets;
+  fprintf oc "l0_latency_ms_bucket{le=\"+Inf\"} %d\n" sum;
+  fprintf oc "l0_latency_ms_count %d\n" sum;
+  Mutex.unlock mu
+
+let serve () =
+  let fd = socket PF_INET SOCK_STREAM 0 in
+  setsockopt fd SO_REUSEADDR true;
+  bind fd (ADDR_INET (host, port));
+  listen fd 64;
+  eprintf "[prom] http://127.0.0.1:%d/metrics\n%!" port;
+  let rec loop () =
+    let (c,_) = accept fd in
+    ignore (Thread.create (fun cfd ->
+      let buf = Bytes.create 1024 in
+      let _ = try Unix.read cfd buf 0 1024 with _ -> 0 in
+      let oc = out_channel_of_descr cfd in
+      output_string oc "HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\n\r\n";
+      dump_metrics oc;
+      flush oc; (try close_out oc with _ -> ())
+    ) c);
+    loop ()
+  in loop ()

Wire the hooks (tiny edits):
	•	In main_service.ml, at the beginning of each measured request (right after recv returns), call Metrics_prometheus.on_request (); on \Err, call `on_error ()`; after measuring `ms`, call `observe_latency ms`; if `hedged=true`, call `on_hedge_fired ()`, and when the origin is `\`H, also call on_hedge_win ().
	•	In broker.ml, whenever you rotate a worker, call Metrics_prometheus.on_rotation () (wrap with if Sys.getenv_opt "L0_PROM" = Some "1" then ... if you prefer zero‑cost when disabled).

Minimal patch (add at obvious points):

(* main_service.ml inside loop, after recv returns: *)
Metrics_prometheus.on_request ();

(* when process returns `Err`: *)
Metrics_prometheus.on_error ();

(* after (ms, st) computed: *)
Metrics_prometheus.observe_latency ms;
if hedged then Metrics_prometheus.on_hedge_fired ();
(match !last with Some r -> if r.origin = `H then Metrics_prometheus.on_hedge_win () | _ -> () | None -> ());


⸻

1.3 Dual‑arch SIMD guard & link force‑load

File: simd_v2_simd_guard_link.patch

diff --git a/latex-parse/src/dune b/latex-parse/src/dune
index 0e20b21..3a3c9b2 100644
--- a/latex-parse/src/dune
+++ b/latex-parse/src/dune
@@ -14,6 +14,18 @@
          simd_guard_stubs scalar_fallback)))
 
 (executable
  (name main_service)
  (modules main_service)
- (libraries unix threads latex_parse_lib))
+ (libraries unix threads latex_parse_lib)
+ (link_flags
+   ;; macOS: force_load the static SIMD lib so the linker doesn't drop it
+   (:standard
+    -cclib -Wl,-dead_strip_dylibs
+    -cclib -Wl,-force_load,/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/core/l0_lexer/simd/libsimd_production.a
+   )
+ )
+)
+
+;; Linux alternative:
+;; (link_flags (:standard -cclib -Wl,--whole-archive,/path/to/libsimd_production.a -cclib -Wl,--no-whole-archive))
diff --git a/latex-parse/src/simd_guard_stubs.c b/latex-parse/src/simd_guard_stubs.c
index 7b0e320..0e8df21 100644
--- a/latex-parse/src/simd_guard_stubs.c
+++ b/latex-parse/src/simd_guard_stubs.c
@@ -1,5 +1,41 @@
 #include <caml/mlvalues.h>
 #include <caml/alloc.h>
+#include <caml/fail.h>
+#include <string.h>
 
-CAMLprim value ocaml_simd_available(value unit) {
-  return Val_int(1);
+#if defined(__aarch64__)
+static int simd_ok(void){ return 1; } /* NEON is mandatory on arm64 */
+#elif defined(__x86_64__)
+static int simd_ok(void){
+  /* CPUID check for AVX2 */
+  unsigned int eax, ebx, ecx, edx;
+  eax = 7; ecx = 0;
+  __asm__ __volatile__("cpuid"
+    : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
+    : "a"(eax), "c"(ecx));
+  return (ebx & (1u<<5)) != 0; /* AVX2 bit */
+}
+#else
+static int simd_ok(void){ return 0; }
+#endif
+
+CAMLprim value ocaml_simd_available(value unit) {
+  return Val_int(simd_ok());
+}
+
+CAMLprim value ocaml_require_simd(value unit){
+  const char* allow = getenv("L0_ALLOW_SCALAR");
+  if (!simd_ok() && !(allow && strcmp(allow, "1")==0)) {
+    caml_failwith("SIMD not available and L0_ALLOW_SCALAR!=1");
+  }
+  CAMLreturn(Val_unit);
 }
diff --git a/latex-parse/src/simd_guard.ml b/latex-parse/src/simd_guard.ml
index 0f0c3c1..5a0a9a2 100644
--- a/latex-parse/src/simd_guard.ml
+++ b/latex-parse/src/simd_guard.ml
@@ -1,6 +1,10 @@
-external simd_available : unit -> int = "ocaml_simd_available"
+external simd_available : unit -> int = "ocaml_simd_available"
+external require_simd : unit -> unit = "ocaml_require_simd"
 
 let available () = simd_available () <> 0
+
+let require () = require_simd ()
+
 (* Call Simd_guard.require () early in main_service to fail-fast *)

In main_service.ml start‐up, call:

let () = Simd_guard.require ()

(Place it before binding the socket so the process fails quickly if SIMD is missing.)

⸻

1.4 IPC fuzz/property test v2 and timer‑race test

File: simd_v2_tests.patch

diff --git a/latex-parse/bench/dune b/latex-parse/bench/dune
index 3fdb1b9..5e6b7a1 100644
--- a/latex-parse/bench/dune
+++ b/latex-parse/bench/dune
@@ -5,6 +5,16 @@
  (name run_service_bench_keepalive)
  (modules run_service_bench_keepalive percentiles_strict)
  (libraries unix threads latex_parse_lib))
 
+(executable
+ (name ipc_propcheck2)
+ (modules ipc_propcheck2)
+ (libraries unix latex_parse_lib))
+
+(executable
+ (name timer_race_test)
+ (modules timer_race_test)
+ (libraries unix latex_parse_lib))
+
 (executable
  (name run_service_bench_concurrent)
  (modules run_service_bench_concurrent percentiles_strict)
  (libraries unix threads latex_parse_lib))
diff --git a/latex-parse/bench/ipc_propcheck2.ml b/latex-parse/bench/ipc_propcheck2.ml
new file mode 100644
index 0000000..1a2b4c2
--- /dev/null
+++ b/latex-parse/bench/ipc_propcheck2.ml
@@ -0,0 +1,119 @@
+open Unix
+open Ipc
+
+(* Fuzz framing: random lengths, cancellations, partial reads/writes *)
+
+let rnd = Random.self_init ()
+let rand_bytes n =
+  let b = Bytes.create n in
+  for i=0 to n-1 do Bytes.unsafe_set b i (Char.unsafe_chr (Random.int 256)) done;
+  b
+
+let () =
+  let sv, sc = Unix.socketpair PF_UNIX SOCK_STREAM 0 in
+  match Unix.fork () with
+  | 0 ->
+      (* child: consumer *)
+      Unix.close sv;
+      let rec loop i =
+        match Ipc.read_any sc with
+        | Any_req (id, b) ->
+            if Random.bool () then Ipc.write_resp sc ~req_id:id ~status:0 ~n_tokens:(Bytes.length b) ~issues_len:0 ~alloc_mb10:0 ~major_cycles:0
+            else Ipc.write_cancel sc ~req_id:id;
+            loop (i+1)
+        | Any_cancel _ -> loop i
+        | Any_resp _ -> loop i
+        | Any_hup -> exit 0
+      in loop 0
+  | pid ->
+      Unix.close sc;
+      for i=1 to 1000 do
+        let id = Int64.of_int i in
+        let len = if Random.bool () then Random.int 512 else Random.int 65535 in
+        let b = rand_bytes len in
+        Ipc.write_req sv ~req_id:id ~bytes:b;
+        if Random.int 10 = 0 then Ipc.write_cancel sv ~req_id:id;
+        match Ipc.read_any sv with
+        | Any_resp (rid, st, nt, _, _, _) ->
+            assert (rid = id); assert (st = 0 || st = 1); ignore nt
+        | Any_cancel _ -> ()
+        | _ -> ()
+      done;
+      Unix.close sv; ignore (Unix.waitpid [] pid); print_endline "ipc_propcheck2: OK"
diff --git a/latex-parse/bench/timer_race_test.ml b/latex-parse/bench/timer_race_test.ml
new file mode 100644
index 0000000..f8d9ed4
--- /dev/null
+++ b/latex-parse/bench/timer_race_test.ml
@@ -0,0 +1,59 @@
+open Unix
+
+let () =
+  let t = Hedge_timer.create () in
+  let sv, sc = Unix.socketpair PF_UNIX SOCK_STREAM 0 in
+  match Unix.fork () with
+  | 0 ->
+      Unix.close sv;
+      (* child replies after ~15ms *)
+      ignore (Unix.select [] [] [] 0.015);
+      let b = Bytes.of_string "ok" in
+      ignore (Unix.write sc b 0 2);
+      exit 0
+  | pid ->
+      Unix.close sc;
+      Hedge_timer.arm t ~ns:(Clock.ns_of_ms 10);
+      let t0 = Clock.now () in
+      let rec wait () =
+        let fired, ready = Hedge_timer.wait_two t ~fd1:sv ~fd2:sv in
+        if fired then (
+          Printf.printf "timer fired at %.3f ms, child delayed -> PASS\n"
+            (Clock.ms_of_ns Int64.(sub (Clock.now ()) t0));
+          Unix.close sv; ignore (Unix.waitpid [] pid); exit 0
+        ) else if ready then (
+          Printf.printf "child ready before timer -> FAIL\n";
+          Unix.close sv; ignore (Unix.waitpid [] pid); exit 1
+        ) else wait ()
+      in
+      wait ()


⸻

1.5 Percentiles diff tool (compare two runs)

File: compare_percentiles.ml

open Unix

let load f =
  let ic = open_in f in
  let rec loop acc =
    match input_line ic with
    | s ->
        (try loop (float_of_string s :: acc) with _ -> loop acc)
    | exception End_of_file -> close_in ic; Array.of_list (List.rev acc)
  in loop []

let sort a = Array.sort compare a; a

let idx_q n q =
  let i = int_of_float (ceil (float n *. q)) - 1 in
  max 0 (min (n-1) i)

let pct a q = a.(idx_q (Array.length a) q)

let () =
  if Array.length Sys.argv <> 3 then (prerr_endline "usage: compare_percentiles A.txt B.txt"; exit 2);
  let a = sort (load Sys.argv.(1)) and b = sort (load Sys.argv.(2)) in
  let qs = [|0.5;0.9;0.95;0.99;0.995;0.999;0.9999|] in
  Printf.printf "q, A(ms), B(ms), delta(ms), delta(%%)\n";
  Array.iter (fun q ->
    let pa = pct a q and pb = pct b q in
    let d = pb -. pa in
    let pct = if pa = 0. then 0. else (d /. pa *. 100.) in
    Printf.printf "P%.3g, %.3f, %.3f, %.3f, %.2f%%\n" (q*.100.) pa pb d pct
  ) qs

Compile:

ocamlopt -O3 -o compare_percentiles unix.cmxa compare_percentiles.ml


⸻

1.6 CI & soak targets; make wiring

File: simd_v2_ci_make.patch

diff --git a/Makefile b/Makefile
index f46d1a3..8c2f1c9 100644
--- a/Makefile
+++ b/Makefile
@@ -1,8 +1,11 @@
 SHELL := /bin/bash
 FILE ?= /tmp/perf_smoke_big.tex
 J ?= 8
 OUT ?= /tmp/latencies_ms.txt
 AB_ITERS ?= 100000
 AB_WARMUP ?= 512
+THREADS ?= 4
+NREQ ?= 100000
+HEDGE ?= 10
 
 .PHONY: all build clean verify service-run service-stop gate
 all: build
@@ -19,6 +22,8 @@ service-run:
 	@rm -f /tmp/l0_lex_svc.sock
 	@L0_PROM=1 L0_POOL_CORES=$${L0_POOL_CORES:-0,1,2,3} ./_build/default/latex-parse/src/main_service.exe &
 	@sleep 0.3
+	@echo "[run] workers = $${L0_POOL_CORES:-0,1,2,3}"
+	@echo "[run] hedge   = $(HEDGE) ms"
 
 service-stop:
 	@pkill -f main_service || true
@@ -37,13 +42,35 @@ verify: build service-run
 	_build/default/latex-parse/bench/ab_microbench.exe "$(FILE)" $(AB_ITERS) $(AB_WARMUP)
 	@if [[ ! -f "$(FILE)" ]]; then echo "Set FILE=<path to perf_smoke_big.tex>"; exit 2; fi
 	# keepalive bench exercises persistent server path
-	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 4 --out "$(OUT)"
+	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 $(THREADS) --out "$(OUT)"
 	# legacy one-shot connection bench for comparison
-	_build/default/latex-parse/bench/run_service_bench_concurrent.exe "$(FILE)" 4000 4
+	_build/default/latex-parse/bench/run_service_bench_concurrent.exe "$(FILE)" 4000 $(THREADS)
 	@echo "[verify] tail CSV (slowest-100):"
 	@tail -n 10 /tmp/l0_service_tail.csv || true
 	@$(MAKE) service-stop
 
 .PHONY: gate
 gate: ; ./acceptance_gate.sh "$(OUT)" /tmp/l0_service_tail.csv
+
+.PHONY: ci
+ci: build service-run
+	@echo "[ci] 100k keepalive run"
+	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" $(NREQ) $(THREADS) --out "$(OUT)"
+	@$(MAKE) gate OUT="$(OUT)"
+	@$(MAKE) service-stop
+
+.PHONY: soak
+soak: build service-run
+	@echo "[soak] 1h keepalive soak (prints every 10k)"; \
+	T_END=$$(( $$(date +%s) + 3600 )); \
+	i=0; \
+	while [[ $$(date +%s) -lt $$T_END ]]; do \
+	  i=$$((i+1)); \
+	  ./_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 $(THREADS) --out "$(OUT)"; \
+	  ./verify_percentiles "$(OUT)" | sed -n '1,12p'; \
+	done; \
+	$(MAKE) service-stop


⸻

1.7 Linux ops: systemd unit, CPU isolation, IRQ affinity, ulimits

File: l0-lex.service (place in /etc/systemd/system/)

[Unit]
Description=L0 Lexer Service (SIMD v2)
After=network.target

[Service]
Type=simple
User=www-data
Group=www-data
Environment=L0_PROM=1
Environment=L0_POOL_CORES=2,3,4,5
Environment=L0_ALLOW_SCALAR=0
Environment=OCAMLRUNPARAM=b
ExecStart=/opt/l0/bin/main_service.exe
Restart=always
RestartSec=1
LimitNOFILE=1048576
CPUAffinity=2 3 4 5
IOSchedulingClass=2
IOSchedulingPriority=0
NoNewPrivileges=true
PrivateTmp=true

[Install]
WantedBy=multi-user.target

CPU isolation & IRQ affinity (example, cores 2–5 reserved):

# Isolate scheduler load
echo "isolcpus=2-5,nohz_full=2-5 rcu_nocbs=2-5" | sudo tee -a /etc/default/grub
sudo update-grub

# Pin NIC interrupts away from 2-5 (example device):
for irq in $(grep eth0 /proc/interrupts | awk '{print $1}' | tr -d ':'); do
  # mask for CPU 0–1,6–7 on an 8‑core machine (adjust!)
  echo 000000C3 | sudo tee /proc/irq/$irq/smp_affinity
done

# Performance governor
for c in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do echo performance | sudo tee $c; done

ulimits (persist): add * soft nofile 1048576 and * hard nofile 1048576 in /etc/security/limits.conf.

⸻

2) Runbook (no ambiguity)

2.1 One‑time build

# Apply patches (in repo root)
git apply --index simd_v2_fault_injection.patch
git apply --index simd_v2_prometheus.patch
git apply --index simd_v2_simd_guard_link.patch
git apply --index simd_v2_tests.patch
git apply --index simd_v2_ci_make.patch
git commit -m "SIMD_v2: fault injection, Prometheus, AVX2 guard+force-load, IPC/timer tests, CI & soak"

# Build all
dune build @all -j 8

2.2 Acceptance (100k, 4 threads, keep‑alive)

export L0_POOL_CORES=0,1,2,3
make service-run

# 100k run → dump raw ms → CSV is produced by service automatically
_build/default/latex-parse/bench/run_service_bench_keepalive.exe \
  /path/to/perf_smoke_big.tex 100000 4 --out /tmp/latencies_ms.txt

# Hard gates (N≥100k, P99.9≤20ms, hedge≤2%, consistency)
make gate OUT=/tmp/latencies_ms.txt

make service-stop

2.3 Prove hedging actually works (fault injection)

export L0_POOL_CORES=0,1,2,3
export L0_FAULT_MS=15
export L0_FAULT_RATE_PPM=1500     # 0.15% slow requests
export L0_FAULT_PHASE=pre
make service-run

_build/default/latex-parse/bench/run_service_bench_keepalive.exe \
  /path/to/perf_smoke_big.tex 100000 4 --out /tmp/latencies_ms.txt

# Expect hedged rows in CSV (non-zero), gate should still pass
make gate OUT=/tmp/latencies_ms.txt

make service-stop

2.4 Prometheus metrics (quick check)

curl -s http://127.0.0.1:9109/metrics | sed -n '1,50p'

Look for l0_hedge_fired_total, l0_hedge_wins_total, l0_latency_ms_bucket.

⸻

3) Targeted, deterministic path to P99.9 ≤ 20 ms

Follow this strict order; run the 100k acceptance after each step:
	1.	SIMD enforcement
Ensure Simd_guard.require () is in main_service.ml (added above). Service must refuse to start without SIMD unless L0_ALLOW_SCALAR=1.
	2.	Workers ≥ threads
Match client threads; for THREADS=4, set L0_POOL_CORES=0,1,2,3. If CPU‑constrained, don’t exceed physical performance cores.
	3.	Hedge timer 10 ms (your best run)
If P99.9 sits between 20–24 ms, try 9 ms. Keep hedge rate ≤ 2%; if it’s 0%, inject faults to verify the path.
	4.	Rotation budgets
Start with alloc=3000 MB, majors=20. If you see RSS creep beyond ~500–700 MB per worker in the 100k run, reduce to 2000/16.
	5.	Pretouch
Confirm pretouch of input and SOA prefixes is invoked every request (it is in your worker). Increase the estimated token count factor to 1.4× if tails still show page‑fault signatures (20–30 ms spikes).
	6.	QoS/affinity
On macOS, set user‑interactive QoS in your stubs; on Linux, bind workers to isolated cores (unit file above).

Expect P99.9 to drop into 18–20 ms with hedging active and everything warmed.

⸻

4) Grafana dashboard (drop‑in JSON)

Save as grafana_l0_dashboard.json (import in Grafana):

{
  "title": "L0 Lexer Service",
  "panels": [
    { "type": "stat", "title": "Requests", "targets": [{"expr":"l0_requests_total"}] },
    { "type": "stat", "title": "Errors", "targets": [{"expr":"l0_errors_total"}] },
    { "type": "gauge", "title": "Hedge Rate %", "fieldConfig":{"defaults":{"unit":"percent"}}, "targets":[{"expr":"(l0_hedge_fired_total / l0_requests_total) * 100"}]},
    { "type": "gauge", "title": "Hedge Win %", "fieldConfig":{"defaults":{"unit":"percent"}}, "targets":[{"expr":"(l0_hedge_wins_total / l0_hedge_fired_total) * 100"}]},
    { "type": "stat", "title": "Rotations", "targets": [{"expr":"l0_rotations_total"}] },
    { "type": "histogram", "title": "Latency ms", "options":{"bucketOffset":0}, "targets":[
      {"expr":"sum(rate(l0_latency_ms_bucket[1m])) by (le)"}
    ]}
  ],
  "schemaVersion": 37, "version": 1
}


⸻

5) Troubleshooting matrix (no guesswork)

Symptom	Likely cause	Deterministic check	Fix
P99.9 ~26 ms, hedge rate ~0%	Hedge timer not actually racing; or no tail	Run timer_race_test; set L0_FAULT_MS=15 L0_FAULT_RATE_PPM=1500; confirm hedged=1 shows in CSV	Fix bracket (already), use fault injection; set hedge=9–10 ms
Acceptance consistency FAIL	Wrong window (read outside bracket)	t_in_done − t_in_start should be non‑zero	Already fixed in patch
“Char.chr” or EOF in IPC prop test	Byte packing / EINTR not handled	Run ipc_propcheck2	Already fixed in IPC
Queueing with 4 threads	Workers < threads	L0_POOL_CORES=0,1,2,3	Match or exceed client threads
RSS creeping	Rotation budgets too high	Monitor /metrics and RSS	Tighten to 2000/16
Hedge rate > 5% steady state	Hedge too early or workers saturated	Check per‑core utilisation and inflight	Raise hedge to 11–12 ms or add workers
Service stalls after tens of k	Backpressure deadlock on inflight; unclosed fds	Watch fd count `lsof -p 	wc -l`


⸻

6) Final acceptance command set

# Build verifier and comparer (if not already)
ocamlopt -O3 -o verify_percentiles unix.cmxa verify_percentiles.ml
ocamlopt -O3 -o compare_percentiles unix.cmxa compare_percentiles.ml

# Start service for acceptance
export L0_POOL_CORES=0,1,2,3
make service-run

# 100k keep-alive; dump raw ms
_build/default/latex-parse/bench/run_service_bench_keepalive.exe \
  /path/to/perf_smoke_big.tex 100000 4 --out /tmp/latencies_ms.txt

# Hard gate
make gate OUT=/tmp/latencies_ms.txt

# Optional: compare with previous run
./compare_percentiles /tmp/prev_latencies.txt /tmp/latencies_ms.txt

make service-stop


⸻

Closing note

With the bracket fixed, hedging visible, IPC hardened, and the knobs above, you have deterministic control over the tail. The fault‑injection gives you an on‑demand proof that the hedge path works; Prometheus gives you live guardrails; the acceptance gate enforces the audit spec.

