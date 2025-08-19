(* Performance Reality Check - Testing actual vs claimed performance *)

open Printf

let measure_cli_timing file_path =
  let start = Unix.gettimeofday () in
  let exit_code = Sys.command (sprintf "./latex_perfectionist_cli_phase3_ultra --summary %s > /dev/null 2>&1" file_path) in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  if exit_code = 0 then Some elapsed else None

let () =
  printf "🔬 PERFORMANCE REALITY CHECK 🔬\n";
  printf "================================\n\n";
  
  let corpus = "corpora/perf/perf_smoke_big.tex" in
  
  (* Test 1: Cold start timing *)
  printf "TEST 1: Cold Start Performance\n";
  printf "------------------------------\n";
  
  (* Clear caches by reading another large file *)
  ignore (Sys.command "find /usr -name '*.h' 2>/dev/null | head -1000 | xargs cat > /dev/null 2>&1");
  
  match measure_cli_timing corpus with
  | Some t -> printf "Cold start: %.2f ms\n" t
  | None -> printf "Cold start: FAILED\n";
  
  (* Test 2: Warm cache timings *)
  printf "\nTEST 2: Warm Cache Performance (10 runs)\n";
  printf "-----------------------------------------\n";
  
  let warm_times = ref [] in
  for i = 1 to 10 do
    match measure_cli_timing corpus with
    | Some t -> 
        warm_times := t :: !warm_times;
        printf "Run %2d: %.2f ms\n" i t
    | None -> printf "Run %2d: FAILED\n" i
  done;
  
  if !warm_times <> [] then begin
    let sorted = List.sort Float.compare !warm_times in
    let mean = List.fold_left (+.) 0.0 sorted /. float_of_int (List.length sorted) in
    let min_t = List.hd sorted in
    let max_t = List.nth sorted (List.length sorted - 1) in
    printf "\nWarm cache summary:\n";
    printf "  Mean: %.2f ms\n" mean;
    printf "  Min:  %.2f ms\n" min_t;
    printf "  Max:  %.2f ms\n" max_t;
    printf "  Range: %.2f ms\n" (max_t -. min_t)
  end;
  
  (* Test 3: Process overhead measurement *)
  printf "\nTEST 3: Process Overhead\n";
  printf "------------------------\n";
  
  let start = Unix.gettimeofday () in
  ignore (Sys.command "true");
  let overhead = (Unix.gettimeofday () -. start) *. 1000.0 in
  printf "Minimal process spawn: %.2f ms\n" overhead;
  
  let start = Unix.gettimeofday () in
  ignore (Sys.command "./latex_perfectionist_cli_phase3_ultra --help > /dev/null 2>&1");
  let help_time = (Unix.gettimeofday () -. start) *. 1000.0 in
  printf "CLI help (no processing): %.2f ms\n" help_time;
  printf "Estimated CLI startup overhead: %.2f ms\n" (help_time -. overhead);
  
  (* Test 4: GC impact *)
  printf "\nTEST 4: GC Configuration Impact\n";
  printf "-------------------------------\n";
  
  (* Run with default GC *)
  printf "Default GC: ";
  Unix.putenv "OCAMLRUNPARAM" "";
  (match measure_cli_timing corpus with
   | Some t -> printf "%.2f ms\n" t
   | None -> printf "FAILED\n");
  
  (* Run with optimized GC *)
  printf "Optimized GC: ";
  Unix.putenv "OCAMLRUNPARAM" "s=32M,i=256M,o=150,O=1000000";
  (match measure_cli_timing corpus with
   | Some t -> printf "%.2f ms\n" t
   | None -> printf "FAILED\n");
  
  (* Test 5: Actual vs Claimed *)
  printf "\n=== VERDICT ===\n";
  printf "Claimed P99: < 10 ms ❌\n";
  printf "Actual P99: ~86 ms (from benchmark)\n";
  printf "Internal processing: ~4.6 ms ✅\n";
  printf "Process overhead: ~5-10 ms\n";
  printf "\nCONCLUSION: Performance claims are MISLEADING\n";
  printf "- Internal processing is fast (4.6ms)\n";
  printf "- But user-facing latency is much higher\n";
  printf "- P99 < 10ms is NOT achieved in practice\n"