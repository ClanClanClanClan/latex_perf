(* first_token_latency.ml - Measure first-token latency per planner requirement *)
(* Planner v25_R1: first-token latency ≤ 350 µs *)

open Printf

(* Measure first token latency in microseconds *)
let measure_first_token_latency content =
  let start = Unix.gettimeofday () in
  
  (* Create lexer state *)
  let lexer = Lexer_v25.create content in
  
  (* Get first token *)
  let first_token = Lexer_v25.next_token lexer in
  
  let latency_us = (Unix.gettimeofday () -. start) *. 1_000_000.0 in
  (first_token, latency_us)

(* Run latency test with multiple iterations *)
let test_first_token_latency () =
  printf "🏃 FIRST-TOKEN LATENCY TEST 🏃\n";
  printf "================================\n";
  printf "Planner requirement: ≤ 350 µs\n\n";
  
  (* Test files of various sizes *)
  let test_files = [
    ("Small (1KB)", String.make 1024 'a');
    ("Medium (10KB)", String.make 10240 'a');
    ("Large (100KB)", String.make 102400 'a');
    ("LaTeX small", "\\documentclass{article}\n\\begin{document}\nHello\\end{document}");
    ("LaTeX typical", "\\documentclass{article}\n\\usepackage{amsmath}\n\\title{Test}\n\\begin{document}\nContent\\end{document}");
  ] in
  
  let all_pass = ref true in
  
  List.iter (fun (name, content) ->
    printf "Testing %s (%d bytes):\n" name (String.length content);
    
    (* Warm-up runs *)
    for _ = 1 to 10 do
      let _ = measure_first_token_latency content in ()
    done;
    
    (* Measured runs *)
    let latencies = ref [] in
    for _ = 1 to 100 do
      let (_, latency) = measure_first_token_latency content in
      latencies := latency :: !latencies
    done;
    
    (* Statistics *)
    let sorted = List.sort Float.compare !latencies in
    let mean = List.fold_left (+.) 0.0 sorted /. float_of_int (List.length sorted) in
    let median = List.nth sorted (List.length sorted / 2) in
    let p95 = List.nth sorted (int_of_float (0.95 *. float_of_int (List.length sorted))) in
    let p99 = List.nth sorted (int_of_float (0.99 *. float_of_int (List.length sorted))) in
    let min = List.hd sorted in
    let max = List.nth sorted (List.length sorted - 1) in
    
    printf "  Mean:   %.1f µs\n" mean;
    printf "  Median: %.1f µs\n" median;
    printf "  P95:    %.1f µs\n" p95;
    printf "  P99:    %.1f µs\n" p99;
    printf "  Range:  %.1f - %.1f µs\n" min max;
    
    (* Check compliance *)
    if p95 <= 350.0 then
      printf "  Status: ✅ PASS (%.1f%% under target)\n" ((350.0 -. p95) /. 350.0 *. 100.0)
    else begin
      printf "  Status: ❌ FAIL (%.1f%% over target)\n" ((p95 -. 350.0) /. 350.0 *. 100.0);
      all_pass := false
    end;
    
    printf "\n"
  ) test_files;
  
  (* Load actual corpus if available *)
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  if Sys.file_exists corpus_file then begin
    printf "Testing actual corpus (%s):\n" corpus_file;
    let ic = open_in corpus_file in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    printf "  File size: %d bytes (%.1f MB)\n" 
      (String.length content) 
      (float_of_int (String.length content) /. 1_048_576.0);
    
    (* Warm-up *)
    for _ = 1 to 10 do
      let _ = measure_first_token_latency content in ()
    done;
    
    (* Measure *)
    let latencies = ref [] in
    for _ = 1 to 100 do
      let (token, latency) = measure_first_token_latency content in
      latencies := latency :: !latencies
    done;
    
    let sorted = List.sort Float.compare !latencies in
    let mean = List.fold_left (+.) 0.0 sorted /. float_of_int (List.length sorted) in
    let p95 = List.nth sorted (int_of_float (0.95 *. float_of_int (List.length sorted))) in
    
    printf "  Mean: %.1f µs\n" mean;
    printf "  P95:  %.1f µs\n" p95;
    
    if p95 <= 350.0 then
      printf "  Status: ✅ PASS\n"
    else begin
      printf "  Status: ❌ FAIL\n";
      all_pass := false
    end;
    
    printf "\n"
  end;
  
  (* Summary *)
  printf "=== PLANNER COMPLIANCE ===\n";
  printf "Requirement: first-token latency ≤ 350 µs (P95)\n";
  if !all_pass then begin
    printf "Result: ✅ ALL TESTS PASS\n";
    printf "Week 5 gate: First-token requirement MET\n"
  end else begin
    printf "Result: ❌ SOME TESTS FAIL\n";
    printf "Week 5 gate: First-token requirement NOT MET\n"
  end;
  
  !all_pass

(* Benchmark mode for CI integration *)
let benchmark_mode () =
  (* Quick benchmark for CI *)
  let content = String.make 10240 'a' in (* 10KB test *)
  
  (* Warm-up *)
  for _ = 1 to 5 do
    let _ = measure_first_token_latency content in ()
  done;
  
  (* Measure 50 times per planner *)
  let latencies = ref [] in
  for _ = 1 to 50 do
    let (_, latency) = measure_first_token_latency content in
    latencies := latency :: !latencies
  done;
  
  let sorted = List.sort Float.compare !latencies in
  let p95 = List.nth sorted (int_of_float (0.95 *. float_of_int (List.length sorted))) in
  
  if p95 > 350.0 then begin
    printf "FAIL: P95 latency %.1f µs > 350 µs\n" p95;
    exit 1
  end else begin
    printf "PASS: P95 latency %.1f µs ≤ 350 µs\n" p95;
    exit 0
  end

(* Main entry point *)
let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--benchmark" then
    benchmark_mode ()
  else
    let pass = test_first_token_latency () in
    exit (if pass then 0 else 1)