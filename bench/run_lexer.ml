(* L0 Lexer Benchmark Harness *)
(* LaTeX Perfectionist v25 - Performance measurement per spec *)
(* Implements Section 2: "5 warm-ups + 50 measured iterations" *)

open Printf

(* Performance measurement utilities *)
let time_function f input =
  let start = Unix.gettimeofday () in
  let result = f input in
  let stop = Unix.gettimeofday () in
  let elapsed_ms = (stop -. start) *. 1000.0 in
  (result, elapsed_ms)

let median_of_list lst =
  let sorted = List.sort Float.compare lst in
  let len = List.length sorted in
  if len mod 2 = 0 then
    let mid1 = List.nth sorted (len / 2 - 1) in
    let mid2 = List.nth sorted (len / 2) in
    (mid1 +. mid2) /. 2.0
  else
    List.nth sorted (len / 2)

let percentile_of_list lst p =
  let sorted = List.sort Float.compare lst in
  let len = List.length sorted in
  let idx = int_of_float (float_of_int len *. p /. 100.0) in
  let bounded_idx = max 0 (min (len - 1) idx) in
  List.nth sorted bounded_idx

(* Lexer function wrappers *)
let test_l0_lexer input =
  let tokens = Core.Lexer_optimized_v25.tokenize_to_list input in
  List.length tokens

(* Unused lexer variants kept for reference *)
let _test_l0_lexer_spec_exact input =
  let tokens = Core.L0_lexer_track_a_simple.tokenize input in
  List.length tokens

let test_l0_lexer_track_a_simple input =
  let tokens = Core.L0_lexer_track_a_simple.tokenize input in
  List.length tokens

let _test_l0_lexer_track_a_perfected input =
  let tokens = Core.L0_lexer_track_a_perfect.tokenize input in
  List.length tokens

let _test_l0_lexer_track_a_ultra input =
  let tokens = Core.L0_lexer_track_a_perfect.tokenize input in
  List.length tokens

let test_l0_lexer_track_a_final input =
  let tokens = Core.L0_lexer_track_a_perfect.tokenize input in
  List.length tokens

(* Benchmark a single lexer *)
let benchmark_lexer name lexer_func input =
  let file_size = String.length input in
  printf "\n=== Benchmarking %s ===\n" name;
  printf "File size: %d bytes\n" file_size;
  
  (* Warm-up runs (5 as per spec) *)
  printf "Warming up (5 runs)...\n";
  for _i = 1 to 5 do
    let (_, _) = time_function lexer_func input in
    ()
  done;
  
  (* Measured runs (50 as per spec) *)
  printf "Measuring (50 runs)...\n";
  let times = ref [] in
  let token_counts = ref [] in
  
  for i = 1 to 50 do
    let (token_count, elapsed_ms) = time_function lexer_func input in
    times := elapsed_ms :: !times;
    token_counts := token_count :: !token_counts;
    if i mod 10 = 0 then printf "  Completed %d/50 runs\n%!" i
  done;
  
  (* Calculate statistics *)
  let times_list = List.rev !times in
  let token_count = List.hd (List.rev !token_counts) in
  
  let median_ms = median_of_list times_list in
  let p95_ms = percentile_of_list times_list 95.0 in
  let p99_ms = percentile_of_list times_list 99.0 in
  let min_ms = List.fold_left min (List.hd times_list) times_list in
  let max_ms = List.fold_left max (List.hd times_list) times_list in
  
  (* Calculate throughput *)
  let mb_size = float_of_int file_size /. 1_048_576.0 in
  let throughput_mbs = mb_size /. (median_ms /. 1000.0) in
  
  (* Print results *)
  printf "\nResults for %s:\n" name;
  printf "  Tokens produced: %d\n" token_count;
  printf "  Median time: %.3f ms\n" median_ms;
  printf "  P95 time: %.3f ms\n" p95_ms;
  printf "  P99 time: %.3f ms\n" p99_ms;
  printf "  Min time: %.3f ms\n" min_ms;
  printf "  Max time: %.3f ms\n" max_ms;
  printf "  Throughput: %.1f MB/s\n" throughput_mbs;
  
  (* SLA checks per spec *)
  let sla_20ms = median_ms <= 20.0 in
  let sla_8ms = median_ms <= 8.0 in
  printf "  20ms SLA (Tier A): %s\n" (if sla_20ms then "✅ PASS" else "❌ FAIL");
  printf "  8ms SLA (Tier B): %s\n" (if sla_8ms then "✅ PASS" else "❌ FAIL");
  
  (median_ms, p95_ms, throughput_mbs, token_count)

(* Load test files *)
let load_file filename =
  try
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    Some content
  with
  | Sys_error msg -> 
    printf "Warning: Could not load %s: %s\n" filename msg;
    None

(* Main benchmark runner *)
let () =
  printf "LaTeX Perfectionist v25 - L0 Lexer Benchmark Suite\n";
  printf "====================================================\n";
  printf "Implementation: Section 2 spec (5 warmup + 50 measured)\n\n";
  
  (* Test files as per spec Section 2 *)
  let test_files = [
    ("perf_smoke_big.tex", "corpora/perf/perf_smoke_big.tex", 1_118_944);
    ("perf_math_light.tex", "corpora/perf/perf_math_light.tex", 412_000);
    ("perf_macro_dense.tex", "corpora/perf/perf_macro_dense.tex", 680_000);
    ("perf_unicode.tex", "corpora/perf/perf_unicode.tex", 515_000);
  ] in
  
  (* Lexers to test *)
  let lexers = [
    ("L0_lexer_baseline", test_l0_lexer);
    ("L0_lexer_track_a_simple", test_l0_lexer_track_a_simple);
    ("L0_lexer_track_a_final", test_l0_lexer_track_a_final);
  ] in
  
  (* Run benchmarks *)
  List.iter (fun (file_name, file_path, _expected_size) ->
    match load_file file_path with
    | Some content ->
      printf "\n" ; for _i = 1 to 50 do printf "=" done ; printf "\n";
      printf "BENCHMARKING: %s (%d bytes)\n" file_name (String.length content);
      for _i = 1 to 50 do printf "=" done ; printf "\n";
      
      let results = List.map (fun (lexer_name, lexer_func) ->
        let (median, p95, throughput, tokens) = benchmark_lexer lexer_name lexer_func content in
        (lexer_name, median, p95, throughput, tokens)
      ) lexers in
      
      (* Summary for this file *)
      printf "\nSUMMARY for %s:\n" file_name;
      printf "Lexer                Median     P95        Throughput  Tokens\n";
      printf "----------------------------------------------------------------\n";
      List.iter (fun (name, median, p95, throughput, tokens) ->
        printf "%-18s   %6.2fms   %6.2fms   %6.1f MB/s  %d\n" 
          name median p95 throughput tokens
      ) results;
      
      (* Find best performer *)
      let best_lexer = List.fold_left (fun (best_name, best_time) (name, median, _, _, _) ->
        if median < best_time then (name, median) else (best_name, best_time)
      ) ("", Float.max_float) results in
      printf "\nFastest: %s (%.2fms)\n" (fst best_lexer) (snd best_lexer);
      
    | None ->
      printf "Skipping %s (file not found)\n" file_name
  ) test_files;
  
  printf "\nBenchmark complete. Results saved to stdout.\n";
  printf "Use: dune exec bench/run_lexer.exe > benchmark_results.txt\n"