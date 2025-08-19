(* COMPREHENSIVE VALIDATOR BENCHMARK SUITE *)

open Printf
open Validator_types

(* Test data generation *)
let create_realistic_test_data n_tokens =
  Array.init n_tokens (fun i ->
    match i mod 100 with
    | 0 -> (12, 34)     (* Quote: 1% *)
    | 1 | 2 -> (12, 45) (* Hyphen: 2% *)
    | 3 | 4 | 5 -> (12, 46) (* Period: 3% *)
    | 6 -> (10, 9)      (* Tab: 1% *)
    | 7 -> (1, 123)     (* Left brace: 1% *)
    | 8 -> (2, 125)     (* Right brace: 1% *)
    | _ -> (11, 97)     (* Letter: 91% *)
  )

(* Create interest mask from test data *)
let build_interest_mask token_data =
  let n = Array.length token_data in
  let interest_mask = L0_integration.create_interest_mask n in
  
  Array.iteri (fun i (kind, ascii) ->
    L0_integration.write_interest_mask interest_mask i ~token_kind:kind ~ascii_code:ascii
  ) token_data;
  
  interest_mask

(* Single benchmark run *)
let benchmark_single tokens iterations =
  let n = Array.length tokens in
  let interest_mask = build_interest_mask tokens in
  
  printf "Benchmarking %d tokens with %d iterations...\n" n iterations;
  
  (* Warm up *)
  for _ = 1 to 20 do
    ignore (Single_pass_validator.validate interest_mask n)
  done;
  
  (* Measure *)
  let times = ref [] in
  let total_issues = ref 0 in
  
  for _ = 1 to iterations do
    let (issues, stats) = Single_pass_validator.validate_with_timing interest_mask n in
    times := stats.validation_time_ms :: !times;
    total_issues := issues.count
  done;
  
  (* Statistics *)
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted ((iterations * 99) / 100) in
  let p95 = List.nth sorted ((iterations * 95) / 100) in
  let p50 = List.nth sorted (iterations / 2) in
  let mean = List.fold_left (+.) 0.0 sorted /. float iterations in
  let min_time = List.hd sorted in
  let max_time = List.hd (List.rev sorted) in
  
  (* Results *)
  printf "Performance Results:\n";
  printf "  Tokens:      %d\n" n;
  printf "  Iterations:  %d\n" iterations;
  printf "  Mean:        %.3fms\n" mean;
  printf "  P50:         %.3fms\n" p50;
  printf "  P95:         %.3fms\n" p95;
  printf "  P99:         %.3fms\n" p99;
  printf "  Min:         %.3fms\n" min_time;
  printf "  Max:         %.3fms\n" max_time;
  printf "  Issues:      %d\n" !total_issues;
  printf "  Throughput:  %.1f tokens/ms\n" (float n /. mean);
  
  if p99 < 1.0 then
    printf "  ✅ SUCCESS: P99 < 1ms achieved!\n"
  else if p99 < 1.5 then
    printf "  ⚠️  CLOSE: P99 %.3fms (within 50%% of target)\n" p99
  else
    printf "  ❌ SLOW: P99 %.3fms exceeds target\n" p99;
  
  printf "\n";
  p99

(* Comprehensive benchmark suite *)
let run_comprehensive_benchmark () =
  printf "=== COMPREHENSIVE VALIDATOR BENCHMARK ===\n\n";
  
  let test_sizes = [
    (10_000, "10K tokens (small document)");
    (50_000, "50K tokens (medium document)");
    (276_000, "276K tokens (large document - 1.1MB)");
    (500_000, "500K tokens (very large document)");
  ] in
  
  let all_results = ref [] in
  
  List.iter (fun (size, description) ->
    printf "=== %s ===\n" description;
    let tokens = create_realistic_test_data size in
    let p99 = benchmark_single tokens 200 in
    all_results := (size, p99) :: !all_results;
    printf "\n"
  ) test_sizes;
  
  printf "=== SCALING ANALYSIS ===\n";
  printf "┌─────────────┬──────────┬─────────────┬─────────────┐\n";
  printf "│ Size        │ P99 Time │ Per Token   │ Scaling     │\n";
  printf "├─────────────┼──────────┼─────────────┼─────────────┤\n";
  
  let results = List.rev !all_results in
  List.iteri (fun i (size, p99) ->
    let per_token = p99 /. float size *. 1_000_000.0 in  (* nanoseconds per token *)
    let scaling = if i = 0 then "baseline" else
      let (prev_size, prev_p99) = List.nth results (i-1) in
      let expected = prev_p99 *. float size /. float prev_size in
      let ratio = p99 /. expected in
      sprintf "%.2fx" ratio
    in
    printf "│ %10dk │ %7.3fms │ %9.1fns │ %11s │\n" 
      (size / 1000) p99 per_token scaling
  ) results;
  
  printf "└─────────────┴──────────┴─────────────┴─────────────┘\n\n";
  
  (* Check if scaling is linear (good) *)
  if List.length results >= 2 then begin
    let (small_size, small_p99) = List.hd results in
    let (large_size, large_p99) = List.hd (List.rev results) in
    let actual_ratio = large_p99 /. small_p99 in
    let size_ratio = float large_size /. float small_size in
    let scaling_factor = actual_ratio /. size_ratio in
    
    printf "Scaling Analysis:\n";
    printf "  Size increase:     %.1fx\n" size_ratio;
    printf "  Time increase:     %.1fx\n" actual_ratio;
    printf "  Scaling factor:    %.2fx\n" scaling_factor;
    
    if scaling_factor < 1.2 then
      printf "  ✅ EXCELLENT: Near-linear scaling\n"
    else if scaling_factor < 1.5 then
      printf "  ⚠️  GOOD: Reasonable scaling\n"
    else
      printf "  ❌ POOR: Worse than linear scaling\n"
  end

(* Memory usage analysis *)
let analyze_memory_usage size =
  printf "=== MEMORY USAGE ANALYSIS ===\n";
  let tokens = create_realistic_test_data size in
  let interest_mask = build_interest_mask tokens in
  
  let mask_size = size in  (* 1 byte per token *)
  let issue_buffer_size = 65536 * (4 + 2) in  (* positions + codes *)
  let total_memory = mask_size + issue_buffer_size in
  
  printf "Memory allocation for %d tokens:\n" size;
  printf "  Interest mask:     %d bytes (%.2f MB)\n" mask_size (float mask_size /. 1_000_000.0);
  printf "  Issue buffer:      %d bytes (%.2f MB)\n" issue_buffer_size (float issue_buffer_size /. 1_000_000.0);
  printf "  Total allocated:   %d bytes (%.2f MB)\n" total_memory (float total_memory /. 1_000_000.0);
  printf "  Memory efficiency: %.1f bytes per token\n" (float total_memory /. float size);
  printf "\n"

(* Main benchmark entry point *)
let () =
  printf "PRODUCTION VALIDATOR BENCHMARK SUITE\n";
  printf "====================================\n\n";
  
  printf "Target: P99 < 1.0ms for 276K tokens\n";
  printf "Baseline: Previous sparse approach = 3.189ms\n\n";
  
  run_comprehensive_benchmark ();
  analyze_memory_usage 276_000;
  
  printf "Benchmark complete!\n"