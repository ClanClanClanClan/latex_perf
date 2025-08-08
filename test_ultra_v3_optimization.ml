(* Test Ultra V3 L0 Optimization vs Original Arena *)

let () =
  print_endline "=== L0 ULTRA-OPTIMIZATION V3 TEST ===\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "File: %d bytes (%.2f MB)\n\n" 
    size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* Test 1: Original Arena Implementation *)
  print_endline "🔄 TESTING ORIGINAL ARENA (baseline):";
  let original_times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let tokens_orig = L0_lexer_track_a_arena.tokenize content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    original_times := elapsed_ms :: !original_times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length tokens_orig)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let orig_sorted = List.sort compare !original_times in
  let orig_p95 = List.nth orig_sorted 9 in
  let orig_median = List.nth orig_sorted 5 in
  let orig_avg = (List.fold_left (+.) 0.0 !original_times) /. 10.0 in
  
  Printf.printf "\n📊 ORIGINAL ARENA RESULTS:\n";
  Printf.printf "  Median: %.2f ms\n" orig_median;
  Printf.printf "  Average: %.2f ms\n" orig_avg;
  Printf.printf "  P95: %.2f ms\n\n" orig_p95;
  
  (* Test 2: Ultra-Optimized V3 *)
  print_endline "🚀 TESTING ULTRA-OPTIMIZED V3:";
  let ultra_times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let tokens_ultra = L0_lexer_track_a_ultra_v3.tokenize content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    ultra_times := elapsed_ms :: !ultra_times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length tokens_ultra)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let ultra_sorted = List.sort compare !ultra_times in
  let ultra_p95 = List.nth ultra_sorted 9 in
  let ultra_median = List.nth ultra_sorted 5 in
  let ultra_avg = (List.fold_left (+.) 0.0 !ultra_times) /. 10.0 in
  
  Printf.printf "\n📊 ULTRA-OPTIMIZED V3 RESULTS:\n";
  Printf.printf "  Median: %.2f ms\n" ultra_median;
  Printf.printf "  Average: %.2f ms\n" ultra_avg;
  Printf.printf "  P95: %.2f ms\n\n" ultra_p95;
  
  (* Performance Analysis *)
  print_endline "⚡ PERFORMANCE ANALYSIS:";
  let speedup = orig_p95 /. ultra_p95 in
  let improvement_pct = (orig_p95 -. ultra_p95) /. orig_p95 *. 100.0 in
  
  Printf.printf "  Speedup: %.2fx faster\n" speedup;
  Printf.printf "  Improvement: %.1f%% reduction in time\n" improvement_pct;
  Printf.printf "  Original P95: %.2f ms\n" orig_p95;
  Printf.printf "  Optimized P95: %.2f ms\n" ultra_p95;
  Printf.printf "  Time saved: %.2f ms\n\n" (orig_p95 -. ultra_p95);
  
  (* Target Analysis *)
  print_endline "🎯 TARGET ANALYSIS:";
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Original: %.2f ms (%.1fx over target)\n" orig_p95 (orig_p95 /. 20.0);
  Printf.printf "  Optimized: %.2f ms" ultra_p95;
  
  if ultra_p95 <= 20.0 then begin
    Printf.printf " (✅ TARGET MET!)\n";
    Printf.printf "  Achievement: %.1f%% better than target\n" ((20.0 -. ultra_p95) /. 20.0 *. 100.0);
    Printf.printf "  🏆 L0 OPTIMIZATION SUCCESS!\n\n"
  end else begin
    Printf.printf " (❌ %.1fx over target)\n" (ultra_p95 /. 20.0);
    let remaining_gap = ultra_p95 -. 20.0 in
    let remaining_pct = remaining_gap /. ultra_p95 *. 100.0 in
    Printf.printf "  Remaining gap: %.2f ms (%.1f%% more optimization needed)\n\n" remaining_gap remaining_pct
  end;
  
  (* Correctness verification *)
  print_endline "✅ CORRECTNESS VERIFICATION:";
  let test_input = "\\[E = mc^2\\] and \\textbf{bold}" in
  Printf.printf "Input: %s\n" test_input;
  
  let orig_tokens = L0_lexer_track_a_arena.tokenize test_input in
  let ultra_tokens = L0_lexer_track_a_ultra_v3.tokenize test_input in
  
  Printf.printf "Original tokens: %d\n" (Array.length orig_tokens);
  Printf.printf "Ultra tokens: %d\n" (Array.length ultra_tokens);
  
  let tokens_match = Array.length orig_tokens = Array.length ultra_tokens &&
    Array.for_all2 Int32.equal orig_tokens ultra_tokens in
  
  if tokens_match then
    Printf.printf "✅ Token output matches perfectly!\n"
  else
    Printf.printf "❌ Token output differs - optimization bug!\n";
  
  print_endline "\n=== ULTRA V3 OPTIMIZATION TEST COMPLETE ==="