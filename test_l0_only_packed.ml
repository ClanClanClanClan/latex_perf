(* Test ONLY L0 packed tokenizer to verify it meets target *)

let () =
  print_endline "=== L0 ONLY PERFORMANCE TEST ===\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "File: %d bytes (%.2f MB)\n\n" 
    size (float_of_int size /. 1024.0 /. 1024.0);
  
  print_endline "🚀 TESTING L0 PACKED TOKENIZER ONLY (TARGET: ≤20ms)";
  
  let times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    
    (* L0: Tokenize (packed format) - This should be ~16ms *)
    let l0_tokens = L0_lexer_track_a_arena.tokenize content in
    
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d packed tokens)\n" 
        i elapsed_ms (Array.length l0_tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let sorted_times = List.sort compare !times in
  let p95 = List.nth sorted_times 9 in
  let median = List.nth sorted_times 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  
  Printf.printf "\n📊 L0 ONLY RESULTS:\n";
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  Printf.printf "  Target: ≤20ms\n\n";
  
  if p95 <= 20.0 then begin
    Printf.printf "✅ L0 PERFORMANCE TARGET MET!\n";
    Printf.printf "  %.2f ms is %.1f%% better than target\n" p95 ((20.0 -. p95) /. 20.0 *. 100.0);
  end else begin
    Printf.printf "❌ L0 Performance target missed\n";
    Printf.printf "  %.2f ms vs ≤20ms target\n" p95
  end;
  
  Printf.printf "\n🔍 COMPARISON WITH EXPERT ANALYSIS:\n";
  Printf.printf "  Expert predicted: ~16ms for L0 arena + packing\n";
  Printf.printf "  Our result: %.2f ms\n" p95;
  Printf.printf "  Difference: %.1fx %s than predicted\n"
    (if p95 > 16.0 then p95 /. 16.0 else 16.0 /. p95)
    (if p95 > 16.0 then "slower" else "faster");