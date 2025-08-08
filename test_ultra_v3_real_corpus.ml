(* Test Ultra V3 Fixed Implementation with Real Corpus *)

let test_ultra_v3_performance () =
  print_endline "=== ULTRA V3 FIXED - REAL CORPUS PERFORMANCE TEST ===";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  (* Check if corpus exists *)
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    Printf.printf "Available files:\n";
    let files = Sys.readdir "." in
    Array.iter (fun f -> Printf.printf "  %s\n" f) files;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "Testing with: %s\n" corpus_file;
  Printf.printf "File size: %d bytes (%.2f MB)\n" size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* Test Ultra V3 Fixed *)
  print_endline "\n🚀 TESTING ULTRA V3 FIXED:";
  
  let times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let tokens = L0_lexer_track_a_ultra_v3_fixed.tokenize content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let sorted = List.sort compare !times in
  let p95 = List.nth sorted 9 in
  let median = List.nth sorted 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  let min_time = List.hd sorted in
  
  Printf.printf "\n📊 ULTRA V3 FIXED RESULTS:\n";
  Printf.printf "  Minimum: %.2f ms\n" min_time;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  
  (* Target Analysis *)
  print_endline "\n🎯 TARGET ANALYSIS:";
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Achieved: %.2f ms\n" p95;
  
  if p95 <= 20.0 then (
    Printf.printf "  ✅ TARGET MET!\n";
    let margin = ((20.0 -. p95) /. 20.0) *. 100.0 in
    Printf.printf "  Margin: %.1f%% better than target\n" margin;
    Printf.printf "  🏆 L0 OPTIMIZATION SUCCESS!\n"
  ) else (
    Printf.printf "  ❌ Over target by %.1fx\n" (p95 /. 20.0);
    let gap = p95 -. 20.0 in
    Printf.printf "  Gap: %.2f ms over target\n" gap
  );
  
  (* Compare to Arena baseline *)
  let arena_baseline = 31.96 in (* From previous honest testing *)
  let speedup = arena_baseline /. p95 in
  let improvement = ((arena_baseline -. p95) /. arena_baseline) *. 100.0 in
  
  print_endline "\n⚡ PERFORMANCE IMPROVEMENT:";
  Printf.printf "  Arena baseline: %.2f ms\n" arena_baseline;
  Printf.printf "  Ultra V3 Fixed: %.2f ms\n" p95;
  Printf.printf "  Speedup: %.2fx faster\n" speedup;
  Printf.printf "  Improvement: %.1f%% reduction\n" improvement;
  
  print_endline "\n=== REAL CORPUS TEST COMPLETE ===";
  p95

let () = 
  let final_performance = test_ultra_v3_performance () in
  Printf.printf "\n🎯 FINAL RESULT: %.2f ms P95 performance\n" final_performance