(* Test the REAL Arena Implementation - Not Standalone Garbage *)

let test_real_arena_performance () =
  print_endline "=== TESTING REAL ARENA IMPLEMENTATION (NOT STANDALONE) ===";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "Testing REAL Arena with: %s\n" corpus_file;
  Printf.printf "File size: %d bytes (%.2f MB)\n" size (float_of_int size /. 1024.0 /. 1024.0);
  
  print_endline "\n🔧 TESTING REAL INTEGRATED ARENA:";
  
  let times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let tokens = L0_lexer_track_a_arena.tokenize content in
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
  
  Printf.printf "\n📊 REAL ARENA RESULTS:\n";
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
    Printf.printf "  🏆 REAL ARENA SUCCESS!\n"
  ) else (
    Printf.printf "  ❌ Over target by %.1fx\n" (p95 /. 20.0);
    let gap = p95 -. 20.0 in
    Printf.printf "  Gap: %.2f ms over target\n" gap
  );
  
  (* Compare to false standalone numbers *)
  let false_standalone = 77.85 in
  let real_vs_false = false_standalone /. p95 in
  
  print_endline "\n⚡ REAL vs STANDALONE COMPARISON:";
  Printf.printf "  False standalone: %.2f ms\n" false_standalone;
  Printf.printf "  Real Arena: %.2f ms\n" p95;
  Printf.printf "  Real Arena is %.2fx FASTER than standalone\n" real_vs_false;
  Printf.printf "  Difference: %.2f ms improvement\n" (false_standalone -. p95);
  
  print_endline "\n=== REAL ARENA TEST COMPLETE ===";
  p95

let () = 
  let real_performance = test_real_arena_performance () in
  Printf.printf "\n🎯 REAL ARENA RESULT: %.2f ms P95\n" real_performance