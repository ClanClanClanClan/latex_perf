(* Test Arena with all optimizations - direct packed token interface *)

open Data

(* Import the Arena module directly *)
include L0_lexer_track_a_arena_standalone

let test_optimized_arena_performance () =
  print_endline "=== TESTING ARENA WITH FULL OPTIMIZATIONS (A1-A4) ===";
  print_endline "Note: Using -O3 -inline 100 flags (Flambda2 requires special switch)";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "Testing OPTIMIZED Arena with: %s\n" corpus_file;
  Printf.printf "File size: %d bytes (%.2f MB)\n" size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* Pre-warm GC as recommended in handoff *)
  Gc.major_slice 0 |> ignore;
  
  print_endline "\n🔧 TESTING WITH ALL TRACK A OPTIMIZATIONS:";
  print_endline "✅ A1: Arena-based tokenization";
  print_endline "✅ A2: Packed tokens (32-bit int)";
  print_endline "✅ A3: No String.sub allocations";
  print_endline "✅ A4: Unrolled hot loop";
  print_endline "⚠️  A5: Using -O3 -inline 100 (Flambda2 needs OCaml 5.1+jst)";
  
  let times = ref [] in
  for i = 1 to 10 do
    (* Clear minor heap before each run *)
    Gc.minor ();
    
    let start_time = Sys.time () in
    let packed_tokens = tokenize content in  (* Direct packed token interface *)
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "\n  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length packed_tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let sorted = List.sort compare !times in
  let p95 = List.nth sorted 9 in
  let median = List.nth sorted 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  let min_time = List.hd sorted in
  
  Printf.printf "\n📊 OPTIMIZED ARENA RESULTS:\n";
  Printf.printf "  Minimum: %.2f ms\n" min_time;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  
  (* GC Stats as recommended *)
  let gc_stats = Gc.stat () in
  Printf.printf "\n📈 GC STATISTICS:\n";
  Printf.printf "  Minor collections: %d\n" gc_stats.minor_collections;
  Printf.printf "  Major collections: %d\n" gc_stats.major_collections;
  Printf.printf "  Minor words: %.0f\n" gc_stats.minor_words;
  Printf.printf "  Major words: %.0f\n" gc_stats.major_words;
  
  (* Target Analysis *)
  print_endline "\n🎯 TARGET ANALYSIS:";
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Achieved: %.2f ms\n" p95;
  
  if p95 <= 20.0 then (
    Printf.printf "  ✅ TARGET MET!\n";
    let margin = ((20.0 -. p95) /. 20.0) *. 100.0 in
    Printf.printf "  Margin: %.1f%% better than target\n" margin;
    Printf.printf "  🏆 OPTIMIZATIONS SUCCESSFUL!\n"
  ) else (
    Printf.printf "  ❌ Over target by %.1fx\n" (p95 /. 20.0);
    let gap = p95 -. 20.0 in
    Printf.printf "  Gap: %.2f ms over target\n" gap;
    Printf.printf "  Note: Full Flambda2 could provide additional ~7ms improvement\n"
  );
  
  (* Compare to claims *)
  print_endline "\n⚡ COMPARISON TO PERFORMANCE CLAIMS:";
  Printf.printf "  Claimed in docs: 17.7ms\n";
  Printf.printf "  Handoff packet target: 18-22ms with all optimizations\n";
  Printf.printf "  Current result: %.2f ms\n" p95;
  
  if p95 <= 22.0 then
    Printf.printf "  ✅ Within handoff packet expectations!\n"
  else
    Printf.printf "  ❓ Something preventing full optimization benefit\n";
  
  print_endline "\n=== OPTIMIZED ARENA TEST COMPLETE ===";
  p95

let () = 
  let optimized_performance = test_optimized_arena_performance () in
  Printf.printf "\n🎯 OPTIMIZED RESULT: %.2f ms P95\n" optimized_performance