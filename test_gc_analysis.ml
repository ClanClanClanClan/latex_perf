(* Test GC behavior to confirm expert analysis *)

let () =
  print_endline "=== GC ANALYSIS TEST ===\n";
  
  (* Load benchmark file *)
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "File size: %d bytes\n" size;
  
  (* Get initial GC stats *)
  let initial_stats = Gc.stat () in
  Printf.printf "Initial state:\n";
  Printf.printf "  Minor words: %f\n" initial_stats.minor_words;
  Printf.printf "  Major words: %f\n" initial_stats.major_words;
  Printf.printf "  Major collections: %d\n" initial_stats.major_collections;
  
  print_endline "\nRunning tokenization...";
  
  (* Run tokenization *)
  let start_time = Sys.time () in
  let tokens = L0_lexer_track_a_arena.tokenize content in
  let end_time = Sys.time () in
  
  (* Get final GC stats *)
  let final_stats = Gc.stat () in
  Printf.printf "\nAfter tokenization:\n";
  Printf.printf "  Time: %.2f ms\n" ((end_time -. start_time) *. 1000.0);
  Printf.printf "  Tokens: %d\n" (List.length tokens);
  Printf.printf "  Minor words: %f (delta: %f)\n" 
    final_stats.minor_words (final_stats.minor_words -. initial_stats.minor_words);
  Printf.printf "  Major words: %f (delta: %f)\n"
    final_stats.major_words (final_stats.major_words -. initial_stats.major_words);
  Printf.printf "  Major collections: %d (delta: %d)\n"
    final_stats.major_collections (final_stats.major_collections - initial_stats.major_collections);
  Printf.printf "  Promotions: %f\n" (final_stats.promoted_words -. initial_stats.promoted_words);
  
  (* Calculate allocation per token *)
  let words_per_token = (final_stats.major_words -. initial_stats.major_words) /. (float_of_int (List.length tokens)) in
  Printf.printf "  Words per token: %.2f\n" words_per_token;
  
  (* Check if this matches expert prediction *)
  let expected_tokens = List.length tokens in
  let file_size_mb = float_of_int size /. 1024.0 /. 1024.0 in
  Printf.printf "\n=== EXPERT ANALYSIS CHECK ===\n";
  Printf.printf "Expert predicted: 'GC dominates for >1MB files'\n";
  Printf.printf "File size: %.2f MB\n" file_size_mb;
  Printf.printf "Tokens: %d (expected ~1M for 1MB)\n" expected_tokens;
  Printf.printf "Major collections during run: %d\n" (final_stats.major_collections - initial_stats.major_collections);
  
  if (final_stats.major_collections - initial_stats.major_collections) > 3 then
    print_endline "✅ CONFIRMED: Multiple major GC cycles during tokenization"
  else
    print_endline "❌ Expected more GC pressure";
    
  (* Test raw tokenizer for comparison *)
  print_endline "\n=== RAW TOKENIZER COMPARISON ===";
  let initial_stats2 = Gc.stat () in
  let start_time2 = Sys.time () in
  let packed_tokens = L0_lexer_track_a_arena.tokenize_raw content in
  let end_time2 = Sys.time () in
  let final_stats2 = Gc.stat () in
  
  Printf.printf "Raw tokenizer:\n";
  Printf.printf "  Time: %.2f ms\n" ((end_time2 -. start_time2) *. 1000.0);
  Printf.printf "  Packed tokens: %d\n" (Array.length packed_tokens);
  Printf.printf "  Major words delta: %f\n" (final_stats2.major_words -. initial_stats2.major_words);
  Printf.printf "  Major collections: %d\n" (final_stats2.major_collections - initial_stats2.major_collections);
  
  let raw_ratio = (final_stats.major_words -. initial_stats.major_words) /. (final_stats2.major_words -. initial_stats2.major_words) in
  Printf.printf "\nConversion overhead factor: %.1fx more allocations\n" raw_ratio