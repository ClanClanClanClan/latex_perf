(* Test if earlier claimed breakthroughs were real *)

let test_simple_performance () =
  print_endline "=== INVESTIGATING EARLIER SUB-20MS CLAIMS ===";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "Investigating earlier breakthrough claims with: %s\n" corpus_file;
  Printf.printf "File size: %d bytes (%.2f MB)\n" size (float_of_int size /. 1024.0 /. 1024.0);
  
  print_endline "\n🔍 ANALYSIS OF PERFORMANCE CLAIMS:";
  
  (* Simple character counting test - baseline *)
  let times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let char_count = String.length content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "  Run %d (char count): %.2f ms (%d chars)\n" i elapsed_ms char_count
    else
      Printf.printf "  Run %d (char count): %.2f ms\n" i elapsed_ms
  done;
  
  let sorted = List.sort compare !times in
  let p95 = List.nth sorted 9 in
  let median = List.nth sorted 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  let min_time = List.hd sorted in
  
  Printf.printf "\n📊 BASELINE (CHAR COUNT ONLY) RESULTS:\n";
  Printf.printf "  Minimum: %.2f ms\n" min_time;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  
  print_endline "\n🤔 BREAKTHROUGH CLAIMS ANALYSIS:";
  Printf.printf "  Claimed breakthrough: ~9.98ms\n";
  Printf.printf "  Arena baseline: 31.40ms\n";
  Printf.printf "  Even counting chars takes: %.2f ms\n" p95;
  
  if p95 > 9.98 then (
    Printf.printf "  ❌ IMPOSSIBLE: Counting chars alone (%.2f ms) > claimed breakthrough (9.98ms)\n" p95;
    Printf.printf "  🚨 CONCLUSION: 9.98ms claim was physically impossible\n"
  ) else (
    Printf.printf "  ✅ POSSIBLE: Char counting leaves headroom for tokenization\n"
  );
  
  (* Test what 9.98ms could realistically accomplish *)
  let theoretical_ops_per_ms = float_of_int size /. 9.98 in
  Printf.printf "\n📈 THEORETICAL ANALYSIS:\n";
  Printf.printf "  File size: %d bytes\n" size;
  Printf.printf "  Claimed time: 9.98ms\n";
  Printf.printf "  Required speed: %.0f bytes/ms (%.0f MB/s)\n" 
    theoretical_ops_per_ms (theoretical_ops_per_ms /. 1024.0);
  Printf.printf "  Arena actual speed: %.0f bytes/ms (%.0f MB/s)\n"
    (float_of_int size /. 31.40) ((float_of_int size /. 31.40) /. 1024.0);
  
  print_endline "\n🎯 CONCLUSION:";
  if p95 > 9.98 then
    print_endline "  Earlier 9.98ms claims were IMPOSSIBLE - even basic file operations exceed this"
  else
    print_endline "  Need to investigate what happened to earlier optimizations";
  
  p95

let () = 
  let baseline_time = test_simple_performance () in
  Printf.printf "\n🎯 BASELINE RESULT: %.2f ms P95\n" baseline_time