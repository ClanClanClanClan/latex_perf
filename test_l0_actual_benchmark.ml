(* Test L0 with actual benchmark file *)

let () =
  print_endline "=== L0 BENCHMARK TEST ===";
  print_endline "Using actual perf_smoke_big.tex file\n";
  
  (* Load benchmark file *)
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists benchmark_file) then begin
    Printf.printf "❌ Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "📁 Loaded: %d bytes (%.2f MB)\n\n" 
    size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* Test tokenization *)
  print_endline "⏱️  Running performance test (10 runs):";
  
  (* Warm-up *)
  let _ = L0_lexer_track_a_arena.tokenize content in
  
  (* Timed runs *)
  let times = ref [] in
  for i = 1 to 10 do
    let start = Sys.time () in
    let tokens = L0_lexer_track_a_arena.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    times := elapsed :: !times;
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed (List.length tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed
  done;
  
  (* Calculate stats *)
  let sorted_times = List.sort compare !times in
  let p95 = List.nth sorted_times 9 in (* 10th element for P95 with 10 runs *)
  let median = List.nth sorted_times 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  
  print_endline "\n📊 Results:";
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  Printf.printf "  Target: ≤20ms\n\n";
  
  if p95 <= 20.0 then begin
    Printf.printf "✅ PERFORMANCE TARGET MET!\n";
    Printf.printf "  %.2f ms is %.1f%% better than target\n" p95 ((20.0 -. p95) /. 20.0 *. 100.0)
  end else begin
    Printf.printf "❌ PERFORMANCE TARGET NOT MET\n";
    Printf.printf "  %.2f ms is %.1fx slower than target\n" p95 (p95 /. 20.0);
    Printf.printf "  Need %.1f%% improvement to meet target\n" ((p95 -. 20.0) /. p95 *. 100.0)
  end;
  
  print_endline "\n=== REALITY CHECK ===";
  Printf.printf "Claimed: 17.7ms P95\n";
  Printf.printf "Actual: %.2f ms P95\n" p95;
  Printf.printf "Difference: %.1fx %s than claimed\n"
    (if p95 > 17.7 then p95 /. 17.7 else 17.7 /. p95)
    (if p95 > 17.7 then "slower" else "faster")