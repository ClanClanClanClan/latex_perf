(* ACTUAL 1MB Performance Test - Uses real perf_smoke_big.tex file *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0  (* Convert to ms *)

let () =
  Printf.printf "LaTeX Perfectionist v25 - ACTUAL 1MB Performance Test\n";
  Printf.printf "=====================================================\n\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists benchmark_file) then begin
    Printf.printf "❌ Error: Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  Printf.printf "📁 Loading actual benchmark file: %s\n" benchmark_file;
  let ic = open_in benchmark_file in
  let file_size = in_channel_length ic in
  let actual_input = really_input_string ic file_size in
  close_in ic;
  
  Printf.printf "   File size: %d bytes (%.2f MB)\n\n" file_size
    ((float_of_int file_size) /. 1024.0 /. 1024.0);
  
  (* Warmup - fewer iterations for large file *)
  Printf.printf "🔥 Warmup (5 iterations)... ";
  for _ = 1 to 5 do
    ignore (Core.L0_lexer.tokenize actual_input);
    Printf.printf "."
  done;
  Printf.printf " done\n\n";
  
  (* Measure on ACTUAL 1.1MB file *)
  Printf.printf "⏱️  Measuring (15 iterations)... ";
  let times = ref [] in
  for i = 1 to 15 do
    let t = time_function Core.L0_lexer.tokenize actual_input in
    times := t :: !times;
    if i mod 3 = 0 then Printf.printf ".";
    flush_all ()
  done;
  Printf.printf " done\n\n";
  
  let sorted = List.sort compare !times in
  let median = List.nth sorted 7 in
  let p95 = List.nth sorted 14 in
  let best = List.hd sorted in
  let worst = List.nth sorted 14 in
  
  Printf.printf "🎯 ACTUAL RESULTS - Enhanced Implementation:\n";
  Printf.printf "============================================\n";
  Printf.printf "  Best:   %.2f ms\n" best;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  P95:    %.2f ms\n" p95;
  Printf.printf "  Worst:  %.2f ms\n\n" worst;
  
  let throughput = (float_of_int file_size) /. (median /. 1000.0) /. 1024.0 /. 1024.0 in
  Printf.printf "📈 Throughput: %.1f MB/s\n\n" throughput;
  
  Printf.printf "🚪 PERFORMANCE GATE STATUS:\n";
  Printf.printf "============================\n";
  
  let week39_target = 20.0 in
  let week48_target = 8.0 in
  
  Printf.printf "Week 39 Gate (≤%.1fms): " week39_target;
  if p95 <= week39_target then
    Printf.printf "✅ PASSED (%.2fms ≤ %.1fms)\n" p95 week39_target
  else
    Printf.printf "❌ FAILED (%.2fms > %.1fms) - need %.1f%% improvement\n" 
      p95 week39_target (((p95 /. week39_target) -. 1.0) *. 100.0);
  
  Printf.printf "Week 48 Gate (≤%.1fms): " week48_target;
  if p95 <= week48_target then
    Printf.printf "✅ PASSED (%.2fms ≤ %.1fms)\n" p95 week48_target
  else
    Printf.printf "❌ FAILED (%.2fms > %.1fms) - need %.1f%% improvement\n"
      p95 week48_target (((p95 /. week48_target) -. 1.0) *. 100.0);
      
  Printf.printf "\n🔍 ANALYSIS:\n";
  Printf.printf "Implementation: Enhanced OCaml (src/core/l0_lexer.ml)\n";
  Printf.printf "Test File: Actual %s (%.2f MB)\n" benchmark_file
    ((float_of_int file_size) /. 1024.0 /. 1024.0);
  Printf.printf "Definitive P95: %.2f ms\n" p95;
  
  Printf.printf "\n✅ THIS IS THE TRUTH - NO EXTRAPOLATION\n"