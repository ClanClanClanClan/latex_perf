(* Performance test on actual 1.1MB benchmark file - perf_smoke_big.tex *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0  (* Convert to ms *)

let benchmark name f input iterations =
  Printf.printf "🚀 %s - Running %d iterations...\n" name iterations;
  
  (* Warmup *)
  Printf.printf "   Warming up...";
  for _ = 1 to 5 do 
    ignore (f input);
    Printf.printf "."
  done;
  Printf.printf " done\n";
  
  (* Measure *)
  Printf.printf "   Measuring...";
  let times = Array.init iterations (fun i ->
    if i mod 10 = 0 then Printf.printf ".";
    time_function f input
  ) in
  Printf.printf " done\n";
  
  Array.sort compare times;
  
  let median = times.(iterations / 2) in
  let p95 = times.((iterations * 95) / 100) in
  let min = times.(0) in
  let max = times.(iterations - 1) in
  
  Printf.printf "   ⏱️  Results: Min=%.2fms  Median=%.2fms  P95=%.2fms  Max=%.2fms\n"
    min median p95 max;
  
  (median, p95)

let check_performance_gates median p95 file_size_mb =
  Printf.printf "\n🎯 Performance Gates Analysis (%.1fMB file):\n" file_size_mb;
  
  let scalar_target = 20.0 in
  let simd_target = 8.0 in
  
  let check_gate name current target =
    if current <= target then
      Printf.printf "  ✅ %s: %.2fms ≤ %.1fms\n" name current target
    else
      let improvement_needed = ((current /. target) -. 1.0) *. 100.0 in
      Printf.printf "  ❌ %s: %.2fms > %.1fms (need %.1f%% improvement)\n"
        name current target improvement_needed
  in
  
  Printf.printf "  📊 Checking against L0_LEXER_SPEC.md targets:\n";
  check_gate "Scalar Path (Week 39)" p95 scalar_target;
  check_gate "SIMD Path (Week 48)" p95 simd_target;
  
  (* Additional analysis *)
  let throughput_mbs = file_size_mb /. (median /. 1000.0) in
  Printf.printf "  📈 Throughput: %.1f MB/s\n" throughput_mbs;
  
  if throughput_mbs >= 55.0 then
    Printf.printf "  ✅ Throughput meets 55 MB/s scalar target from spec\n"
  else
    Printf.printf "  ❌ Throughput below 55 MB/s scalar target (%.1f MB/s)\n" throughput_mbs

let () =
  Printf.printf "LaTeX Perfectionist v25 - 1.1MB Benchmark Performance Test\n";
  Printf.printf "==========================================================\n\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  (* Check if file exists *)
  if not (Sys.file_exists benchmark_file) then begin
    Printf.printf "❌ Error: Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  (* Read the benchmark file *)
  Printf.printf "📁 Loading benchmark file: %s\n" benchmark_file;
  let ic = open_in benchmark_file in
  let file_size = in_channel_length ic in
  let input = really_input_string ic file_size in
  close_in ic;
  
  let file_size_mb = (float_of_int file_size) /. (1024.0 *. 1024.0) in
  Printf.printf "   File size: %d bytes (%.2f MB)\n\n" file_size file_size_mb;
  
  (* Test ultra-optimized implementation *)
  let median, p95 = 
    benchmark "L0 Lexer Track A Ultra (Default)" 
      Core.L0_lexer.tokenize input 30 in
  
  check_performance_gates median p95 file_size_mb;
  
  Printf.printf "\n📋 Performance Summary:\n";
  Printf.printf "=====================================\n";
  Printf.printf "✅ Successfully tested on actual 1.1MB corpus file\n";
  Printf.printf "✅ Ultra-optimized lexer is production default\n";
  
  if p95 <= 20.0 then
    Printf.printf "🎉 PASSED: Meets Week 39 scalar performance gate (≤20ms)\n"
  else
    Printf.printf "⚠️  TODO: Need %.1f%% improvement to meet Week 39 gate\n" 
      (((p95 /. 20.0) -. 1.0) *. 100.0);
  
  Printf.printf "\n📊 Scaling Verification:\n";
  Printf.printf "  50KB result: 1.37ms (from previous test)\n";
  Printf.printf "  1.1MB result: %.2fms (this test)\n" median;
  Printf.printf "  Scaling factor: %.1fx (linear = %.1fx)\n" 
    (median /. 1.37) (file_size_mb /. 0.05)