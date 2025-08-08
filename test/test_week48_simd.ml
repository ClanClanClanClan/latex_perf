(* Week 48 SIMD Performance Gate Test *)
(* Target: ≤8ms P95 for 1.1MB benchmark file *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0

let benchmark_implementation name f input iterations =
  Printf.printf "🚀 %s\n" name;
  Printf.printf "   Target: ≤8ms P95 (Week 48 SIMD Gate)\n";
  
  (* Warmup *)
  for _ = 1 to 5 do ignore (f input) done;
  
  (* Measure *)
  let times = Array.init iterations (fun _ -> time_function f input) in
  Array.sort compare times;
  
  let median = times.(iterations / 2) in
  let p95 = times.((iterations * 95) / 100) in
  let min = times.(0) in
  let max = times.(iterations - 1) in
  
  Printf.printf "   📊 Min=%.2fms  Median=%.2fms  P95=%.2fms  Max=%.2fms\n"
    min median p95 max;
  
  (* Check Week 48 gate *)
  let target = 8.0 in
  if p95 <= target then
    Printf.printf "   ✅ Week 48 Gate: %.2fms ≤ %.1fms (PASSED)\n\n" p95 target
  else
    Printf.printf "   ❌ Week 48 Gate: %.2fms > %.1fms (need %.1f%% improvement)\n\n" 
      p95 target (((p95 /. target) -. 1.0) *. 100.0);
  
  (median, p95)

let () =
  Printf.printf "LaTeX Perfectionist v25 - Week 48 SIMD Performance Gate Test\n";
  Printf.printf "=============================================================\n\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists benchmark_file) then begin
    Printf.printf "❌ Error: Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  let ic = open_in benchmark_file in
  let file_size = in_channel_length ic in
  let input = really_input_string ic file_size in
  close_in ic;
  
  let file_size_mb = (float_of_int file_size) /. (1024.0 *. 1024.0) in
  Printf.printf "📁 Benchmark: %s (%.2f MB)\n\n" benchmark_file file_size_mb;
  
  Printf.printf "🏁 Performance Gate Testing:\n";
  Printf.printf "==============================\n\n";
  
  (* Test current best implementation *)
  let enhanced_med, enhanced_p95 = 
    benchmark_implementation "Track A Enhanced (Current Default)" 
      Core.L0_lexer_track_a_enhanced.tokenize_enhanced input 25 in
  
  (* Test SIMD implementation *)
  let simd_med, simd_p95 = 
    benchmark_implementation "Track A SIMD (Week 48 Target)" 
      Core.L0_lexer_track_a_simd.tokenize_simd input 25 in
  
  (* Overall analysis *)
  Printf.printf "🎯 GATE ANALYSIS:\n";
  Printf.printf "==================\n";
  
  let week39_target = 20.0 in
  let week48_target = 8.0 in
  
  Printf.printf "Week 39 Gate (≤20ms scalar):\n";
  if enhanced_p95 <= week39_target then
    Printf.printf "  ✅ Enhanced: %.2fms ≤ %.1fms (PASSED)\n" enhanced_p95 week39_target
  else
    Printf.printf "  ❌ Enhanced: %.2fms > %.1fms\n" enhanced_p95 week39_target;
  
  Printf.printf "\nWeek 48 Gate (≤8ms SIMD):\n";
  if simd_p95 <= week48_target then
    Printf.printf "  ✅ SIMD: %.2fms ≤ %.1fms (PASSED)\n" simd_p95 week48_target
  else
    Printf.printf "  ❌ SIMD: %.2fms > %.1fms\n" simd_p95 week48_target;
  
  Printf.printf "\n🏆 FINAL RESULT:\n";
  Printf.printf "=================\n";
  
  let both_passed = (enhanced_p95 <= week39_target) && (simd_p95 <= week48_target) in
  
  if both_passed then (
    Printf.printf "🎉 SUCCESS: BOTH Week 39 AND Week 48 gates PASSED!\n";
    Printf.printf "   LaTeX Perfectionist v25 achieves both scalar and SIMD targets\n";
    Printf.printf "   Week 2-3 delivers performance foundation 45+ weeks ahead of schedule\n"
  ) else if enhanced_p95 <= week39_target then (
    Printf.printf "✅ Week 39 Gate: PASSED (scalar performance excellent)\n";
    Printf.printf "🔄 Week 48 Gate: Needs %.1f%% improvement for SIMD target\n"
      (((simd_p95 /. week48_target) -. 1.0) *. 100.0)
  ) else (
    Printf.printf "⚠️  Both gates need additional optimization\n"
  )