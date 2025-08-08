(* Ultra V2 vs Enhanced Performance Test *)
(* Target: ≤8ms for Week 48 SIMD-equivalent performance *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0

let benchmark name f input iterations =
  Printf.printf "%s\n" name;
  
  (* Warmup *)
  for _ = 1 to 5 do ignore (f input) done;
  
  (* Measure *)
  let times = Array.init iterations (fun _ -> time_function f input) in
  Array.sort compare times;
  
  let median = times.(iterations / 2) in
  let p95 = times.((iterations * 95) / 100) in
  let min = times.(0) in
  
  Printf.printf "  Min=%.2fms  Median=%.2fms  P95=%.2fms\n\n" min median p95;
  (median, p95)

let () =
  Printf.printf "Ultra V2 vs Enhanced Performance Test\n";
  Printf.printf "=====================================\n\n";
  
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists benchmark_file) then begin
    Printf.printf "❌ Error: Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  let ic = open_in benchmark_file in
  let file_size = in_channel_length ic in
  let input = really_input_string ic file_size in
  close_in ic;
  
  Printf.printf "Benchmark: %.1f MB\n\n" ((float_of_int file_size) /. 1024.0 /. 1024.0);
  
  let enhanced_med, enhanced_p95 = 
    benchmark "Track A Enhanced (Current)" Core.L0_lexer_track_a_enhanced.tokenize_enhanced input 20 in
  
  let ultra_v2_med, ultra_v2_p95 = 
    benchmark "Track A Ultra V2 (≤8ms Target)" Core.L0_lexer_track_a_ultra_v2.tokenize_ultra_v2 input 20 in
  
  Printf.printf "Performance Analysis:\n";
  Printf.printf "=====================\n";
  
  let speedup = enhanced_med /. ultra_v2_med in
  if speedup > 1.0 then
    Printf.printf "Ultra V2 is %.2fx faster\n" speedup
  else
    Printf.printf "Enhanced is %.2fx faster\n" (1.0 /. speedup);
  
  Printf.printf "\nGate Status:\n";
  Printf.printf "============\n";
  Printf.printf "Week 39 (≤20ms): Enhanced %.2fms %s\n" enhanced_p95 
    (if enhanced_p95 <= 20.0 then "✅ PASSED" else "❌ FAILED");
  Printf.printf "Week 48 (≤8ms):  Ultra V2 %.2fms %s\n" ultra_v2_p95
    (if ultra_v2_p95 <= 8.0 then "✅ PASSED" else "❌ FAILED");
  
  if ultra_v2_p95 <= 8.0 then
    Printf.printf "\n🎉 SUCCESS: Week 48 SIMD-equivalent target achieved!\n"
  else
    Printf.printf "\n⚠️  Need %.1f%% improvement for Week 48 target\n" 
      (((ultra_v2_p95 /. 8.0) -. 1.0) *. 100.0)