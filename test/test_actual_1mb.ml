(* ACTUAL 1.1MB Test - Enhanced Implementation - NO EXTRAPOLATION *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0

let () =
  Printf.printf "ACTUAL Enhanced Implementation Test - Full 1.1MB File\n";
  Printf.printf "===================================================\n\n";
  
  let big_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists big_file) then (
    Printf.printf "❌ File not found: %s\n" big_file;
    exit 1
  );
  
  (* Read the ACTUAL 1.1MB file *)
  let ic = open_in big_file in
  let file_size = in_channel_length ic in
  let full_content = really_input_string ic file_size in
  close_in ic;
  
  Printf.printf "File: %s\n" big_file;
  Printf.printf "Size: %d bytes (%.2f MB)\n\n" file_size
    ((float_of_int file_size) /. 1024.0 /. 1024.0);
  
  (* Use Core.L0_lexer which is set to Enhanced implementation *)
  Printf.printf "Testing Core.L0_lexer (Enhanced implementation) on FULL FILE...\n";
  
  (* Warmup - fewer iterations for large file *)
  Printf.printf "Warmup (3 iterations)... ";
  for _ = 1 to 3 do
    ignore (Core.L0_lexer.tokenize full_content);
    Printf.printf "."
  done;
  Printf.printf " done\n\n";
  
  (* Measure with actual 1.1MB file *)
  Printf.printf "Measuring 10 iterations on ACTUAL 1.1MB... ";
  let times = ref [] in
  for i = 1 to 10 do
    let t = time_function Core.L0_lexer.tokenize full_content in
    times := t :: !times;
    Printf.printf ".";
    flush_all ()
  done;
  Printf.printf " done\n\n";
  
  let sorted = List.sort compare !times in
  let median = List.nth sorted 5 in
  let p95 = List.nth sorted 9 in
  let best = List.hd sorted in
  let worst = List.nth sorted 9 in
  
  Printf.printf "ACTUAL RESULTS - ENHANCED ON 1.1MB:\n";
  Printf.printf "====================================\n";
  Printf.printf "  Best:   %.2f ms\n" best;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  P95:    %.2f ms\n" p95;
  Printf.printf "  Worst:  %.2f ms\n\n" worst;
  
  let throughput = (float_of_int file_size) /. (median /. 1000.0) /. 1024.0 /. 1024.0 in
  Printf.printf "Throughput: %.1f MB/s\n\n" throughput;
  
  Printf.printf "PERFORMANCE GATE ANALYSIS (ACTUAL MEASUREMENT):\n";
  Printf.printf "================================================\n";
  
  Printf.printf "Week 39 Target (≤20ms): ";
  if p95 <= 20.0 then
    Printf.printf "✅ PASSED (%.2fms ≤ 20ms)\n" p95
  else
    Printf.printf "❌ FAILED (%.2fms > 20ms - need %.1f%% improvement)\n"
      p95 (((p95 /. 20.0) -. 1.0) *. 100.0);
      
  Printf.printf "Week 48 Target (≤8ms):  ";
  if p95 <= 8.0 then
    Printf.printf "✅ PASSED (%.2fms ≤ 8ms)\n" p95
  else
    Printf.printf "❌ FAILED (%.2fms > 8ms - need %.1f%% improvement)\n"
      p95 (((p95 /. 8.0) -. 1.0) *. 100.0);
      
  Printf.printf "\nTHIS IS THE DEFINITIVE RESULT - ACTUAL 1.1MB TEST\n";
  Printf.printf "Enhanced Implementation P95: %.2f ms\n" p95