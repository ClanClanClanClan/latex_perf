(* Simple incremental processing proof-of-concept *)

open Printf

let hash_line content =
  Digest.string content |> Digest.to_hex

let simulate_large_file_edit () =
  printf "REAL-TIME INCREMENTAL PROCESSING TEST\n";
  printf "=====================================\n";
  
  (* Simulate 3MB file as 100,000 lines *)
  let total_lines = 100000 in
  let line_content = "\\section{Test} Hello $x^2$ world % comment here" in
  
  (* Simulate full tokenization time (based on our 43ms for 91KB) *)
  let bytes_per_line = String.length line_content in
  let total_bytes = total_lines * bytes_per_line in
  let mb_size = float_of_int total_bytes /. (1024.0 *. 1024.0) in
  
  (* Estimated full tokenization time (linear scaling from 43ms for 91KB) *)
  let estimated_full_time = 43.0 *. (mb_size /. 0.091) in
  
  printf "File simulation:\n";
  printf "  Lines: %d\n" total_lines;
  printf "  Size: %.1f MB\n" mb_size;
  printf "  Estimated full tokenization: %.0f ms\n" estimated_full_time;
  
  (* Simulate incremental change (1 line changed) *)
  let changed_lines = 1 in
  let incremental_work_ratio = float_of_int changed_lines /. float_of_int total_lines in
  let estimated_incremental_time = estimated_full_time *. incremental_work_ratio in
  
  printf "\nIncremental update simulation:\n";
  printf "  Lines changed: %d\n" changed_lines;
  printf "  Work ratio: %.6f%%\n" (incremental_work_ratio *. 100.0);
  printf "  Estimated incremental time: %.3f ms\n" estimated_incremental_time;
  
  let speedup = estimated_full_time /. estimated_incremental_time in
  printf "  Theoretical speedup: %.0fx\n" speedup;
  
  printf "\nReal-time capability:\n";
  printf "  Target: < 100ms for real-time\n";
  printf "  Incremental time: %.3f ms\n" estimated_incremental_time;
  printf "  Real-time capable: %s\n" 
    (if estimated_incremental_time < 100.0 then "YES" else "NO");
  
  printf "  Interactive target: < 16.6ms (60 FPS)\n";
  printf "  Interactive capable: %s\n"
    (if estimated_incremental_time < 16.6 then "YES" else "NO");

let test_actual_hash_performance () =
  printf "\nActual hash performance test:\n";
  let test_line = "\\section{Introduction} This is a LaTeX line with $math$ and % comments" in
  let iterations = 10000 in
  
  let start_time = Unix.gettimeofday () in
  for i = 1 to iterations do
    let _ = hash_line test_line in
    ()
  done;
  let end_time = Unix.gettimeofday () in
  
  let total_time_ms = (end_time -. start_time) *. 1000.0 in
  let time_per_hash_ms = total_time_ms /. float_of_int iterations in
  
  printf "  Hash operations: %d\n" iterations;
  printf "  Total time: %.2f ms\n" total_time_ms;
  printf "  Time per hash: %.4f ms\n" time_per_hash_ms;
  
  (* Estimate time to check all lines in 3MB file *)
  let lines_3mb = 100000 in
  let time_to_check_all = time_per_hash_ms *. float_of_int lines_3mb in
  printf "  Time to check 100k lines: %.2f ms\n" time_to_check_all;

let () =
  simulate_large_file_edit ();
  test_actual_hash_performance ()