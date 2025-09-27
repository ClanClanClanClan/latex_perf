open Printf
open Unix

(* Load the SIMD validation functions *)
module Simd_val = struct
  include Simd_ffi
end

(* Statistics tracking for deviations *)
type validation_stats = {
  total_iterations : int;
  mutable deviations_found : int;
  mutable zero_diffs : int;
  mutable positive_diffs : int;
  mutable negative_diffs : int;
  mutable min_diff : int;
  mutable max_diff : int;
  mutable sum_abs_diffs : int;
  deviation_histogram : (int, int) Hashtbl.t;
}

let create_stats total_iterations =
  {
    total_iterations;
    deviations_found = 0;
    zero_diffs = 0;
    positive_diffs = 0;
    negative_diffs = 0;
    min_diff = 0;
    max_diff = 0;
    sum_abs_diffs = 0;
    deviation_histogram = Hashtbl.create 100;
  }

let update_stats stats diff =
  if diff = 0 then stats.zero_diffs <- stats.zero_diffs + 1
  else (
    stats.deviations_found <- stats.deviations_found + 1;
    if diff > 0 then stats.positive_diffs <- stats.positive_diffs + 1
    else stats.negative_diffs <- stats.negative_diffs + 1;

    stats.min_diff <- min stats.min_diff diff;
    stats.max_diff <- max stats.max_diff diff;
    stats.sum_abs_diffs <- stats.sum_abs_diffs + abs diff;

    let current =
      try Hashtbl.find stats.deviation_histogram diff with Not_found -> 0
    in
    Hashtbl.replace stats.deviation_histogram diff (current + 1))

let print_stats stats duration =
  printf "\n=== SPECIFICATION COMPLIANCE VALIDATION RESULTS ===\n";
  printf "Test Duration: %.2f seconds (%.2f minutes)\n" duration
    (duration /. 60.0);
  printf "Total Iterations: %d\n" stats.total_iterations;
  printf "Perfect Matches (diff=0): %d (%.2f%%)\n" stats.zero_diffs
    (100.0
    *. float_of_int stats.zero_diffs
    /. float_of_int stats.total_iterations);

  if stats.deviations_found = 0 then (
    printf "🟢 SPECIFICATION COMPLIANCE: PERFECT ✅\n";
    printf "Zero tokenization deviations found across %d iterations\n"
      stats.total_iterations)
  else (
    printf "🔴 SPECIFICATION DEVIATIONS DETECTED: %d ❌\n" stats.deviations_found;
    printf "Deviation Rate: %.6f%% (%d/%d)\n"
      (100.0
      *. float_of_int stats.deviations_found
      /. float_of_int stats.total_iterations)
      stats.deviations_found stats.total_iterations;

    printf "\nDeviation Statistics:\n";
    printf "  Positive diffs (SIMD > scalar): %d\n" stats.positive_diffs;
    printf "  Negative diffs (SIMD < scalar): %d\n" stats.negative_diffs;
    printf "  Min difference: %d tokens\n" stats.min_diff;
    printf "  Max difference: %d tokens\n" stats.max_diff;
    printf "  Mean absolute difference: %.2f tokens\n"
      (float_of_int stats.sum_abs_diffs /. float_of_int stats.deviations_found);

    printf "\nDeviation Histogram (top 10):\n";
    let hist_list =
      Hashtbl.fold (fun k v acc -> (k, v) :: acc) stats.deviation_histogram []
    in
    let sorted = List.sort (fun (_, v1) (_, v2) -> compare v2 v1) hist_list in
    List.iteri
      (fun i (diff, count) ->
        if i < 10 then printf "  diff=%d: %d occurrences\n" diff count)
      sorted)

let run_spec_validation_test file_path iterations =
  printf "🔍 COMPREHENSIVE SPECIFICATION COMPLIANCE VALIDATION\n";
  printf "==================================================\n";
  printf "Input file: %s\n" file_path;
  printf "Iterations: %d\n" iterations;

  if not (Sys.file_exists file_path) then
    failwith (sprintf "Test file not found: %s" file_path);

  (* Read test file *)
  let ic = open_in file_path in
  let file_size = in_channel_length ic in
  let input_bytes = Bytes.create file_size in
  really_input ic input_bytes 0 file_size;
  close_in ic;

  printf "File size: %d bytes (%.1f KB)\n" file_size
    (float_of_int file_size /. 1024.0);

  let stats = create_stats iterations in
  let start_time = gettimeofday () in

  printf "\nRunning validation iterations...\n";
  let progress_interval = max 1 (iterations / 100) in

  for i = 1 to iterations do
    if i mod progress_interval = 0 then (
      printf "\rProgress: %d/%d (%.1f%%)" i iterations
        (100.0 *. float_of_int i /. float_of_int iterations);
      flush stdout);

    try
      let simd_buf, scalar_buf, diff =
        Simd_val.benchmark_simd_vs_scalar input_bytes 10000
      in
      update_stats stats diff
    with
    | Failure msg ->
        printf "\nERROR at iteration %d: %s\n" i msg;
        stats.deviations_found <- stats.deviations_found + 1
    | e ->
        printf "\nUNEXPECTED ERROR at iteration %d: %s\n" i
          (Printexc.to_string e);
        stats.deviations_found <- stats.deviations_found + 1
  done;

  printf "\rCompleted: %d/%d (100.0%%)\n" iterations iterations;

  let end_time = gettimeofday () in
  let duration = end_time -. start_time in

  print_stats stats duration;

  (* Exit with appropriate code *)
  if stats.deviations_found = 0 then (
    printf
      "\n\
       ✅ VALIDATION PASSED: SIMD tokenizer fully compliant with specification\n";
    exit 0)
  else (
    printf "\n❌ VALIDATION FAILED: %d specification deviations detected\n"
      stats.deviations_found;
    exit 1)

let () =
  if Array.length Sys.argv < 3 then (
    printf "Usage: %s <test_file> <iterations>\n" Sys.argv.(0);
    printf "Example: %s corpora/perf/perf_smoke_big.tex 100000\n" Sys.argv.(0);
    exit 1);

  let test_file = Sys.argv.(1) in
  let iterations = int_of_string Sys.argv.(2) in

  printf "SIMD Tokenizer Specification Compliance Validator\n";
  printf "================================================\n";

  try run_spec_validation_test test_file iterations with
  | Failure msg ->
      printf "FATAL ERROR: %s\n" msg;
      exit 2
  | e ->
      printf "UNEXPECTED ERROR: %s\n" (Printexc.to_string e);
      exit 2
