(* LaTeX Perfectionist v25 - SIMD Performance Benchmark
 * Compare Track A (OCaml) vs Track B (SIMD) performance
 *)

open Core

let test_corpus = "corpora/perf_smoke.tex"

(* Generate test input of various sizes *)
let generate_test_input size =
  let chars = [|
    '\\'; 'd'; 'o'; 'c'; 'u'; 'm'; 'e'; 'n'; 't'; 'c'; 'l'; 'a'; 's'; 's'; '{'; 'a'; 'r'; 't'; 'i'; 'c'; 'l'; 'e'; '}'; '\n';
    '\\'; 'b'; 'e'; 'g'; 'i'; 'n'; '{'; 'd'; 'o'; 'c'; 'u'; 'm'; 'e'; 'n'; 't'; '}'; '\n';
    '$'; 'x'; '^'; '2'; ' '; '+'; ' '; 'y'; '^'; '2'; ' '; '='; ' '; 'z'; '^'; '2'; '$'; '\n';
    '\\'; 'e'; 'n'; 'd'; '{'; 'd'; 'o'; 'c'; 'u'; 'm'; 'e'; 'n'; 't'; '}'; '\n'
  |] in
  let pattern_len = Array.length chars in
  let buf = Buffer.create size in
  for i = 0 to size - 1 do
    Buffer.add_char buf chars.(i mod pattern_len)
  done;
  Buffer.contents buf

(* Benchmark a single implementation *)
let benchmark_impl name tokenize_fn input iterations =
  (* Warmup *)
  for _ = 1 to 10 do
    let _ = tokenize_fn input in ()
  done;
  
  (* Actual benchmark *)
  let start_time = Mtime_clock.now () in
  let token_count = ref 0 in
  
  for _ = 1 to iterations do
    let tokens = tokenize_fn input in
    token_count := List.length tokens
  done;
  
  let end_time = Mtime_clock.now () in
  let elapsed_ns = Mtime.Span.to_uint64_ns (Mtime.span start_time end_time) in
  let elapsed_ms = Int64.to_float elapsed_ns /. 1e6 in
  let avg_ms = elapsed_ms /. float_of_int iterations in
  
  Printf.printf "%s:\n" name;
  Printf.printf "  Total time: %.3f ms (%d iterations)\n" elapsed_ms iterations;
  Printf.printf "  Average: %.3f ms/iteration\n" avg_ms;
  Printf.printf "  Tokens: %d\n" !token_count;
  Printf.printf "  Throughput: %.1f MB/s\n" 
    (float_of_int (String.length input * iterations) /. elapsed_ms /. 1000.0);
  
  avg_ms

(* Test with Track B if available *)
let test_track_b_available () =
  try
    let _ = Core.Track_b_ffi.init () in
    let (avail, name) = Core.Track_b_ffi.simd_info () in
    Printf.printf "Track B SIMD: %s (%s)\n" 
      (if avail then "Available" else "Not available") name;
    avail
  with _ -> 
    Printf.printf "Track B not available (FFI not compiled)\n";
    false

(* Main benchmark *)
let run_benchmarks () =
  Printf.printf "🚀 LaTeX Perfectionist v25 - SIMD Performance Benchmark\n";
  Printf.printf "=" ^ String.make 58 '=' ^ "\n\n";
  
  (* Test different input sizes *)
  let test_sizes = [1024; 10240; 102400; 1024000] in
  
  List.iter (fun size ->
    Printf.printf "\n📊 Testing with %d bytes input:\n" size;
    Printf.printf "-" ^ String.make 40 '-' ^ "\n";
    
    let input = generate_test_input size in
    let iterations = max 1 (100000 / size) in (* Adjust iterations based on size *)
    
    (* Benchmark Track A (pure OCaml) *)
    let track_a_time = benchmark_impl "Track A (OCaml)" Lexer_v25.tokenize input iterations in
    
    (* Benchmark Track B if available *)
    if test_track_b_available () then begin
      let track_b_time = benchmark_impl "Track B (SIMD)" Core.Track_b_ffi.tokenize input iterations in
      
      let speedup = track_a_time /. track_b_time in
      Printf.printf "\n🎯 Speedup: %.2fx\n" speedup;
      
      (* Check against performance targets *)
      Printf.printf "\n📈 Performance vs Targets:\n";
      let check_target name target_ms current_ms =
        if current_ms < target_ms then
          Printf.printf "  %s: %.2f ms < %.1f ms ✅ PASS\n" name current_ms target_ms
        else
          Printf.printf "  %s: %.2f ms >= %.1f ms ❌ NEED %.1f%% improvement\n" 
            name current_ms target_ms ((current_ms /. target_ms -. 1.0) *. 100.0)
      in
      
      check_target "Week 4 target" 4.0 track_b_time;
      check_target "Week 5 target" 2.0 track_b_time;
      check_target "Final target" 1.0 track_b_time;
    end else begin
      Printf.printf "\n⚠️  Track B not available - cannot measure SIMD speedup\n"
    end
  ) test_sizes;
  
  (* Test with actual corpus if available *)
  if Sys.file_exists test_corpus then begin
    Printf.printf "\n\n📄 Testing with real corpus: %s\n" test_corpus;
    Printf.printf "=" ^ String.make 58 '=' ^ "\n";
    
    let ic = open_in test_corpus in
    let input = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    Printf.printf "Corpus size: %d bytes (%.1f MB)\n" 
      (String.length input) (float_of_int (String.length input) /. 1024.0 /. 1024.0);
    
    let iterations = 10 in
    let track_a_time = benchmark_impl "Track A (OCaml)" Lexer_v25.tokenize input iterations in
    
    if test_track_b_available () then begin
      let track_b_time = benchmark_impl "Track B (SIMD)" Core.Track_b_ffi.tokenize input iterations in
      Printf.printf "\n🎯 Real corpus speedup: %.2fx\n" (track_a_time /. track_b_time);
    end
  end

let () = run_benchmarks ()