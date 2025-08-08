(* Direct L0 Performance Verification *)

open Printf

let () =
  printf "\n=== L0 PERFORMANCE VERIFICATION ===\n";
  printf "Testing actual benchmark file: perf_smoke_big.tex\n\n";
  
  (* Load the actual benchmark file *)
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists benchmark_file) then begin
    printf "❌ Benchmark file not found: %s\n" benchmark_file;
    exit 1
  end;
  
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  printf "📁 Loaded benchmark file: %d bytes (%.2f MB)\n\n" 
    size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* First check what modules are available *)
  printf "🔍 Checking available L0 implementations:\n";
  
  (* Try L0_lexer_track_a_arena *)
  try
    printf "  Testing L0_lexer_track_a_arena.tokenize... ";
    flush stdout;
    
    (* Do a quick test *)
    let test_tokens = L0_lexer_track_a_arena.tokenize "test" in
    printf "✅ Works! (%d tokens from 'test')\n" (List.length test_tokens);
    
    (* Now do the performance test *)
    printf "\n⏱️  Running performance test (5 runs):\n";
    
    (* Warm-up *)
    let _ = L0_lexer_track_a_arena.tokenize content in
    
    (* Timed runs *)
    let times = ref [] in
    for i = 1 to 5 do
      let start = Unix.gettimeofday () in
      let tokens = L0_lexer_track_a_arena.tokenize content in
      let stop = Unix.gettimeofday () in
      let elapsed_ms = (stop -. start) *. 1000.0 in
      times := elapsed_ms :: !times;
      printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (List.length tokens)
    done;
    
    (* Calculate stats *)
    let sorted_times = List.sort compare !times in
    let p95 = List.nth sorted_times 4 in
    let avg = (List.fold_left (+.) 0.0 !times) /. 5.0 in
    
    printf "\n📊 Results:\n";
    printf "  Average: %.2f ms\n" avg;
    printf "  P95: %.2f ms\n" p95;
    printf "  Target: ≤20ms\n\n";
    
    if p95 <= 20.0 then begin
      printf "✅ PERFORMANCE TARGET MET!\n";
      printf "  %.2f ms is %.1f%% better than target\n" p95 ((20.0 -. p95) /. 20.0 *. 100.0)
    end else begin
      printf "❌ PERFORMANCE TARGET NOT MET\n";
      printf "  %.2f ms is %.1fx slower than target\n" p95 (p95 /. 20.0)
    end
    
  with e ->
    printf "❌ Error: %s\n\n" (Printexc.to_string e);
    
    (* Try raw tokenize interface *)
    try
      printf "  Testing L0_lexer_track_a_arena.tokenize_raw... ";
      flush stdout;
      
      let packed = L0_lexer_track_a_arena.tokenize_raw content in
      printf "✅ Works! (%d packed tokens)\n" (Array.length packed);
      
      (* Test raw performance *)
      printf "\n⏱️  Testing raw tokenizer performance:\n";
      
      let times = ref [] in
      for i = 1 to 5 do
        let start = Unix.gettimeofday () in
        let packed = L0_lexer_track_a_arena.tokenize_raw content in
        let stop = Unix.gettimeofday () in
        let elapsed_ms = (stop -. start) *. 1000.0 in
        times := elapsed_ms :: !times;
        printf "  Run %d: %.2f ms (%d packed tokens)\n" i elapsed_ms (Array.length packed)
      done;
      
      let sorted_times = List.sort compare !times in
      let p95 = List.nth sorted_times 4 in
      printf "\n  Raw tokenizer P95: %.2f ms\n" p95
      
    with e ->
      printf "❌ Error: %s\n" (Printexc.to_string e);
      
  printf "\n=== END VERIFICATION ===\n"