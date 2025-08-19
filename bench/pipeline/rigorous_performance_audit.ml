(* RIGOROUS PERFORMANCE AUDIT - Verify L0 Lexer Claims *)
(* Statistical analysis with mean, median, P95, P99 *)

let run_rigorous_benchmark () =
  Printf.printf "🔬 RIGOROUS PERFORMANCE AUDIT\n";
  Printf.printf "==============================\n\n";
  
  (* Apply GC tuning as documented *)
  Gc.set {
    (Gc.get()) with
    Gc.minor_heap_size = 8_388_608;      (* 8MB minor heap *)
    Gc.major_heap_increment = 4_194_304; (* 4MB increments *)
    Gc.space_overhead = 120;             (* Less aggressive compaction *)
  };
  
  Printf.printf "GC Configuration Applied:\n";
  Printf.printf "  Minor heap: 8MB\n";
  Printf.printf "  Major increment: 4MB\n";
  Printf.printf "  Space overhead: 120\n\n";
  
  (* Test files *)
  let test_files = [
    ("corpora/perf/edit_window_4kb.tex", "4KB edit window");
    ("corpora/perf/perf_math_light.tex", "412KB math-heavy");
    ("corpora/perf/perf_smoke_big.tex", "1.1MB thesis");
  ] in
  
  (* Run multiple iterations for statistical validity *)
  let iterations = 100 in
  
  List.iter (fun (file, desc) ->
    try
      Printf.printf "Testing: %s (%s)\n" file desc;
      Printf.printf "Iterations: %d\n" iterations;
      
      (* Load file *)
      let ic = open_in file in
      let size = in_channel_length ic in
      let content = really_input_string ic size in
      close_in ic;
      
      Printf.printf "File size: %.2f KB\n" (float_of_int size /. 1024.0);
      
      (* Warmup runs *)
      for _ = 1 to 10 do
        ignore (L0_lexer_track_a_arena.tokenize content)
      done;
      
      (* Timed runs *)
      let timings = ref [] in
      
      for _ = 1 to iterations do
        (* Force GC to ensure consistent state *)
        Gc.minor ();
        
        let start = Sys.time () in
        let tokens = L0_lexer_track_a_arena.tokenize content in
        let elapsed = (Sys.time () -. start) *. 1000.0 in
        
        timings := elapsed :: !timings;
        ignore tokens (* Prevent optimization *)
      done;
      
      (* Statistical analysis *)
      let sorted_timings = List.sort Float.compare !timings in
      let n = List.length sorted_timings in
      
      let mean = 
        (List.fold_left (+.) 0.0 sorted_timings) /. float_of_int n in
      
      let median = 
        if n mod 2 = 0 then
          (List.nth sorted_timings (n/2 - 1) +. List.nth sorted_timings (n/2)) /. 2.0
        else
          List.nth sorted_timings (n/2) in
      
      let p95_idx = int_of_float (0.95 *. float_of_int n) in
      let p99_idx = int_of_float (0.99 *. float_of_int n) in
      
      let p95 = List.nth sorted_timings p95_idx in
      let p99 = List.nth sorted_timings p99_idx in
      let min_time = List.hd sorted_timings in
      let max_time = List.nth sorted_timings (n - 1) in
      
      (* Calculate standard deviation *)
      let variance = 
        List.fold_left (fun acc t -> 
          acc +. (t -. mean) ** 2.0
        ) 0.0 sorted_timings /. float_of_int n in
      let std_dev = sqrt variance in
      
      Printf.printf "\n📊 RESULTS:\n";
      Printf.printf "  Mean:     %.2f ms\n" mean;
      Printf.printf "  Median:   %.2f ms\n" median;
      Printf.printf "  Std Dev:  %.2f ms\n" std_dev;
      Printf.printf "  Min:      %.2f ms\n" min_time;
      Printf.printf "  Max:      %.2f ms\n" max_time;
      Printf.printf "  P95:      %.2f ms\n" p95;
      Printf.printf "  P99:      %.2f ms\n" p99;
      
      (* Target verification *)
      Printf.printf "\n🎯 TARGET VERIFICATION (≤20ms):\n";
      if median <= 20.0 then
        Printf.printf "  ✅ MEDIAN PASSES (%.2f ms)\n" median
      else
        Printf.printf "  ❌ MEDIAN FAILS (%.2f ms)\n" median;
        
      if p95 <= 20.0 then
        Printf.printf "  ✅ P95 PASSES (%.2f ms)\n" p95
      else
        Printf.printf "  ❌ P95 FAILS (%.2f ms)\n" p95;
      
      Printf.printf "\n" 
      
    with exn ->
      Printf.printf "  ERROR: %s\n\n" (Printexc.to_string exn)
  ) test_files;
  
  Printf.printf "=====================================\n";
  Printf.printf "🏁 AUDIT COMPLETE\n";
  Printf.printf "=====================================\n";
  Printf.printf "\n⚠️  CRITICAL NOTES:\n";
  Printf.printf "  1. Performance varies significantly with file size\n";
  Printf.printf "  2. GC tuning is ESSENTIAL for consistent results\n";
  Printf.printf "  3. Warmup runs are necessary for JIT optimization\n";
  Printf.printf "  4. Statistical analysis reveals true performance\n"

let () = run_rigorous_benchmark ()