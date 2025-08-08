(* Test L0 raw tokenizer performance *)

let () =
  print_endline "=== L0 RAW TOKENIZER PERFORMANCE TEST ===\n";
  
  (* Load benchmark file *)
  let benchmark_file = "corpora/perf/perf_smoke_big.tex" in
  let ic = open_in benchmark_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "📁 File: %d bytes (%.2f MB)\n\n" 
    size (float_of_int size /. 1024.0 /. 1024.0);
  
  (* Test 1: Raw tokenizer (returns packed array) *)
  print_endline "Test 1: Raw tokenizer (tokenize_raw)";
  
  let times = ref [] in
  for i = 1 to 10 do
    let start = Sys.time () in
    let packed = L0_lexer_track_a_arena.tokenize_raw content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    times := elapsed :: !times;
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d packed tokens)\n" i elapsed (Array.length packed)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed
  done;
  
  let sorted_times = List.sort compare !times in
  let p95_raw = List.nth sorted_times 9 in
  Printf.printf "\n  Raw P95: %.2f ms\n" p95_raw;
  
  (* Test 2: Full tokenizer (includes conversion) *)
  print_endline "\nTest 2: Full tokenizer (tokenize)";
  
  let times2 = ref [] in
  for i = 1 to 10 do
    let start = Sys.time () in
    let tokens = L0_lexer_track_a_arena.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    times2 := elapsed :: !times2;
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed (List.length tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed
  done;
  
  let sorted_times2 = List.sort compare !times2 in
  let p95_full = List.nth sorted_times2 9 in
  Printf.printf "\n  Full P95: %.2f ms\n" p95_full;
  
  (* Analysis *)
  print_endline "\n📊 ANALYSIS:";
  Printf.printf "  Raw tokenizer: %.2f ms\n" p95_raw;
  Printf.printf "  Full tokenizer: %.2f ms\n" p95_full;
  Printf.printf "  Conversion overhead: %.2f ms (%.1f%%)\n" 
    (p95_full -. p95_raw) ((p95_full -. p95_raw) /. p95_raw *. 100.0);
  Printf.printf "  Target: ≤20ms\n\n";
  
  print_endline "🔍 SPEC COMPLIANCE CHECK:";
  print_endline "  L0 Spec requires:";
  print_endline "    - Bigarray.Array1 ring buffer ❌ (using Bytes)";
  print_endline "    - -O3 -flambda2 compilation ❌ (using just -O3)";
  print_endline "    - ≤20ms on 1.1MB file ❌ (got ~71ms)";
  print_endline "\n  Claimed in docs: 17.7ms ❌ FALSE";
  print_endline "  Spec benchmark: 18.7ms on Ryzen 7950X";
  print_endline "  Our result: ~71ms on M2 Max"