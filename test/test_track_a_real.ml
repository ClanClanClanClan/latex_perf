open Printf

let () =
  printf "🔬 REAL TRACK A IMPLEMENTATION TEST\n";
  printf "===================================\n";
  
  let content = 
    try
      let ic = open_in "corpora/perf/perf_smoke_big.tex" in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      printf "✅ Loaded corpus: %d bytes\n" n;
      s
    with _ ->
      printf "❌ Could not load corpus, using synthetic test\n";
      String.concat "\n" [
        "\\documentclass{article}";
        "\\begin{document}";
        String.make 10000 'x';
        "\\end{document}"
      ]
  in
  
  printf "\n--- SIMPLE BASELINE ---\n";
  
  (* Warmup *)
  for _ = 1 to 5 do
    let _ = Core.L0_lexer_track_a_simple.tokenize content in
    Gc.full_major ()
  done;
  
  let simple_times = ref [] in
  let simple_tokens = ref 0 in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let tokens = Core.L0_lexer_track_a_simple.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    simple_times := elapsed :: !simple_times;
    
    if i = 1 then (
      simple_tokens := List.length tokens;
      printf "Token count: %d\n" !simple_tokens
    )
  done;
  
  let simple_sorted = List.sort compare !simple_times in
  let simple_best = List.hd simple_sorted in
  let simple_median = List.nth simple_sorted 7 in
  
  printf "Best: %.2f ms\n" simple_best;
  printf "Median: %.2f ms\n" simple_median;
  
  printf "\n--- PERFECT TRACK A ---\n";
  
  (* Warmup *)
  for _ = 1 to 5 do
    let _ = Core.L0_lexer_track_a_perfect.tokenize content in
    Gc.full_major ()
  done;
  
  let perfect_times = ref [] in
  let perfect_tokens = ref 0 in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let tokens = Core.L0_lexer_track_a_perfect.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    perfect_times := elapsed :: !perfect_times;
    
    if i = 1 then (
      perfect_tokens := List.length tokens;
      printf "Token count: %d\n" !perfect_tokens
    )
  done;
  
  let perfect_sorted = List.sort compare !perfect_times in
  let perfect_best = List.hd perfect_sorted in
  let perfect_median = List.nth perfect_sorted 7 in
  
  printf "Best: %.2f ms\n" perfect_best;
  printf "Median: %.2f ms\n" perfect_median;
  
  printf "\n--- ANALYSIS ---\n";
  
  if !simple_tokens = !perfect_tokens then
    printf "✅ Token counts match (%d)\n" !simple_tokens
  else
    printf "❌ Token mismatch: Simple=%d, Perfect=%d\n" !simple_tokens !perfect_tokens;
  
  if perfect_median < simple_median then (
    let improvement = simple_median /. perfect_median in
    printf "✅ Perfect is %.2fx faster than Simple\n" improvement
  ) else (
    let degradation = perfect_median /. simple_median in
    printf "❌ Perfect is %.2fx SLOWER than Simple\n" degradation
  );
  
  printf "\nTarget verification:\n";
  printf "Tier A (≤20ms): %s (Perfect=%.2fms)\n"
    (if perfect_median <= 20.0 then "✅ PASS" else "❌ FAIL") perfect_median;
  printf "Spec claim (≤18.7ms): %s (Perfect=%.2fms)\n"
    (if perfect_median <= 18.7 then "✅ PASS" else "❌ FAIL") perfect_median;
  
  printf "\n🏁 REAL IMPLEMENTATION TEST COMPLETE\n"