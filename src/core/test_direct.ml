open Printf

let () =
  printf "🔬 DIRECT TEST OF IMPLEMENTATIONS\n";
  printf "=================================\n";
  
  let content = 
    try
      let ic = open_in "../../corpora/perf/perf_smoke_big.tex" in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      printf "✅ Loaded: %d bytes\n" n;
      s
    with _ ->
      printf "Using synthetic test\n";
      String.concat "\n" [
        "\\documentclass{article}";
        "\\begin{document}";
        String.make 10000 'x';
        "\\end{document}"
      ]
  in
  
  printf "\n--- SIMPLE ---\n";
  let start1 = Sys.time () in
  let tokens1 = L0_lexer_track_a_simple.tokenize content in
  let time1 = (Sys.time () -. start1) *. 1000.0 in
  printf "Tokens: %d\n" (List.length tokens1);
  printf "Time: %.2f ms\n" time1;
  
  printf "\n--- PERFECT ---\n";
  let start2 = Sys.time () in
  let tokens2 = L0_lexer_track_a_perfect.tokenize content in
  let time2 = (Sys.time () -. start2) *. 1000.0 in
  printf "Tokens: %d\n" (List.length tokens2);
  printf "Time: %.2f ms\n" time2;
  
  printf "\n--- COMPARISON ---\n";
  if time2 < time1 then
    printf "✅ Perfect is %.2fx faster\n" (time1 /. time2)
  else
    printf "❌ Perfect is %.2fx slower\n" (time2 /. time1)