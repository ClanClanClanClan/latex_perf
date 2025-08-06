(* Test the CORRECT production lexers *)

(* L0 wrapper to convert token list to located_token list *)
let l0_wrapper input = 
  let tokens = Core.Lexer_optimized_v25.tokenize_to_list input in
  List.map (fun tok -> { Core.Lexer_v25.token = tok; loc = Data.Location.make 1 1 }) tokens

let test_lexer name lexer_func input =
  let size = String.length input in
  Printf.printf "\n=== Testing %s on %d bytes ===\n" name size;
  
  (* Warm up *)
  let _ = lexer_func input in
  
  (* Test 5 times *)
  let times = ref [] in
  for i = 1 to 5 do
    let start = Unix.gettimeofday () in
    let tokens = lexer_func input in
    let stop = Unix.gettimeofday () in
    let elapsed_ms = (stop -. start) *. 1000.0 in
    times := elapsed_ms :: !times;
    Printf.printf "  Run %d: %.3f ms (%d tokens)\n" i elapsed_ms (List.length tokens)
  done;
  
  (* Calculate average *)
  let avg_ms = List.fold_left (+.) 0.0 !times /. float_of_int (List.length !times) in
  Printf.printf "Average: %.3f ms\n" avg_ms;
  
  (* Extrapolate to 1.1MB *)
  let scale_factor = (1.1 *. 1024.0 *. 1024.0) /. float_of_int size in
  let estimated_1_1mb = avg_ms *. scale_factor in
  Printf.printf "Extrapolated 1.1MB: %.3f ms\n" estimated_1_1mb;
  Printf.printf "SLA check (42ms): %s\n" 
    (if estimated_1_1mb <= 42.0 then "✅ PASS" else "❌ FAIL");
  
  avg_ms

let () =
  (* Test document *)
  let latex = {|\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Test}
Hello world $x^2 + y^2 = z^2$.
More content here...
\begin{equation}
\int_0^\infty e^{-x^2} dx = \frac{\sqrt{\pi}}{2}
\end{equation}
\end{document}|} in

  Printf.printf "🔍 TESTING ALL PRODUCTION LEXERS\n";
  Printf.printf "======================================\n";
  
  (* Test 1: L0 Track A Simple *)
  let time1 = test_lexer "L0_lexer_track_a_simple" 
    (fun input -> List.map (fun tok -> { Core.Lexer_v25.token = tok; loc = Data.Location.make 1 1 }) 
                    (Core.L0_lexer_track_a_simple.tokenize input)) latex in
  
  (* Test 2: L0 Track A Perfect *)  
  let time2 = test_lexer "L0_lexer_track_a_perfect"
    (fun input -> List.map (fun tok -> { Core.Lexer_v25.token = tok; loc = Data.Location.make 1 1 }) 
                    (Core.L0_lexer_track_a_perfect.tokenize input)) latex in
  
  (* Test 3: Standard Lexer V25 *)
  let time3 = test_lexer "Lexer_v25.tokenize"
    l0_wrapper latex in
  
  Printf.printf "\n📊 SUMMARY:\n";
  Printf.printf "===========\n";
  Printf.printf "Track A Simple:  %.3f ms\n" time1;
  Printf.printf "Track A Perfect: %.3f ms\n" time2;
  Printf.printf "Standard V25:    %.3f ms\n" time3;
  
  let best_time = min time1 (min time2 time3) in
  let best_name = 
    if best_time = time1 then "Track A Simple"
    else if best_time = time2 then "Track A Perfect" 
    else "Standard V25" in
  
  Printf.printf "\n🏆 FASTEST: %s (%.3f ms)\n" best_name best_time;
  
  (* Test on actual perf_smoke if time allows *)
  if best_time < 10.0 then begin
    Printf.printf "\n🚀 Testing winner on perf_smoke file...\n";
    let ic = open_in "corpus/perf_smoke/2506.19274v1/VBSurrogate_arxiv.tex" in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    let size = String.length content in
    Printf.printf "File size: %d bytes\n" size;
    
    let lexer_func = 
      if best_name = "Track A Simple" then (fun input -> List.map (fun tok -> { Core.Lexer_v25.token = tok; loc = Data.Location.make 1 1 }) 
                                               (Core.L0_lexer_track_a_simple.tokenize input))
      else if best_name = "Track A Perfect" then (fun input -> List.map (fun tok -> { Core.Lexer_v25.token = tok; loc = Data.Location.make 1 1 }) 
                                                   (Core.L0_lexer_track_a_perfect.tokenize input))
      else l0_wrapper in
    
    let start = Unix.gettimeofday () in
    let tokens = lexer_func content in  
    let stop = Unix.gettimeofday () in
    let elapsed_ms = (stop -. start) *. 1000.0 in
    
    Printf.printf "Real performance: %.3f ms for %d bytes\n" elapsed_ms size;
    Printf.printf "Tokens: %d\n" (List.length tokens);
    
    let scale_factor = (1.1 *. 1024.0 *. 1024.0) /. float_of_int size in
    let estimated_1_1mb = elapsed_ms *. scale_factor in
    
    Printf.printf "📊 FINAL RESULT: %.3f ms for 1.1MB\n" estimated_1_1mb;
    Printf.printf "vs 42ms SLA: %s\n" 
      (if estimated_1_1mb <= 42.0 then "✅ PASS" else "❌ FAIL");
    Printf.printf "vs 0.73ms claim: %.1fx %s\n" 
      (estimated_1_1mb /. 0.73)
      (if estimated_1_1mb <= 0.73 then "faster" else "slower")
  end