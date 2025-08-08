(* Minimal performance test - no external dependencies *)

let time_function f x =
  let start = Sys.time () in
  let _ = f x in
  let stop = Sys.time () in
  (stop -. start) *. 1000.0  (* Convert to ms *)

let test_input = 
  let header = "\\documentclass{article}\n\\begin{document}\n" in
  let content = "This is a test document with some \\LaTeX{} commands.\n" ^
                "Math: $x^2 + y^2 = z^2$\n" ^
                "\\section{Test Section}\n" ^
                "More text here with \\textbf{bold} and \\emph{emphasis}.\n" in
  let padding = String.make 50000 'a' in
  let footer = "\n\\end{document}\n" in
  header ^ content ^ padding ^ footer

let () =
  Printf.printf "LaTeX Perfectionist v25 - Minimal Performance Test\\n";
  Printf.printf "================================================\\n\\n";
  Printf.printf "Input size: %d bytes\\n\\n" (String.length test_input);
  
  (* Warmup *)
  for _ = 1 to 5 do
    ignore (Core.L0_lexer.tokenize test_input)
  done;
  
  (* Measure *)
  let times = ref [] in
  for _ = 1 to 20 do
    let t = time_function Core.L0_lexer.tokenize test_input in
    times := t :: !times
  done;
  
  let sorted = List.sort compare !times in
  let median = List.nth sorted 10 in
  let best = List.hd sorted in
  let worst = List.nth sorted 19 in
  
  Printf.printf "Results (20 iterations):\\n";
  Printf.printf "  Best:   %.3f ms\\n" best;
  Printf.printf "  Median: %.3f ms\\n" median;
  Printf.printf "  Worst:  %.3f ms\\n" worst;
  Printf.printf "\\nImplementation: L0 lexer (ultra-optimized)\\n"