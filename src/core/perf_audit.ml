open Types
open Lexer_verified

let measure_performance () =
  let test_input = "\\documentclass{article}\\begin{document}Hello \\LaTeX{} world!\\end{document}" in
  let iterations = 100 in
  let times = Array.make iterations 0. in
  
  Printf.printf "Testing %d iterations of %d char input...\n" iterations (String.length test_input);
  
  for i = 0 to iterations - 1 do
    let start = Unix.gettimeofday () in
    let _ = lex_string test_input in
    let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
    times.(i) <- elapsed
  done;
  
  let total = Array.fold_left (+.) 0. times in
  let avg = total /. float iterations in
  let min_time = Array.fold_left min max_float times in
  let max_time = Array.fold_left max 0. times in
  
  Printf.printf "Average: %.0fμs (%.2fms)\n" avg (avg /. 1000.);
  Printf.printf "Min: %.0fμs  Max: %.0fμs\n" min_time max_time;
  Printf.printf "Claimed: 4430μs (4.43ms)\n";
  Printf.printf "Reality: %.1fx %s than claimed\n" 
    (if avg < 4430. then 4430. /. avg else avg /. 4430.)
    (if avg < 4430. then "FASTER" else "SLOWER")

let () = measure_performance ()