(* Quick benchmark test - run manually compiled lexers *)

#load "unix.cma";;

let time_function f input =
  let start = Unix.gettimeofday () in
  let result = f input in
  let stop = Unix.gettimeofday () in
  let elapsed_ms = (stop -. start) *. 1000.0 in
  (result, elapsed_ms)

let load_file filename =
  try
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    Some content
  with
  | Sys_error msg -> 
    Printf.printf "Error loading %s: %s\n" filename msg;
    None

let () =
  Printf.printf "L0 Lexer Benchmark - Quick Test\n";
  Printf.printf "================================\n\n";
  
  (* Try to load test file *)
  match load_file "corpora/perf/perf_smoke_big.tex" with
  | None -> 
    Printf.printf "Could not load test file.\n";
    Printf.printf "Creating synthetic test (100KB)...\n";
    let test_content = String.concat "" [
      "\\documentclass{article}\n";
      "\\begin{document}\n";
      String.make 50000 'a';
      "\n\\section{Test} % comment\n";
      "$x^2 + y^2 = z^2$\n";
      String.make 50000 'b';
      "\n\\end{document}"
    ] in
    Printf.printf "Test size: %d bytes\n" (String.length test_content);
    
    (* Manual timing test *)
    Printf.printf "\nNote: Lexers need to be loaded separately.\n";
    Printf.printf "To test, compile and run:\n";
    Printf.printf "  make\n";
    Printf.printf "  ./_build/default/bench/run_lexer.exe\n"
    
  | Some content ->
    Printf.printf "Loaded perf_smoke_big.tex: %d bytes (%.2f MB)\n" 
      (String.length content)
      (float_of_int (String.length content) /. 1_048_576.0);
    Printf.printf "\nFile loaded. Run compiled benchmark to test.\n"