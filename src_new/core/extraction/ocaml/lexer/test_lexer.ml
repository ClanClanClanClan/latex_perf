(** Test suite for the extracted LaTeX lexer *)

open Latex_tokenize

(* Helper to convert token to string for display *)
let token_to_string = function
  | TText s -> Printf.sprintf "TText(%S)" s
  | TCommand s -> Printf.sprintf "TCommand(%S)" s
  | TMathShift -> "TMathShift"
  | TBeginGroup -> "TBeginGroup"
  | TEndGroup -> "TEndGroup"
  | TParameter n -> Printf.sprintf "TParameter(%d)" n
  | TSpace -> "TSpace"
  | TNewline -> "TNewline"
  | TVerbatim s -> Printf.sprintf "TVerbatim(%S)" s

(* Print token list *)
let print_tokens tokens =
  List.iter (fun t -> Printf.printf "%s\n" (token_to_string t)) tokens

(* Test cases *)
let test_cases = [
  (* Basic text *)
  ("Hello world", 
   [TText "Hello"; TSpace; TText "world"]);
  
  (* Simple math *)
  ("$x + y$",
   [TMathShift; TText "x"; TSpace; TText "+"; TSpace; TText "y"; TMathShift]);
  
  (* Command *)
  ("\\section{Introduction}",
   [TCommand "section"; TBeginGroup; TText "Introduction"; TEndGroup]);
  
  (* Mixed content *)
  ("The equation $E = mc^2$ is famous.",
   [TText "The"; TSpace; TText "equation"; TSpace; 
    TMathShift; TText "E"; TSpace; TText "="; TSpace; TText "mc^2"; TMathShift;
    TSpace; TText "is"; TSpace; TText "famous."]);
  
  (* Nested groups *)
  ("\\textbf{\\emph{nested}}",
   [TCommand "textbf"; TBeginGroup; 
    TCommand "emph"; TBeginGroup; TText "nested"; TEndGroup;
    TEndGroup]);
]

(* Run tests *)
let run_tests () =
  Printf.printf "Running LaTeX lexer tests...\n\n";
  
  List.iteri (fun i (input, expected) ->
    Printf.printf "Test %d: %S\n" (i + 1) input;
    let result = latex_tokenize input in
    
    (* Compare results *)
    if result = expected then
      Printf.printf "✓ PASSED\n"
    else begin
      Printf.printf "✗ FAILED\n";
      Printf.printf "Expected:\n";
      print_tokens expected;
      Printf.printf "Got:\n";
      print_tokens result
    end;
    Printf.printf "\n"
  ) test_cases

(* Performance test *)
let perf_test () =
  Printf.printf "Performance test...\n";
  
  (* Generate a large document *)
  let large_doc = String.concat " " (List.init 1000 (fun i ->
    Printf.sprintf "This is paragraph %d with math $x_%d = %d$ and command \\ref{eq:%d}." i i i i
  )) in
  
  let start_time = Sys.time () in
  let tokens = latex_tokenize large_doc in
  let end_time = Sys.time () in
  
  Printf.printf "Tokenized %d characters into %d tokens in %.3f seconds\n"
    (String.length large_doc)
    (List.length tokens)
    (end_time -. start_time);
  
  Printf.printf "Speed: %.0f chars/sec\n"
    (float_of_int (String.length large_doc) /. (end_time -. start_time))

(* Main *)
let () =
  run_tests ();
  Printf.printf "\n";
  perf_test ()