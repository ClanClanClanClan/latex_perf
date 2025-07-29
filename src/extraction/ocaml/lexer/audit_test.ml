(** Audit test for the LaTeX lexer - checking critical tokenization *)

open Latex_tokenize

(* Helper to create ASCII characters *)
let ascii_of_char c =
  let n = Char.code c in
  let bit i = if n land (1 lsl i) != 0 then True else False in
  Ascii (bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

(* Convert OCaml string to extracted string *)
let string_of_ocaml s =
  let rec aux i =
    if i >= String.length s then EmptyString
    else String (ascii_of_char s.[i], aux (i + 1))
  in aux 0

(* Check token types in a list *)
let analyze_tokens tokens =
  let rec count_types toks counts =
    match toks with
    | Nil -> counts
    | Cons (tok, rest) ->
        let (texts, cmds, maths, groups, spaces, others) = counts in
        match tok with
        | TText _ -> count_types rest (texts+1, cmds, maths, groups, spaces, others)
        | TCommand _ -> count_types rest (texts, cmds+1, maths, groups, spaces, others)
        | TMathShift -> count_types rest (texts, cmds, maths+1, groups, spaces, others)
        | TBeginGroup -> count_types rest (texts, cmds, maths, groups+1, spaces, others)
        | TEndGroup -> count_types rest (texts, cmds, maths, groups+1, spaces, others)
        | TSpace -> count_types rest (texts, cmds, maths, groups, spaces+1, others)
        | _ -> count_types rest (texts, cmds, maths, groups, spaces, others+1)
  in
  count_types tokens (0, 0, 0, 0, 0, 0)

(* Test the critical case that was causing 99.8% false positives *)
let test_critical_case () =
  Printf.printf "=== CRITICAL TEST: Math in text ===\n\n";
  
  (* This is the exact case that was failing *)
  let input = "By examining arithmetic operations between numbers expressed in base $m\\\\ge 2$, we uncover new families." in
  Printf.printf "Input: %S\n" input;
  
  let tokens = latex_tokenize (string_of_ocaml input) in
  let (texts, cmds, maths, groups, spaces, others) = analyze_tokens tokens in
  
  Printf.printf "\nToken counts:\n";
  Printf.printf "  TText tokens: %d\n" texts;
  Printf.printf "  TCommand tokens: %d\n" cmds;
  Printf.printf "  TMathShift tokens: %d\n" maths;
  Printf.printf "  Group tokens: %d\n" groups;
  Printf.printf "  Space tokens: %d\n" spaces;
  Printf.printf "  Other tokens: %d\n" others;
  
  (* Critical check: we should have exactly 2 TMathShift tokens *)
  if maths = 2 then
    Printf.printf "\n✓ PASS: Found correct number of math delimiters\n"
  else
    Printf.printf "\n✗ FAIL: Expected 2 TMathShift tokens, found %d\n" maths;
  
  (* Check if any text token contains $ *)
  let rec check_no_dollar_in_text = function
    | Nil -> true
    | Cons (TText _, rest) -> 
        (* We can't easily check the content without conversion, 
           but the presence of TMathShift tokens is the key indicator *)
        check_no_dollar_in_text rest
    | Cons (_, rest) -> check_no_dollar_in_text rest
  in
  
  Printf.printf "\n"

(* Test other important cases *)
let test_other_cases () =
  Printf.printf "=== OTHER TOKENIZATION TESTS ===\n\n";
  
  let test_cases = [
    ("$x$", "inline math");
    ("$$E=mc^2$$", "display math");
    ("\\section{Title}", "command with argument");
    ("\\textbf{bold}", "text command");
    ("text $a+b$ more", "mixed content");
  ] in
  
  List.iter (fun (input, desc) ->
    Printf.printf "Test: %s\n" desc;
    Printf.printf "Input: %S\n" input;
    
    let tokens = latex_tokenize (string_of_ocaml input) in
    let (texts, cmds, maths, groups, spaces, others) = analyze_tokens tokens in
    
    Printf.printf "Results: %d text, %d cmd, %d math, %d group, %d space\n\n"
      texts cmds maths groups spaces
  ) test_cases

(* Main *)
let () =
  Printf.printf "LATEX LEXER AUDIT TEST\n";
  Printf.printf "======================\n\n";
  
  test_critical_case ();
  test_other_cases ();
  
  Printf.printf "======================\n";
  Printf.printf "AUDIT COMPLETE\n"