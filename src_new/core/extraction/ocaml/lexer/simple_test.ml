(** Simple test for the LaTeX lexer *)

open Latex_tokenize

(* Create a simple string *)
let test_string = 
  String (Ascii (False, False, False, False, False, True, True, False),  (* H *)
  String (Ascii (True, False, True, False, False, True, True, False),   (* e *)
  String (Ascii (False, False, True, True, False, True, True, False),   (* l *)
  String (Ascii (False, False, True, True, False, True, True, False),   (* l *)
  String (Ascii (True, True, True, True, False, True, True, False),     (* o *)
  EmptyString)))))

let () =
  Printf.printf "Testing lexer with 'Hello'...\n";
  let tokens = latex_tokenize test_string in
  Printf.printf "Tokenization complete.\n";
  
  (* Count tokens *)
  let rec count_tokens = function
    | Nil -> 0
    | Cons (_, rest) -> 1 + count_tokens rest
  in
  
  Printf.printf "Number of tokens: %d\n" (count_tokens tokens);
  
  (* Check token types *)
  let rec print_token_types = function
    | Nil -> ()
    | Cons (tok, rest) ->
        let type_str = match tok with
          | TText _ -> "TText"
          | TCommand _ -> "TCommand"
          | TMathShift -> "TMathShift"
          | TBeginGroup -> "TBeginGroup"
          | TEndGroup -> "TEndGroup"
          | TParameter _ -> "TParameter"
          | TSpace -> "TSpace"
          | TNewline -> "TNewline"
          | TVerbatim _ -> "TVerbatim"
        in
        Printf.printf "  Token type: %s\n" type_str;
        print_token_types rest
  in
  
  print_token_types tokens