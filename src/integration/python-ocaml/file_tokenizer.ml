
(* Reliable file-based tokenizer *)
#use "lexer_extracted.ml";;

let bool_to_int = function True -> 1 | False -> 0;;

let rec coq_string_to_ocaml = function
  | EmptyString -> ""
  | String (c, rest) -> 
    let Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = c in
    let code = (bool_to_int b0) + 2 * (bool_to_int b1) + 
               4 * (bool_to_int b2) + 8 * (bool_to_int b3) +
               16 * (bool_to_int b4) + 32 * (bool_to_int b5) +
               64 * (bool_to_int b6) + 128 * (bool_to_int b7) in
    String.make 1 (Char.chr code) ^ coq_string_to_ocaml rest;;

let int_to_bool = function 0 -> False | _ -> True;;

let rec ocaml_string_to_coq s =
  if String.length s = 0 then EmptyString
  else
    let c = s.[0] in
    let code = Char.code c in
    let b0 = int_to_bool (code land 1) in
    let b1 = int_to_bool (code land 2) in
    let b2 = int_to_bool (code land 4) in
    let b3 = int_to_bool (code land 8) in
    let b4 = int_to_bool (code land 16) in
    let b5 = int_to_bool (code land 32) in
    let b6 = int_to_bool (code land 64) in
    let b7 = int_to_bool (code land 128) in
    let ascii_char = Ascii (b0,b1,b2,b3,b4,b5,b6,b7) in
    String (ascii_char, ocaml_string_to_coq (String.sub s 1 (String.length s - 1)));;

let write_token_simple = function
  | TText s -> Printf.printf "TEXT:%s\n" (coq_string_to_ocaml s)
  | TCommand s -> Printf.printf "COMMAND:%s\n" (coq_string_to_ocaml s)
  | TMathShift -> Printf.printf "MATHSHIFT\n"
  | TBeginGroup -> Printf.printf "BEGINGROUP\n"
  | TEndGroup -> Printf.printf "ENDGROUP\n"
  | TSpace -> Printf.printf "SPACE\n"
  | TNewline -> Printf.printf "NEWLINE\n"
  | TAlignment -> Printf.printf "ALIGNMENT\n"
  | TSuperscript -> Printf.printf "SUPERSCRIPT\n"
  | TSubscript -> Printf.printf "SUBSCRIPT\n"
  | TComment s -> Printf.printf "COMMENT:%s\n" (coq_string_to_ocaml s)
  | TVerbatim s -> Printf.printf "VERBATIM:%s\n" (coq_string_to_ocaml s)
  | TEOF -> Printf.printf "EOF\n"
  | TParameter n -> Printf.printf "PARAMETER:0\n";;

let rec write_tokens = function
  | Nil -> ()
  | Cons (token, rest) -> 
    write_token_simple token;
    write_tokens rest;;

(* Read input file and tokenize *)
let () =
  let input_file = Sys.argv.(1) in
  let ic = open_in input_file in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  
  let coq_input = ocaml_string_to_coq content in
  let tokens = latex_tokenize coq_input in
  write_tokens tokens;;
