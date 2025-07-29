(* Simple test for enhanced lexer *)

#use "lexer_extracted.ml";;

let bool_to_int = function True -> 1 | False -> 0;;

let rec string_to_ocaml = function
  | EmptyString -> ""
  | String (c, rest) -> 
    let Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = c in
    let code = (bool_to_int b0) + 2 * (bool_to_int b1) + 
               4 * (bool_to_int b2) + 8 * (bool_to_int b3) +
               16 * (bool_to_int b4) + 32 * (bool_to_int b5) +
               64 * (bool_to_int b6) + 128 * (bool_to_int b7) in
    String.make 1 (Char.chr code) ^ string_to_ocaml rest;;

let int_to_bool = function 0 -> False | _ -> True;;

let rec ocaml_to_coq_string s =
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
    String (ascii_char, ocaml_to_coq_string (String.sub s 1 (String.length s - 1)));;

let test_text = "x^2_1 & % comment";;
let coq_input = ocaml_to_coq_string test_text;;
let result = latex_tokenize coq_input;;

print_endline ("Testing: " ^ test_text);;
print_endline "Tokens extracted successfully!";;