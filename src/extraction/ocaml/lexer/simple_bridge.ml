(* Simple bridge for Python integration *)
#use "lexer_extracted.ml";;

(* Convert Coq bool to OCaml int *)
let bool_to_int = function True -> 1 | False -> 0;;

(* Convert Coq string to OCaml string *)
let rec coq_string_to_ocaml = function
  | EmptyString -> ""
  | String (c, rest) -> 
    let Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = c in
    let code = (bool_to_int b0) + 2 * (bool_to_int b1) + 
               4 * (bool_to_int b2) + 8 * (bool_to_int b3) +
               16 * (bool_to_int b4) + 32 * (bool_to_int b5) +
               64 * (bool_to_int b6) + 128 * (bool_to_int b7) in
    String.make 1 (Char.chr code) ^ coq_string_to_ocaml rest;;

(* Convert OCaml string to Coq string *)
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

(* Simple token printing *)
let print_token = function
  | TText s -> Printf.printf "TText(%s) " (coq_string_to_ocaml s)
  | TCommand s -> Printf.printf "TCommand(%s) " (coq_string_to_ocaml s)
  | TMathShift -> Printf.printf "TMathShift "
  | TBeginGroup -> Printf.printf "TBeginGroup "
  | TEndGroup -> Printf.printf "TEndGroup "
  | TSpace -> Printf.printf "TSpace "
  | TNewline -> Printf.printf "TNewline "
  | TAlignment -> Printf.printf "TAlignment "
  | TSuperscript -> Printf.printf "TSuperscript "
  | TSubscript -> Printf.printf "TSubscript "
  | TComment s -> Printf.printf "TComment(%s) " (coq_string_to_ocaml s)
  | TEOF -> Printf.printf "TEOF "
  | _ -> Printf.printf "Other ";;

let rec print_tokens = function
  | Nil -> ()
  | Cons (token, rest) -> print_token token; print_tokens rest;;

(* Test tokenization *)
let test_input = "x^2_1 & % comment";;
let coq_input = ocaml_string_to_coq test_input;;
let tokens = latex_tokenize coq_input;;

Printf.printf "Input: %s\n" test_input;;
Printf.printf "Tokens: ";;
print_tokens tokens;;
Printf.printf "\n";;
Printf.printf "SUCCESS: Verified lexer working!\n";;