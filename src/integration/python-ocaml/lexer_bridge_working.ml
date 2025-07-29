(* Working Python-OCaml Bridge for LaTeX Lexer *)
#use "../../extraction/ocaml/lexer/lexer_extracted.ml";;

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

(* Convert token to JSON - matching actual extracted token type *)
let token_to_json = function
  | TText s -> Printf.sprintf "{\"type\": \"TText\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TCommand s -> Printf.sprintf "{\"type\": \"TCommand\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TMathShift -> "{\"type\": \"TMathShift\"}"
  | TBeginGroup -> "{\"type\": \"TBeginGroup\"}"
  | TEndGroup -> "{\"type\": \"TEndGroup\"}"
  | TParameter n -> 
    let rec nat_to_int = function O -> 0 | S n -> 1 + nat_to_int n in
    Printf.sprintf "{\"type\": \"TParameter\", \"num\": %d}" (nat_to_int n)
  | TSpace -> "{\"type\": \"TSpace\"}"
  | TNewline -> "{\"type\": \"TNewline\"}"
  | TVerbatim s -> Printf.sprintf "{\"type\": \"TVerbatim\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TAlignment -> "{\"type\": \"TAlignment\"}"
  | TSuperscript -> "{\"type\": \"TSuperscript\"}"
  | TSubscript -> "{\"type\": \"TSubscript\"}"
  | TComment s -> Printf.sprintf "{\"type\": \"TComment\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TEOF -> "{\"type\": \"TEOF\"}";;

(* Convert token list to JSON array *)
let rec tokens_to_json_list = function
  | Nil -> []
  | Cons (token, rest) -> (token_to_json token) :: (tokens_to_json_list rest);;

(* Main tokenization function *)
let tokenize_and_output input_string =
  let coq_input = ocaml_string_to_coq input_string in
  let tokens = latex_tokenize coq_input in
  let json_tokens = tokens_to_json_list tokens in
  Printf.printf "[%s]\n" (String.concat "," json_tokens);;

(* Simple test *)
let test_lexer () =
  Printf.printf "Testing lexer with 'hello world':\n";
  tokenize_and_output "hello world";
  Printf.printf "Testing lexer with '\\frac{1}{2}':\n";
  tokenize_and_output "\\frac{1}{2}";;

(* Interactive mode *)
let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "test" then
    test_lexer ()
  else
    let input = read_line () in
    tokenize_and_output input;;