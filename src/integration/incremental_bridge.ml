(* OCaml Bridge for Incremental Lexing *)
(* This connects the Coq incremental lexer to Python *)

#use "../../incremental_lexer_extracted.ml";;
#use "../../src/extraction/ocaml/lexer/lexer_extracted.ml";;

(* JSON serialization for checkpoints *)
let checkpoint_to_json cp =
  Printf.sprintf 
    "{\"position\": %d, \"line\": %d, \"column\": %d, \"token_count\": %d}"
    (match cp.cp_position with O -> 0 | S n -> 1 + nat_to_int n)
    (match cp.cp_line with O -> 0 | S n -> 1 + nat_to_int n)
    (match cp.cp_column with O -> 0 | S n -> 1 + nat_to_int n)
    (list_length cp.cp_tokens)

(* Convert token to JSON *)
let token_to_json = function
  | TText s -> Printf.sprintf "{\"type\": \"TText\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TCommand s -> Printf.sprintf "{\"type\": \"TCommand\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TMathShift -> "{\"type\": \"TMathShift\"}"
  | TBeginGroup -> "{\"type\": \"TBeginGroup\"}"
  | TEndGroup -> "{\"type\": \"TEndGroup\"}"
  | TParameter -> "{\"type\": \"TParameter\"}"
  | TSpace -> "{\"type\": \"TSpace\"}"
  | TNewline -> "{\"type\": \"TNewline\"}"
  | TAlignment -> "{\"type\": \"TAlignment\"}"
  | TSuperscript -> "{\"type\": \"TSuperscript\"}"
  | TSubscript -> "{\"type\": \"TSubscript\"}"
  | TComment s -> Printf.sprintf "{\"type\": \"TComment\", \"content\": \"%s\"}" (String.escaped (coq_string_to_ocaml s))
  | TEOF -> "{\"type\": \"TEOF\"}"

(* Convert Coq bool to OCaml bool *)
let bool_to_ocaml = function True -> true | False -> false

(* Convert OCaml bool to Coq bool *)
let bool_of_ocaml = function true -> True | false -> False

(* Convert Coq nat to OCaml int *)
let rec nat_to_int = function O -> 0 | S n -> 1 + nat_to_int n

(* Convert OCaml int to Coq nat *)
let rec nat_of_int n = if n <= 0 then O else S (nat_of_int (n - 1))

(* Convert between string representations *)
let rec coq_string_to_ocaml = function
  | EmptyString -> ""
  | String (c, rest) -> 
    let Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = c in
    let code = (if bool_to_ocaml b0 then 1 else 0) + 
               (if bool_to_ocaml b1 then 2 else 0) + 
               (if bool_to_ocaml b2 then 4 else 0) + 
               (if bool_to_ocaml b3 then 8 else 0) +
               (if bool_to_ocaml b4 then 16 else 0) + 
               (if bool_to_ocaml b5 then 32 else 0) +
               (if bool_to_ocaml b6 then 64 else 0) + 
               (if bool_to_ocaml b7 then 128 else 0) in
    String.make 1 (Char.chr code) ^ coq_string_to_ocaml rest

let rec ocaml_string_to_coq s =
  if String.length s = 0 then EmptyString
  else
    let c = s.[0] in
    let code = Char.code c in
    let b0 = bool_of_ocaml (code land 1 <> 0) in
    let b1 = bool_of_ocaml (code land 2 <> 0) in
    let b2 = bool_of_ocaml (code land 4 <> 0) in
    let b3 = bool_of_ocaml (code land 8 <> 0) in
    let b4 = bool_of_ocaml (code land 16 <> 0) in
    let b5 = bool_of_ocaml (code land 32 <> 0) in
    let b6 = bool_of_ocaml (code land 64 <> 0) in
    let b7 = bool_of_ocaml (code land 128 <> 0) in
    let ascii_char = Ascii (b0,b1,b2,b3,b4,b5,b6,b7) in
    String (ascii_char, ocaml_string_to_coq (String.sub s 1 (String.length s - 1)))

(* Initial document lexing with checkpoints *)
let lex_initial_with_checkpoints input_string =
  let coq_input = ocaml_string_to_coq input_string in
  let (tokens, checkpoints) = lex_document_with_checkpoints coq_input in
  
  (* Convert tokens to JSON *)
  let tokens_json = List.map token_to_json tokens in
  let tokens_json_str = "[" ^ String.concat "," tokens_json ^ "]" in
  
  (* Convert checkpoints to JSON *)
  let checkpoints_json = List.map checkpoint_to_json checkpoints in
  let checkpoints_json_str = "[" ^ String.concat "," checkpoints_json ^ "]" in
  
  (* Return combined result *)
  Printf.printf "{\"tokens\": %s, \"checkpoints\": %s}\n" tokens_json_str checkpoints_json_str

(* Incremental lexing from edit *)
let lex_incremental_edit doc_string checkpoints_json edit_json =
  (* For now, just do full re-lex as placeholder *)
  let coq_doc = ocaml_string_to_coq doc_string in
  let tokens = latex_tokenize coq_doc in
  
  (* Convert to JSON *)
  let tokens_json = List.map token_to_json tokens in
  Printf.printf "[%s]\n" (String.concat "," tokens_json)

(* Main entry point *)
let () =
  if Array.length Sys.argv > 1 then
    match Sys.argv.(1) with
    | "initial" ->
      let input = read_all_stdin () in
      lex_initial_with_checkpoints input
    | "incremental" ->
      (* Read document, checkpoints, and edit from stdin *)
      let input = read_all_stdin () in
      (* For now, just re-lex the input *)
      let coq_input = ocaml_string_to_coq input in
      let tokens = latex_tokenize coq_input in
      let tokens_json = List.map token_to_json tokens in
      Printf.printf "[%s]\n" (String.concat "," tokens_json)
    | _ ->
      Printf.fprintf stderr "Usage: %s [initial|incremental]\n" Sys.argv.(0);
      exit 1
  else
    (* Default: read input and tokenize *)
    let input = read_all_stdin () in
    let coq_input = ocaml_string_to_coq input in
    let tokens = latex_tokenize coq_input in
    let tokens_json = List.map token_to_json tokens in
    Printf.printf "[%s]\n" (String.concat "," tokens_json)

(* Helper to read all stdin *)
and read_all_stdin () =
  let buffer = Buffer.create 1024 in
  try
    while true do
      let line = read_line () in
      Buffer.add_string buffer line;
      Buffer.add_char buffer '\n'
    done;
    Buffer.contents buffer
  with End_of_file ->
    Buffer.contents buffer