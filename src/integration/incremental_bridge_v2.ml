(* OCaml Bridge for Incremental Lexing V2 *)
(* This connects the extracted Coq incremental lexer to Python *)

#use "incremental_lexer_extracted.ml";;

(* Helper to convert between int representation *)
let rec nat_to_int = function 
  | O -> 0 
  | S n -> 1 + nat_to_int n

(* JSON serialization for checkpoints *)
let checkpoint_to_json cp =
  Printf.sprintf 
    "{\"position\": %d, \"line\": %d, \"column\": %d, \"token_count\": %d}"
    cp.cp_position
    cp.cp_line
    cp.cp_column
    (List.length cp.cp_tokens)

(* Convert token to JSON *)
let token_to_json = function
  | TText s -> Printf.sprintf "{\"type\": \"TText\", \"content\": \"%s\"}" (String.escaped s)
  | TCommand s -> Printf.sprintf "{\"type\": \"TCommand\", \"content\": \"%s\"}" (String.escaped s)
  | TMathShift -> "{\"type\": \"TMathShift\", \"content\": \"\"}"
  | TBeginGroup -> "{\"type\": \"TBeginGroup\", \"content\": \"\"}"
  | TEndGroup -> "{\"type\": \"TEndGroup\", \"content\": \"\"}"
  | TParameter -> "{\"type\": \"TParameter\", \"content\": \"\"}"
  | TSpace -> "{\"type\": \"TSpace\", \"content\": \"\"}"
  | TNewline -> "{\"type\": \"TNewline\", \"content\": \"\"}"
  | TAlignment -> "{\"type\": \"TAlignment\", \"content\": \"\"}"
  | TSuperscript -> "{\"type\": \"TSuperscript\", \"content\": \"\"}"
  | TSubscript -> "{\"type\": \"TSubscript\", \"content\": \"\"}"
  | TComment s -> Printf.sprintf "{\"type\": \"TComment\", \"content\": \"%s\"}" (String.escaped s)
  | TEOF -> "{\"type\": \"TEOF\", \"content\": \"\"}"

(* Helper to read all stdin *)
let read_all_stdin () =
  let buffer = Buffer.create 1024 in
  try
    while true do
      let line = read_line () in
      Buffer.add_string buffer line;
      Buffer.add_char buffer '\n'
    done;
    Buffer.contents buffer
  with End_of_file ->
    let contents = Buffer.contents buffer in
    (* Remove trailing newline if present *)
    let len = String.length contents in
    if len > 0 && contents.[len-1] = '\n' then
      String.sub contents 0 (len-1)
    else
      contents

(* Initial document lexing with checkpoints *)
let lex_initial_with_checkpoints input_string =
  let (tokens, checkpoints) = lex_document_with_checkpoints input_string in
  
  (* Convert tokens to JSON *)
  let tokens_json = List.map token_to_json tokens in
  let tokens_json_str = "[" ^ String.concat "," tokens_json ^ "]" in
  
  (* Convert checkpoints to JSON *)
  let checkpoints_json = List.map checkpoint_to_json checkpoints in
  let checkpoints_json_str = "[" ^ String.concat "," checkpoints_json ^ "]" in
  
  (* Return combined result *)
  Printf.printf "{\"tokens\": %s, \"checkpoints\": %s}\n" tokens_json_str checkpoints_json_str

(* Simple tokenization without checkpoints *)
let lex_simple input_string =
  let tokens = lex_from_string input_string in
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
      (* For now, just re-lex the input *)
      let input = read_all_stdin () in
      lex_simple input
    | _ ->
      Printf.fprintf stderr "Usage: %s [initial|incremental]\n" Sys.argv.(0);
      exit 1
  else
    (* Default: read input and tokenize *)
    let input = read_all_stdin () in
    lex_simple input