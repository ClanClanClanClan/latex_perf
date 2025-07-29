(* Manual OCaml Bridge for Incremental Lexing *)
(* This provides a simple incremental lexer interface without Coq extraction issues *)

(* Token type matching Coq definition *)
type latex_token =
  | TCommand of string
  | TBeginGroup
  | TEndGroup
  | TMathShift
  | TAlignment
  | TParameter
  | TSuperscript
  | TSubscript
  | TText of string
  | TSpace
  | TComment of string
  | TNewline
  | TEOF

(* Checkpoint state *)
type checkpoint_state = {
  cp_position : int;
  cp_tokens : latex_token list;
  cp_line : int;
  cp_column : int;
  cp_in_math : bool;
  cp_env_stack : string list
}

(* Simple tokenizer that matches Coq lexer behavior *)
let tokenize_simple input =
  let tokens = ref [] in
  let i = ref 0 in
  let len = String.length input in
  
  while !i < len do
    let c = input.[!i] in
    match c with
    | '\\' ->
      (* Command *)
      incr i;
      if !i < len then begin
        let cmd_start = !i in
        while !i < len && (let c = input.[!i] in (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) do
          incr i
        done;
        let cmd = String.sub input cmd_start (!i - cmd_start) in
        tokens := TCommand cmd :: !tokens
      end else
        tokens := TText "\\" :: !tokens
    | '{' -> tokens := TBeginGroup :: !tokens; incr i
    | '}' -> tokens := TEndGroup :: !tokens; incr i
    | '$' -> tokens := TMathShift :: !tokens; incr i
    | '&' -> tokens := TAlignment :: !tokens; incr i
    | '#' -> tokens := TParameter :: !tokens; incr i
    | '^' -> tokens := TSuperscript :: !tokens; incr i
    | '_' -> tokens := TSubscript :: !tokens; incr i
    | ' ' | '\t' ->
      (* Whitespace *)
      (* ws_start not used *)
      while !i < len && (input.[!i] = ' ' || input.[!i] = '\t') do
        incr i
      done;
      tokens := TSpace :: !tokens
    | '\n' ->
      tokens := TNewline :: !tokens; incr i
    | '%' ->
      (* Comment *)
      incr i;
      let comment_start = !i in
      while !i < len && input.[!i] <> '\n' do
        incr i
      done;
      let comment = String.sub input comment_start (!i - comment_start) in
      tokens := TComment comment :: !tokens
    | _ ->
      (* Text *)
      let text_start = !i in
      while !i < len && 
        (let c = input.[!i] in
         c <> '\\' && c <> '{' && c <> '}' && c <> '$' && c <> '&' &&
         c <> '#' && c <> '^' && c <> '_' && c <> ' ' && c <> '\t' &&
         c <> '\n' && c <> '%') do
        incr i
      done;
      let text = String.sub input text_start (!i - text_start) in
      tokens := TText text :: !tokens
  done;
  
  tokens := TEOF :: !tokens;
  List.rev !tokens

(* Create checkpoints at regular intervals *)
let create_checkpoints tokens =
  let checkpoints = ref [] in
  let current_pos = ref 0 in
  let current_line = ref 1 in
  let current_col = ref 1 in
  let token_count = ref 0 in
  
  List.iter (fun tok ->
    (* Create checkpoint every 10 tokens for demo *)
    if !token_count mod 10 = 0 then
      checkpoints := {
        cp_position = !current_pos;
        cp_tokens = [];  (* Would store actual tokens in real implementation *)
        cp_line = !current_line;
        cp_column = !current_col;
        cp_in_math = false;
        cp_env_stack = []
      } :: !checkpoints;
    
    (* Update position based on token *)
    (match tok with
    | TNewline -> incr current_line; current_col := 1
    | TText s | TCommand s | TComment s -> 
      current_pos := !current_pos + String.length s;
      current_col := !current_col + String.length s
    | _ -> incr current_pos; incr current_col);
    
    incr token_count
  ) tokens;
  
  List.rev !checkpoints

(* Token to JSON *)
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

(* Checkpoint to JSON *)
let checkpoint_to_json cp =
  Printf.sprintf 
    "{\"position\": %d, \"line\": %d, \"column\": %d, \"token_count\": %d}"
    cp.cp_position
    cp.cp_line
    cp.cp_column
    (List.length cp.cp_tokens)

(* Read all stdin *)
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
    let len = String.length contents in
    if len > 0 && contents.[len-1] = '\n' then
      String.sub contents 0 (len-1)
    else
      contents

(* Main entry point *)
let () =
  if Array.length Sys.argv > 1 then
    match Sys.argv.(1) with
    | "initial" ->
      let input = read_all_stdin () in
      let tokens = tokenize_simple input in
      let checkpoints = create_checkpoints tokens in
      
      (* Convert to JSON *)
      let tokens_json = List.map token_to_json tokens in
      let tokens_json_str = "[" ^ String.concat "," tokens_json ^ "]" in
      
      let checkpoints_json = List.map checkpoint_to_json checkpoints in
      let checkpoints_json_str = "[" ^ String.concat "," checkpoints_json ^ "]" in
      
      Printf.printf "{\"tokens\": %s, \"checkpoints\": %s}\n" tokens_json_str checkpoints_json_str
      
    | "incremental" ->
      (* Read JSON input with document, checkpoints, and edit *)
      let input = read_all_stdin () in
      (* For simplicity, just re-tokenize the full document *)
      (* A real implementation would parse the JSON and use checkpoints *)
      let tokens = tokenize_simple input in
      let tokens_json = List.map token_to_json tokens in
      Printf.printf "[%s]\n" (String.concat "," tokens_json)
      
    | _ ->
      Printf.fprintf stderr "Usage: %s [initial|incremental]\n" Sys.argv.(0);
      exit 1
  else
    (* Default: simple tokenization *)
    let input = read_all_stdin () in
    let tokens = tokenize_simple input in
    let tokens_json = List.map token_to_json tokens in
    Printf.printf "[%s]\n" (String.concat "," tokens_json)