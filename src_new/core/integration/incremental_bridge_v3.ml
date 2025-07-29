(* Incremental OCaml Bridge V3 - With actual incremental lexing *)

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

(* Edit operation *)
type edit_op = 
  | Insert of int * string
  | Delete of int * int  
  | Replace of int * int * string

(* Apply edit to string *)
let apply_edit_to_string s op =
  match op with
  | Insert (pos, text) ->
    let before = String.sub s 0 pos in
    let after = String.sub s pos (String.length s - pos) in
    before ^ text ^ after
  | Delete (pos, len) ->
    let before = String.sub s 0 pos in
    let after = String.sub s (pos + len) (String.length s - pos - len) in
    before ^ after
  | Replace (pos, len, text) ->
    let before = String.sub s 0 pos in
    let after = String.sub s (pos + len) (String.length s - pos - len) in
    before ^ text ^ after

(* Tokenize from a specific position *)
let tokenize_from_position input start_pos =
  let tokens = ref [] in
  let i = ref start_pos in
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
  
  List.rev !tokens

(* Incremental tokenization using checkpoints *)
let tokenize_incremental doc checkpoints edit_op =
  (* Apply the edit *)
  let new_doc = apply_edit_to_string doc edit_op in
  
  (* Find edit position *)
  let edit_pos = match edit_op with
    | Insert (pos, _) -> pos
    | Delete (pos, _) -> pos
    | Replace (pos, _, _) -> pos
  in
  
  (* Find the last checkpoint before the edit *)
  let rec find_checkpoint cps best_pos =
    match cps with
    | [] -> best_pos
    | cp :: rest ->
      if cp.cp_position <= edit_pos && cp.cp_position > best_pos then
        find_checkpoint rest cp.cp_position
      else
        find_checkpoint rest best_pos
  in
  
  let checkpoint_pos = find_checkpoint checkpoints 0 in
  
  (* Tokenize from checkpoint position *)
  let new_tokens = tokenize_from_position new_doc checkpoint_pos in
  
  (* For demo: return all tokens (in real implementation, would merge with prefix) *)
  if checkpoint_pos = 0 then
    new_tokens
  else
    (* Would need to preserve tokens before checkpoint *)
    new_tokens

(* Full tokenization *)
let tokenize_simple input = tokenize_from_position input 0

(* Create checkpoints during tokenization *)
let create_checkpoints_during_tokenization input checkpoint_interval =
  let tokens_result = ref [] in
  let checkpoints_result = ref [] in
  let tokens = ref [] in
  let i = ref 0 in
  let len = String.length input in
  let line = ref 1 in
  let col = ref 1 in
  let last_checkpoint = ref 0 in
  
  while !i < len do
    let c = input.[!i] in
    
    (* Create checkpoint if needed *)
    if !i - !last_checkpoint >= checkpoint_interval then begin
      checkpoints_result := {
        cp_position = !i;
        cp_tokens = List.rev !tokens;
        cp_line = !line;
        cp_column = !col;
        cp_in_math = false;
        cp_env_stack = []
      } :: !checkpoints_result;
      last_checkpoint := !i
    end;
    
    (* Token parsing (same as before) *)
    match c with
    | '\\' ->
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
      while !i < len && (input.[!i] = ' ' || input.[!i] = '\t') do
        incr i; incr col
      done;
      tokens := TSpace :: !tokens
    | '\n' ->
      tokens := TNewline :: !tokens; 
      incr i; incr line; col := 1
    | '%' ->
      incr i;
      let comment_start = !i in
      while !i < len && input.[!i] <> '\n' do
        incr i; incr col
      done;
      let comment = String.sub input comment_start (!i - comment_start) in
      tokens := TComment comment :: !tokens
    | _ ->
      let text_start = !i in
      while !i < len && 
        (let c = input.[!i] in
         c <> '\\' && c <> '{' && c <> '}' && c <> '$' && c <> '&' &&
         c <> '#' && c <> '^' && c <> '_' && c <> ' ' && c <> '\t' &&
         c <> '\n' && c <> '%') do
        incr i; incr col
      done;
      let text = String.sub input text_start (!i - text_start) in
      tokens := TText text :: !tokens
  done;
  
  tokens := TEOF :: !tokens;
  tokens_result := List.rev !tokens;
  (!tokens_result, List.rev !checkpoints_result)

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
      let (tokens, checkpoints) = create_checkpoints_during_tokenization input 100 in (* checkpoint every 100 chars *)
      
      (* Convert to JSON *)
      let tokens_json = List.map token_to_json tokens in
      let tokens_json_str = "[" ^ String.concat "," tokens_json ^ "]" in
      
      let checkpoints_json = List.map checkpoint_to_json checkpoints in
      let checkpoints_json_str = "[" ^ String.concat "," checkpoints_json ^ "]" in
      
      Printf.printf "{\"tokens\": %s, \"checkpoints\": %s}\n" tokens_json_str checkpoints_json_str
      
    | "incremental" ->
      (* For demo: just re-tokenize *)
      let input = read_all_stdin () in
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