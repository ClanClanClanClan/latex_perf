(* OPTIMIZED LEXER - LaTeX Perfectionist v24-R3
   
   This is a hand-optimized version of the lexer that fixes the quadratic
   time complexity issues in the Coq-extracted code.
   
   Key optimizations:
   1. Use Buffer.t instead of string concatenation
   2. Use mutable references for accumulator instead of list append
   3. Process characters in-place without recursive string operations
   4. Eliminate O(n²) buffer operations
*)

(* Token types - same as extracted version *)
type token =
| TText of string
| TCommand of string  
| TMathShift
| TBeginGroup
| TEndGroup
| TParameter of int
| TSpace
| TNewline
| TVerbatim of string
| TAlignment
| TSuperscript
| TSubscript
| TComment of string
| TEOF

(* Optimized lexer state using mutable buffer *)
type lexer_state = {
  mutable buffer: Buffer.t;
  mutable math_mode: bool;
  mutable in_command: bool;
  mutable in_verbatim: bool;
  mutable verb_delim: char option;
  mutable in_comment: bool;
}

let create_state () = {
  buffer = Buffer.create 256;
  math_mode = false;
  in_command = false;
  in_verbatim = false;
  verb_delim = None;
  in_comment = false;
}

let clear_buffer st =
  Buffer.clear st.buffer

let add_to_buffer st c =
  Buffer.add_char st.buffer c

let get_buffer_contents st =
  Buffer.contents st.buffer

let flush_buffer st =
  if Buffer.length st.buffer = 0 then
    []
  else
    let content = get_buffer_contents st in
    clear_buffer st;
    [TText content]

let is_letter c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let is_digit c =
  c >= '0' && c <= '9'

(* Optimized character processing - no recursion, direct array access *)
let lex_char st c tokens_acc =
  if st.in_comment then
    match c with
    | '\n' | '\r' ->
      (* End comment mode *)
      let comment_content = if Buffer.length st.buffer > 0 then get_buffer_contents st else "" in
      clear_buffer st;
      st.in_comment <- false;
      let comment_token = if comment_content <> "" then [TComment comment_content] else [] in
      List.rev_append (TNewline :: comment_token) tokens_acc
    | _ ->
      (* Accumulate comment content *)
      add_to_buffer st c;
      tokens_acc
  else if st.in_command then
    if is_letter c then (
      (* Continue command *)
      add_to_buffer st c;
      tokens_acc
    ) else (
      (* End command *)
      let cmd_content = get_buffer_contents st in
      clear_buffer st;
      st.in_command <- false;
      let cmd_token = TCommand ("\\" ^ cmd_content) in
      
      (* Process the character that ended the command *)
      match c with
      | '$' -> List.rev_append [cmd_token; TMathShift] tokens_acc
      | '{' -> List.rev_append [cmd_token; TBeginGroup] tokens_acc  
      | '}' -> List.rev_append [cmd_token; TEndGroup] tokens_acc
      | ' ' | '\t' -> List.rev_append [cmd_token; TSpace] tokens_acc
      | '\n' | '\r' -> List.rev_append [cmd_token; TNewline] tokens_acc
      | '^' -> List.rev_append [cmd_token; TSuperscript] tokens_acc
      | '_' -> List.rev_append [cmd_token; TSubscript] tokens_acc
      | '&' -> List.rev_append [cmd_token; TAlignment] tokens_acc
      | _ -> 
        add_to_buffer st c;
        cmd_token :: tokens_acc
    )
  else
    match c with
    | '%' when not st.in_verbatim ->
      (* Start comment mode *)
      let flush_tokens = if Buffer.length st.buffer > 0 then flush_buffer st else [] in
      st.in_comment <- true;
      List.rev_append flush_tokens tokens_acc
      
    | '\\' ->
      (* Start command *)
      let flush_tokens = if Buffer.length st.buffer > 0 then flush_buffer st else [] in
      st.in_command <- true;
      List.rev_append flush_tokens tokens_acc
      
    | '$' -> TMathShift :: tokens_acc
    | '{' -> TBeginGroup :: tokens_acc
    | '}' -> TEndGroup :: tokens_acc
    | ' ' | '\t' -> TSpace :: tokens_acc
    | '\n' | '\r' -> TNewline :: tokens_acc
    | '^' -> TSuperscript :: tokens_acc
    | '_' -> TSubscript :: tokens_acc
    | '&' -> TAlignment :: tokens_acc
    | _ ->
      (* Regular character - add to buffer *)
      add_to_buffer st c;
      tokens_acc

(* Optimized tokenization - O(n) instead of O(n²) *)
let latex_tokenize_optimized input =
  let st = create_state () in
  let tokens_acc = ref [] in
  
  (* Process each character in linear time *)
  for i = 0 to String.length input - 1 do
    let c = input.[i] in
    tokens_acc := lex_char st c !tokens_acc
  done;
  
  (* Flush any remaining buffer content *)
  let final_tokens = 
    if Buffer.length st.buffer > 0 then
      if st.in_comment then
        let comment_content = get_buffer_contents st in
        [TComment comment_content; TEOF]
      else if st.in_command then
        let cmd_content = get_buffer_contents st in  
        [TCommand ("\\" ^ cmd_content); TEOF]
      else
        let text_content = get_buffer_contents st in
        [TText text_content; TEOF]
    else
      [TEOF]
  in
  
  List.rev (List.rev_append final_tokens !tokens_acc)

(* Token output functions - same as original *)
let write_token_simple = function
  | TText s -> Printf.printf "TEXT:%s\n" s
  | TCommand s -> Printf.printf "COMMAND:%s\n" s
  | TMathShift -> Printf.printf "MATHSHIFT\n"
  | TBeginGroup -> Printf.printf "BEGINGROUP\n"
  | TEndGroup -> Printf.printf "ENDGROUP\n"
  | TSpace -> Printf.printf "SPACE\n"
  | TNewline -> Printf.printf "NEWLINE\n"
  | TAlignment -> Printf.printf "ALIGNMENT\n"
  | TSuperscript -> Printf.printf "SUPERSCRIPT\n"
  | TSubscript -> Printf.printf "SUBSCRIPT\n"
  | TComment s -> Printf.printf "COMMENT:%s\n" s
  | TVerbatim s -> Printf.printf "VERBATIM:%s\n" s
  | TEOF -> Printf.printf "EOF\n"
  | TParameter n -> Printf.printf "PARAMETER:%d\n" n

let write_tokens tokens =
  List.iter write_token_simple tokens

(* Main entry point *)
let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <input_file>\n" Sys.argv.(0);
    exit 1
  end;
  
  let input_file = Sys.argv.(1) in
  try
    let ic = open_in input_file in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    let tokens = latex_tokenize_optimized content in
    write_tokens tokens
  with
  | Sys_error msg -> 
    Printf.eprintf "Error: %s\n" msg;
    exit 1
  | exn ->
    Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string exn);
    exit 1