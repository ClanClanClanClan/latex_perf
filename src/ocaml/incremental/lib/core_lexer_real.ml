(* core_lexer_real.ml - Real high-performance lexer with deep state tracking *)

open Deep_state

external xxhash64 : string -> int64 = "caml_xxhash64"

(* Fallback implementations for SIMD functions *)
let classify_chars_simd input start len =
  let found_mask = ref 0 in
  let special_backslash = 1 in
  let special_dollar = 2 in
  let special_percent = 4 in
  let special_brace_l = 8 in
  let special_brace_r = 16 in
  let special_newline = 32 in
  
  for i = start to min (start + len - 1) (String.length input - 1) do
    match input.[i] with
    | '\\' -> found_mask := !found_mask lor special_backslash
    | '$' -> found_mask := !found_mask lor special_dollar
    | '%' -> found_mask := !found_mask lor special_percent
    | '{' -> found_mask := !found_mask lor special_brace_l
    | '}' -> found_mask := !found_mask lor special_brace_r
    | '\n' -> found_mask := !found_mask lor special_newline
    | _ -> ()
  done;
  !found_mask

let find_special_char input start len =
  let rec find_from pos =
    if pos >= start + len || pos >= String.length input then
      -1
    else
      match input.[pos] with
      | '\\' | '$' | '%' | '{' | '}' | '\n' -> pos
      | _ -> find_from (pos + 1)
  in
  find_from start

type token =
  | TChar of char
  | TCommand of string
  | TNewline
  | TSpace
  | TMath
  | TComment of string
  | TBeginEnv of string
  | TEndEnv of string
  | TBeginGroup
  | TEndGroup
  | TError of string
  | TVerbatim of string

type lex_context = {
  input : string;
  len : int;
  mutable pos : int;
  mutable state : deep_lexer_state;
  mutable tokens : token list;
}

(* Special character flags *)
let special_backslash = 1
let special_dollar = 2
let special_percent = 4
let special_brace_l = 8
let special_brace_r = 16
let special_newline = 32

let make_context state input =
  {
    input = input;
    len = String.length input;
    pos = 0;
    state = state;
    tokens = [];
  }

let peek ctx =
  if ctx.pos < ctx.len then
    Some ctx.input.[ctx.pos]
  else
    None

let peek_ahead ctx n =
  if ctx.pos + n < ctx.len then
    Some ctx.input.[ctx.pos + n]
  else
    None

let advance ctx =
  if ctx.pos < ctx.len then begin
    if ctx.input.[ctx.pos] = '\n' then begin
      ctx.state <- { ctx.state with
        line_no = ctx.state.line_no + 1;
        col_no = 0;
        byte_offset = ctx.state.byte_offset + 1;
        state_hash = None;
      }
    end else begin
      ctx.state <- { ctx.state with
        col_no = ctx.state.col_no + 1;
        byte_offset = ctx.state.byte_offset + 1;
        state_hash = None;
      }
    end;
    ctx.pos <- ctx.pos + 1
  end

let get_catcode ctx c =
  ctx.state.catcodes.(Char.code c)

let emit_token ctx tok =
  ctx.tokens <- tok :: ctx.tokens

(* Fast scanning using fallback *)
let scan_text_fast ctx =
  let special_pos = find_special_char ctx.input ctx.pos (ctx.len - ctx.pos) in
  
  if special_pos = -1 then begin
    (* No special chars - consume rest *)
    let text = String.sub ctx.input ctx.pos (ctx.len - ctx.pos) in
    ctx.pos <- ctx.len;
    String.iter (fun c -> emit_token ctx (TChar c)) text
  end else begin
    (* Process normal chars up to special *)
    for i = ctx.pos to special_pos - 1 do
      emit_token ctx (TChar ctx.input.[i])
    done;
    ctx.pos <- special_pos
  end

(* Read command name *)
let read_command ctx =
  let start = ctx.pos in
  advance ctx;  (* Skip \ *)
  
  (* Check for special single-char commands *)
  match peek ctx with
  | Some c when get_catcode ctx c <> Letter ->
      advance ctx;
      String.make 1 c
  | _ ->
      (* Read letters *)
      while ctx.pos < ctx.len && 
            get_catcode ctx ctx.input.[ctx.pos] = Letter do
        advance ctx
      done;
      String.sub ctx.input (start + 1) (ctx.pos - start - 1)

(* Read verbatim content *)
let read_verbatim ctx end_marker =
  let end_len = String.length end_marker in
  
  let rec find_end pos =
    if pos + end_len > ctx.len then
      ctx.len
    else if String.sub ctx.input pos end_len = end_marker then
      pos
    else
      find_end (pos + 1)
  in
  
  let end_pos = find_end ctx.pos in
  let content = String.sub ctx.input ctx.pos (end_pos - ctx.pos) in
  ctx.pos <- end_pos;
  
  if ctx.pos + end_len <= ctx.len then begin
    ctx.pos <- ctx.pos + end_len;
    ctx.state <- { ctx.state with 
      in_verbatim = false;
      verbatim_end = None;
      state_hash = None;
    }
  end;
  
  content

(* Read comment to end of line *)
let read_comment ctx =
  let start = ctx.pos in
  while ctx.pos < ctx.len && ctx.input.[ctx.pos] <> '\n' do
    advance ctx
  done;
  String.sub ctx.input start (ctx.pos - start)

(* Main lexing function *)
let lex_token ctx =
  if ctx.pos >= ctx.len then
    false
  else if ctx.state.in_verbatim then begin
    match ctx.state.verbatim_end with
    | Some end_marker ->
        let content = read_verbatim ctx end_marker in
        emit_token ctx (TVerbatim content);
        true
    | None ->
        (* Error state *)
        advance ctx;
        emit_token ctx (TError "Verbatim without end marker");
        true
  end else begin
    (* Use character classification to find special characters *)
    let mask = classify_chars_simd ctx.input ctx.pos (min 32 (ctx.len - ctx.pos)) in
    
    if mask = 0 then begin
      (* No special chars in next 32 bytes - fast path *)
      scan_text_fast ctx;
      true
    end else begin
      (* Special character found *)
      match peek ctx with
      | None -> false
      | Some c ->
          match get_catcode ctx c with
          | Escape ->
              let cmd = read_command ctx in
              
              (* Handle special commands *)
              if cmd = "begin" || cmd = "end" then begin
                (* Skip spaces *)
                while ctx.pos < ctx.len && get_catcode ctx ctx.input.[ctx.pos] = Space do
                  advance ctx
                done;
                
                (* Read environment name *)
                if ctx.pos < ctx.len && ctx.input.[ctx.pos] = '{' then begin
                  advance ctx;
                  let env_start = ctx.pos in
                  while ctx.pos < ctx.len && ctx.input.[ctx.pos] <> '}' do
                    advance ctx
                  done;
                  let env_name = String.sub ctx.input env_start (ctx.pos - env_start) in
                  if ctx.pos < ctx.len then advance ctx;
                  
                  if cmd = "begin" then begin
                    ctx.state <- enter_environment ctx.state env_name;
                    emit_token ctx (TBeginEnv env_name)
                  end else begin
                    ctx.state <- exit_environment ctx.state env_name;
                    emit_token ctx (TEndEnv env_name)
                  end
                end else begin
                  emit_token ctx (TCommand cmd)
                end
              end else begin
                emit_token ctx (TCommand cmd)
              end;
              true
              
          | BeginGroup ->
              advance ctx;
              ctx.state <- enter_group ctx.state;
              emit_token ctx TBeginGroup;
              true
              
          | EndGroup ->
              advance ctx;
              ctx.state <- exit_group ctx.state;
              emit_token ctx TEndGroup;
              true
              
          | MathShift ->
              advance ctx;
              
              (* Check for $$ *)
              if peek ctx = Some '$' then begin
                advance ctx;
                if ctx.state.math_mode = NoMath then
                  ctx.state <- enter_math_mode ctx.state DisplayMath "$$"
                else
                  ctx.state <- exit_math_mode ctx.state;
              end else begin
                if ctx.state.math_mode = NoMath then
                  ctx.state <- enter_math_mode ctx.state InlineMath "$"
                else
                  ctx.state <- exit_math_mode ctx.state;
              end;
              emit_token ctx TMath;
              true
              
          | Comment ->
              advance ctx;
              let comment = read_comment ctx in
              emit_token ctx (TComment comment);
              ctx.state <- { ctx.state with 
                in_comment = false;  (* Comments end at newline *)
                state_hash = None;
              };
              true
              
          | Space ->
              while ctx.pos < ctx.len && get_catcode ctx ctx.input.[ctx.pos] = Space do
                advance ctx
              done;
              emit_token ctx TSpace;
              true
              
          | EndOfLine ->
              advance ctx;
              emit_token ctx TNewline;
              true
              
          | _ ->
              advance ctx;
              emit_token ctx (TChar c);
              true
    end
  end

(* Lex entire string with state *)
let lex_string state input =
  let ctx = make_context state input in
  
  (* Main lexing loop *)
  while lex_token ctx do
    ()
  done;
  
  (List.rev ctx.tokens, ctx.state)

(* Lex with convergence detection *)
let lex_with_convergence state input target_state_hash =
  let ctx = make_context state input in
  
  (* Lex and check for convergence periodically *)
  let check_interval = 100 in  (* Check every 100 tokens *)
  let token_count = ref 0 in
  let converged = ref false in
  
  while lex_token ctx && not !converged do
    incr token_count;
    
    if !token_count mod check_interval = 0 then begin
      (* Check if we've converged *)
      if hash_deep_state ctx.state = target_state_hash then begin
        (* State has converged - can stop early *)
        converged := true
      end
    end
  done;
  
  (List.rev ctx.tokens, ctx.state, !token_count)