(* core_lexer.ml - Core lexing engine for v24-R3 *)

open Types

(** Character classification *)
let is_letter c = 
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let is_space c = 
  c = ' ' || c = '\t'

let is_newline c = 
  c = '\n' || c = '\r'

(** Lexer context for efficient processing *)
type lex_context = {
  mutable pos : int;
  mutable line : int;
  mutable col : int;
  mutable state : lexer_state;
  input : string;
  len : int;
}

(** Create lexing context *)
let make_context state input =
  {
    pos = 0;
    line = state.line_no;
    col = state.col_no;
    state = state;
    input = input;
    len = String.length input;
  }

(** Peek at current character *)
let peek ctx =
  if ctx.pos < ctx.len then
    Some ctx.input.[ctx.pos]
  else
    None

(** Advance position *)
let advance ctx =
  if ctx.pos < ctx.len then begin
    if ctx.input.[ctx.pos] = '\n' then begin
      ctx.line <- ctx.line + 1;
      ctx.col <- 0;
    end else begin
      ctx.col <- ctx.col + 1;
    end;
    ctx.pos <- ctx.pos + 1
  end

(** Read while predicate holds *)
let read_while ctx pred =
  let start = ctx.pos in
  while ctx.pos < ctx.len && pred ctx.input.[ctx.pos] do
    advance ctx
  done;
  String.sub ctx.input start (ctx.pos - start)

(** Read command name *)
let read_command ctx =
  advance ctx; (* skip \ *)
  if ctx.pos < ctx.len && is_letter ctx.input.[ctx.pos] then
    read_while ctx is_letter
  else
    ""

(** Read comment *)
let read_comment ctx =
  advance ctx; (* skip % *)
  let content = read_while ctx (fun c -> c <> '\n') in
  TComment content

(** Lex math mode *)
let lex_math_char ctx =
  match peek ctx with
  | Some '$' ->
      advance ctx;
      ctx.state <- { ctx.state with in_math = false };
      TMath
  | Some c ->
      advance ctx;
      TChar c
  | None -> TError "Unexpected end in math mode"

(** Main lexing function for a single token *)
let lex_token ctx =
  match peek ctx with
  | None -> None
  | Some c ->
      if ctx.state.in_comment then begin
        if is_newline c then begin
          advance ctx;
          ctx.state <- { ctx.state with in_comment = false };
          Some TNewline
        end else begin
          advance ctx;
          Some (TChar c)
        end
      end else if ctx.state.in_math then begin
        Some (lex_math_char ctx)
      end else begin
        match c with
        | ' ' | '\t' ->
            let _ = read_while ctx is_space in
            Some TSpace
        | '\n' ->
            advance ctx;
            Some TNewline
        | '\\' ->
            let cmd = read_command ctx in
            if cmd = "" then
              Some (TChar '\\')
            else if cmd = "begin" || cmd = "end" then begin
              (* Simplified env handling *)
              let _ = read_while ctx is_space in
              if ctx.pos < ctx.len && ctx.input.[ctx.pos] = '{' then begin
                advance ctx;
                let env = read_while ctx (fun c -> c <> '}') in
                if ctx.pos < ctx.len then advance ctx;
                if cmd = "begin" then
                  Some (TBeginEnv env)
                else
                  Some (TEndEnv env)
              end else
                Some (TCommand cmd)
            end else
              Some (TCommand cmd)
        | '%' ->
            ctx.state <- { ctx.state with in_comment = true };
            Some (read_comment ctx)
        | '$' ->
            advance ctx;
            ctx.state <- { ctx.state with in_math = true };
            Some TMath
        | _ ->
            advance ctx;
            Some (TChar c)
      end

(** Lex an entire string from a given state *)
let lex_string state input =
  let ctx = make_context state input in
  let tokens = ref [] in
  let rec loop () =
    match lex_token ctx with
    | None -> ()
    | Some tok ->
        tokens := tok :: !tokens;
        loop ()
  in
  loop ();
  let final_state = {
    line_no = ctx.line;
    col_no = ctx.col;
    in_math = ctx.state.in_math;
    in_comment = ctx.state.in_comment;
    in_verbatim = ctx.state.in_verbatim;
    mode_stack = ctx.state.mode_stack;
  } in
  (List.rev !tokens, final_state)

(** Lex a single line (without newline) *)
let lex_line state line =
  lex_string state (line ^ "\n")