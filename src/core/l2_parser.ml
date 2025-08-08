(** L2 Incremental Parser Implementation - LaTeX Perfectionist v25 *)

open Lexer_v25
open Catcode

(* Type definitions - must match .mli exactly *)
type list_kind = Itemize | Enumerate | Description
type include_kind = Input | Include | InputListing | VerbatimInput

type arg =
  | Optional of inline list
  | Required of inline list

and block =
  | Section of { level: int; title: inline list; content: block list }
  | Environment of { name: string; args: arg list; body: block list }
  | Paragraph of inline list
  | List of { kind: list_kind; items: block list list }
  | Table of { spec: string; rows: block list list list }
  | MathDisplay of inline list
  | Include of { kind: include_kind; path: string }
  | BlockError of { msg: string; tokens: token list }

and inline =
  | Command of { name: string; args: arg list }
  | Text of string
  | MathInline of inline list
  | Group of inline list
  | Space
  | Newline
  | InlineError of { msg: string; tokens: token list }

type document = {
  preamble: block list;
  body: block list;
  stats: parse_stats;
}

and parse_stats = {
  total_tokens: int;
  parse_time_ms: float;
  error_count: int;
  max_depth: int;
}

type options = {
  max_errors: int;
  error_recovery: bool;
  track_positions: bool;
  math_mode: bool;
}

let default_options = {
  max_errors = 100;
  error_recovery = true;
  track_positions = false;
  math_mode = false;
}

(* Parser state *)
type state = {
  mutable tokens: token array;
  mutable pos: int;
  mutable errors: int;
  mutable max_depth: int;
  mutable current_depth: int;
  options: options;
  mutable math_mode: bool;
  mutable in_preamble: bool;
}

(* Utilities *)
let initial_state ?(options=default_options) () = {
  tokens = [||];
  pos = 0;
  errors = 0;
  max_depth = 0;
  current_depth = 0;
  options;
  math_mode = options.math_mode;
  in_preamble = true;
}

let[@inline] peek state =
  if state.pos < Array.length state.tokens then
    Some state.tokens.(state.pos)
  else
    None

let[@inline] peek2 state =
  if state.pos + 1 < Array.length state.tokens then
    (Some state.tokens.(state.pos), Some state.tokens.(state.pos + 1))
  else if state.pos < Array.length state.tokens then
    (Some state.tokens.(state.pos), None)
  else
    (None, None)

let[@inline] advance state =
  state.pos <- state.pos + 1

let[@inline] consume state =
  if state.pos < Array.length state.tokens then
    let tok = state.tokens.(state.pos) in
    advance state;
    Some tok
  else
    None

let error state msg =
  state.errors <- state.errors + 1;
  if state.errors > state.options.max_errors then
    failwith (Printf.sprintf "Too many parse errors (>%d)" state.options.max_errors)

(* Forward declarations *)
let rec parse_blocks state = 
  parse_block_list state []

and parse_block_list state acc =
  match peek state with
  | None -> List.rev acc
  | Some _ ->
      match parse_block state with
      | Some block -> parse_block_list state (block :: acc)
      | None -> List.rev acc

and parse_block state =
  match peek2 state with
  | Some (TMacro "section"), _ -> parse_section state 1
  | Some (TMacro "subsection"), _ -> parse_section state 2
  | Some (TMacro "subsubsection"), _ -> parse_section state 3
  | Some (TMacro "begin"), _ -> parse_environment state
  | Some (TMacro "\\"), _ -> parse_display_math state
  | Some (TMacro "["), _ -> 
      advance state;
      parse_display_math_bracket state
  | Some (TMacro name), _ when is_include_command name -> 
      parse_include state name
  | Some (TGroupOpen | TMacro _ | TChar _), _ -> 
      parse_paragraph state
  | Some (TGroupClose | TParam _), _ ->
      advance state; (* Skip unexpected tokens *)
      None
  | _ -> None

and parse_section state level =
  match consume state with
  | Some (TMacro _) ->
      state.current_depth <- state.current_depth + 1;
      if state.current_depth > state.max_depth then
        state.max_depth <- state.current_depth;
      
      let title = parse_argument state in
      let content = parse_block_list state [] in
      
      state.current_depth <- state.current_depth - 1;
      Some (Section { level; title; content })
  | _ -> None

and parse_environment state =
  match consume state with
  | Some (TMacro "begin") ->
      let name = parse_env_name state in
      let args = parse_arguments state in
      
      (* Special handling for document environment *)
      if name = "document" && state.in_preamble then
        state.in_preamble <- false;
      
      let body = parse_env_body state name in
      Some (Environment { name; args; body })
  | _ -> None

and parse_env_name state =
  match parse_argument state with
  | [Text name] -> name
  | _ -> "unknown"

and parse_env_body state name =
  let rec loop acc =
    match peek2 state with
    | Some (TMacro "end"), Some (TGroupOpen) ->
        advance state; advance state;
        let end_name = parse_env_name state in
        if end_name = name then
          List.rev acc
        else (
          error state (Printf.sprintf "Mismatched \\end{%s}, expected \\end{%s}" end_name name);
          List.rev acc
        )
    | (None, _) | (_, None) -> 
        error state (Printf.sprintf "Unclosed environment: %s" name);
        List.rev acc
    | _ ->
        match parse_block state with
        | Some block -> loop (block :: acc)
        | None -> 
            (* Try to consume a token to avoid infinite loop *)
            ignore (consume state);
            loop acc
  in
  loop []

and parse_display_math state =
  match consume state with
  | Some (TMacro "\\") ->
      let old_math = state.math_mode in
      state.math_mode <- true;
      let content = parse_math_content state in
      state.math_mode <- old_math;
      
      (* Consume closing \\ *)
      (match peek state with
       | Some (TMacro "\\") -> advance state
       | _ -> error state "Expected closing \\\\");
      
      Some (MathDisplay content)
  | _ -> None

and parse_display_math_bracket state =
  let old_math = state.math_mode in
  state.math_mode <- true;
  let content = parse_math_until state (TMacro "]") in
  state.math_mode <- old_math;
  Some (MathDisplay content)

and parse_paragraph state =
  let inlines = parse_inlines state in
  if inlines = [] then None
  else Some (Paragraph inlines)

and parse_include state cmd =
  let kind = match cmd with
    | "input" -> Input
    | "include" -> Include
    | "lstinputlisting" -> InputListing
    | "verbatiminput" -> VerbatimInput
    | _ -> Input
  in
  advance state; (* consume command *)
  let path = match parse_argument state with
    | [Text p] -> p
    | _ -> ""
  in
  Some (Include { kind; path })

(* Inline parsing *)
and parse_inlines state =
  let rec loop acc =
    match parse_inline state with
    | Some inline -> loop (inline :: acc)
    | None -> List.rev acc
  in
  loop []

and parse_inline state =
  match peek state with
  | None -> None
  | Some (TChar (c, cat)) when cat <> Space && cat <> EndLine && cat <> MathShift ->
      (* Coalesce adjacent characters into single text node *)
      let buf = Buffer.create 16 in
      Buffer.add_char buf (Uchar.to_char c);
      advance state;
      let rec collect_chars () =
        match peek state with
        | Some (TChar (c2, cat2)) when cat2 <> Space && cat2 <> EndLine && 
                                       cat2 <> MathShift && cat2 <> AlignTab &&
                                       cat2 <> Comment ->
            Buffer.add_char buf (Uchar.to_char c2);
            advance state;
            collect_chars ()
        | _ -> ()
      in
      collect_chars ();
      Some (Text (Buffer.contents buf))
  | Some (TMacro name) when String.length name > 0 && name.[0] <> '\\' ->
      parse_command state
  | Some (TChar (c, MathShift)) when Uchar.to_int c = Char.code '$' ->
      advance state;
      let old_math = state.math_mode in
      state.math_mode <- true;
      let content = parse_math_until state (TChar (Uchar.of_char '$', MathShift)) in
      state.math_mode <- old_math;
      Some (MathInline content)
  | Some TGroupOpen ->
      advance state;
      let content = parse_group_content state in
      Some (Group content)
  | Some (TChar (_, Space)) ->
      advance state;
      Some Space
  | Some (TChar (_, EndLine)) ->
      advance state;
      Some Newline
  | Some (TChar (_, Comment) | TGroupClose | TChar (_, AlignTab) | TParam _) ->
      None
  | _ -> None

and parse_command state =
  match consume state with
  | Some (TMacro name) ->
      let args = parse_arguments state in
      Some (Command { name; args })
  | _ -> None

and parse_arguments state =
  let rec loop acc =
    match peek state with
    | Some TGroupOpen ->
        let arg = Required (parse_argument state) in
        loop (arg :: acc)
    | Some (TMacro "[") ->
        advance state;
        let content = parse_optional_arg state in
        let arg = Optional content in
        loop (arg :: acc)
    | _ -> List.rev acc
  in
  loop []

and parse_argument state =
  match peek state with
  | Some TGroupOpen ->
      advance state;
      parse_group_content state
  | _ -> []

and parse_optional_arg state =
  parse_until state (TMacro "]")

and parse_group_content state =
  parse_until state TGroupClose

and parse_until state end_tok =
  let rec loop acc =
    match peek state with
    | None -> List.rev acc
    | Some tok when tok = end_tok -> 
        advance state;
        List.rev acc
    | _ ->
        match parse_inline state with
        | Some inline -> loop (inline :: acc)
        | None -> 
            advance state; (* skip unparseable token *)
            loop acc
  in
  loop []

and parse_math_content state =
  parse_inlines state

and parse_math_until state end_tok =
  parse_until state end_tok

(* Helper predicates *)
and is_include_command = function
  | "input" | "include" | "lstinputlisting" | "verbatiminput" -> true
  | _ -> false

(* Main parsing functions *)
let parse ?(options=default_options) tokens =
  let start_time = Unix.gettimeofday () in
  let state = {
    tokens;
    pos = 0;
    errors = 0;
    max_depth = 0;
    current_depth = 0;
    options;
    math_mode = options.math_mode;
    in_preamble = false; (* Start in body for simple documents *)
  } in
  
  let preamble = [] in  (* No preamble for simple documents *)
  let body = parse_block_list state [] in
  
  let parse_time = (Unix.gettimeofday () -. start_time) *. 1000. in
  
  {
    preamble;
    body;
    stats = {
      total_tokens = Array.length tokens;
      parse_time_ms = parse_time;
      error_count = state.errors;
      max_depth = state.max_depth;
    }
  }

let parse_incremental state tokens =
  state.tokens <- tokens;
  state.pos <- 0;
  let doc = parse ~options:state.options tokens in
  (doc, state)

(* Pretty printing *)
let pp_list pp_item fmt items =
  Format.pp_print_list 
    ~pp_sep:(fun fmt () -> Format.pp_print_string fmt "; ")
    pp_item fmt items

let rec pp_inline fmt = function
  | Command { name; args } ->
      Format.fprintf fmt "\\%s%a" name pp_args args
  | Text s ->
      Format.fprintf fmt "\"%s\"" s
  | MathInline content ->
      Format.fprintf fmt "$%a$" (pp_list pp_inline) content
  | Group content ->
      Format.fprintf fmt "{%a}" (pp_list pp_inline) content
  | Space ->
      Format.pp_print_string fmt "␣"
  | Newline ->
      Format.pp_print_string fmt "⏎"
  | InlineError { msg; _ } ->
      Format.fprintf fmt "ERROR(%s)" msg

and pp_args fmt args =
  List.iter (function
    | Optional content -> 
        Format.fprintf fmt "[%a]" (pp_list pp_inline) content
    | Required content ->
        Format.fprintf fmt "{%a}" (pp_list pp_inline) content
  ) args

let rec pp_block fmt = function
  | Section { level; title; content } ->
      Format.fprintf fmt "Section(L%d, %a, [%a])" 
        level (pp_list pp_inline) title (pp_list pp_block) content
  | Environment { name; args; body } ->
      Format.fprintf fmt "Env(%s%a, [%a])" 
        name pp_args args (pp_list pp_block) body
  | Paragraph content ->
      Format.fprintf fmt "Para(%a)" (pp_list pp_inline) content
  | List { kind; items } ->
      Format.fprintf fmt "List(%s, %d items)" 
        (match kind with Itemize -> "itemize" | Enumerate -> "enum" | Description -> "desc")
        (List.length items)
  | Table { spec; rows } ->
      Format.fprintf fmt "Table(%s, %d rows)" spec (List.length rows)
  | MathDisplay content ->
      Format.fprintf fmt "Math[%a]" (pp_list pp_inline) content
  | Include { kind; path } ->
      Format.fprintf fmt "Include(%s, %s)" 
        (match kind with Input -> "input" | Include -> "include" | InputListing -> "listing" | VerbatimInput -> "verbatim")
        path
  | BlockError { msg; _ } ->
      Format.fprintf fmt "ERROR(%s)" msg

let pp_document fmt doc =
  Format.fprintf fmt "Document {@\n";
  Format.fprintf fmt "  preamble: [@[%a@]];@\n" (pp_list pp_block) doc.preamble;
  Format.fprintf fmt "  body: [@[%a@]];@\n" (pp_list pp_block) doc.body;
  Format.fprintf fmt "  stats: { tokens=%d; time=%.2fms; errors=%d; depth=%d }@\n" 
    doc.stats.total_tokens doc.stats.parse_time_ms 
    doc.stats.error_count doc.stats.max_depth;
  Format.fprintf fmt "}"