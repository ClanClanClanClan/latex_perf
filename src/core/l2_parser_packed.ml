(* L2 Parser - Packed Token Version
   Parses packed tokens from L1 without conversion overhead *)

type packed_token = int32

(* AST types - same as before but optimized for packed tokens *)
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
  | BlockError of { msg: string; raw_tokens: packed_token array }

and inline =
  | Command of { name: string; args: arg list }
  | Text of string
  | MathInline of inline list
  | Group of inline list
  | Space
  | Newline
  | InlineError of { msg: string; raw_tokens: packed_token array }

type parse_stats = {
  total_tokens: int;
  parse_time_ms: float;
  error_count: int;
  max_depth: int;
}

(* Parser state *)
type parser_state = {
  mutable pos: int;
  tokens: packed_token array;
  mutable error_count: int;
  mutable max_depth: int;
  current_depth: int;
}

let create_parser_state tokens = {
  pos = 0;
  tokens = tokens;
  error_count = 0;
  max_depth = 0;
  current_depth = 0;
}

(* Token utility functions *)
let is_macro_token token =
  let open L0_lexer_track_a_arena.TokenPacking in
  let catcode = unpack_catcode token in
  catcode = cc_escape

let get_macro_name token =
  if is_macro_token token then
    let open L0_lexer_track_a_arena in
    let macro_id = TokenPacking.unpack_data token in
    StringOps.get_macro_name_by_id macro_id
  else
    failwith "Not a macro token"

let is_char_token token =
  let open L0_lexer_track_a_arena.TokenPacking in
  let catcode = unpack_catcode token in
  catcode = cc_letter || catcode = cc_other || catcode = cc_space

let get_char token =
  if is_char_token token then
    let open L0_lexer_track_a_arena.TokenPacking in
    let ascii = (unpack_data token) land 0xFF in
    Char.chr ascii
  else
    failwith "Not a character token"

(* Simple parser functions *)
let peek_token state =
  if state.pos < Array.length state.tokens then
    Some state.tokens.(state.pos)
  else
    None

let consume_token state =
  if state.pos < Array.length state.tokens then begin
    let token = state.tokens.(state.pos) in
    state.pos <- state.pos + 1;
    Some token
  end else
    None

(* Parse text content from character tokens *)
let parse_text_content state =
  let buffer = Buffer.create 256 in
  let rec loop () =
    match peek_token state with
    | Some token when is_char_token token ->
        ignore (consume_token state);
        Buffer.add_char buffer (get_char token);
        loop ()
    | _ -> 
        Buffer.contents buffer
  in
  let text = loop () in
  if String.length text > 0 then [Text text] else []

(* Parse display math *)
let parse_display_math state =
  (* Look for \[ ... \] pattern *)
  match peek_token state with
  | Some token when is_macro_token token ->
      let name = get_macro_name token in
      if name = "[" then begin
        ignore (consume_token state); (* consume \[ *)
        
        (* Parse content until \] *)
        let content_buffer = Buffer.create 256 in
        let rec parse_until_close () =
          match consume_token state with
          | Some token when is_macro_token token ->
              let macro_name = get_macro_name token in
              if macro_name = "]" then
                [MathDisplay [Text (Buffer.contents content_buffer)]]
              else begin
                Buffer.add_char content_buffer '\\';
                Buffer.add_string content_buffer macro_name;
                parse_until_close ()
              end
          | Some token when is_char_token token ->
              Buffer.add_char content_buffer (get_char token);
              parse_until_close ()
          | Some _ ->
              parse_until_close () (* Skip other tokens *)
          | None ->
              [BlockError { msg = "Unclosed display math"; raw_tokens = [||] }]
        in
        parse_until_close ()
      end else
        []
    | _ -> []

(* Simple block parser *)
let rec parse_blocks state =
  let blocks = ref [] in
  
  while state.pos < Array.length state.tokens do
    (* Try display math first *)
    let display_math = parse_display_math state in
    if display_math <> [] then
      blocks := display_math @ !blocks
    else begin
      (* Parse regular text *)
      let text_content = parse_text_content state in
      if text_content <> [] then
        blocks := (Paragraph text_content) :: !blocks
      else
        (* Skip unknown tokens *)
        ignore (consume_token state)
    end
  done;
  
  List.rev !blocks

(* Main parse function *)
let parse_tokens (tokens: packed_token array) =
  let start_time = Sys.time () in
  let state = create_parser_state tokens in
  
  let blocks = parse_blocks state in
  
  let end_time = Sys.time () in
  let parse_time = (end_time -. start_time) *. 1000.0 in
  
  blocks

(* Convert AST to string for debugging *)
let rec ast_to_string blocks =
  let rec block_to_string = function
    | Paragraph inlines ->
        "Paragraph(" ^ (String.concat "" (List.map inline_to_string inlines)) ^ ")"
    | MathDisplay inlines ->
        "MathDisplay(" ^ (String.concat "" (List.map inline_to_string inlines)) ^ ")"  
    | Section { title; _ } ->
        "Section(" ^ (String.concat "" (List.map inline_to_string title)) ^ ")"
    | Environment { name; _ } ->
        "Environment(" ^ name ^ ")"
    | BlockError { msg; _ } ->
        "BlockError(" ^ msg ^ ")"
    | _ ->
        "OtherBlock"
  and inline_to_string = function
    | Text s -> s
    | Command { name; _ } -> "\\" ^ name
    | MathInline inlines -> "$" ^ (String.concat "" (List.map inline_to_string inlines)) ^ "$"
    | Space -> " "
    | Newline -> "\n"
    | Group inlines -> "{" ^ (String.concat "" (List.map inline_to_string inlines)) ^ "}"
    | InlineError { msg; _ } -> "[ERROR:" ^ msg ^ "]"
  in
  "[" ^ String.concat "; " (List.map block_to_string blocks) ^ "]"