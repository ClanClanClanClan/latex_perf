(** See [cst.mli]. *)

type span = Stable_spans.t
type trivia_kind = Whitespace | Comment
type token_kind = Word | Command | GroupOpen | GroupClose | MathDelim

type t =
  | CToken of { kind : token_kind; text : string; span : span }
  | CTrivia of { kind : trivia_kind; text : string; span : span }
  | CGroup of { children : t list; span : span }
  | CEnvironment of { env_name : string; body_text : string; span : span }
  | CMathInline of { text : string; span : span }
  | CMathDisplay of { text : string; span : span }
  | CVerbatim of { env_name : string; text : string; span : span }
  | CUnparsed of { text : string; span : span }

let span_of = function
  | CToken { span; _ }
  | CTrivia { span; _ }
  | CGroup { span; _ }
  | CEnvironment { span; _ }
  | CMathInline { span; _ }
  | CMathDisplay { span; _ }
  | CVerbatim { span; _ }
  | CUnparsed { span; _ } ->
      span

(* [text_of] returns the literal bytes for a node. For [CGroup], we don't store
   delimiters as separate tokens; instead we assume the span covers the full [{
   ... }] and emit it via substring at serialize time. To keep [text_of] total,
   each variant carries its own text except [CGroup] whose serialization is [\{
   children... \}]. We therefore serialize [CGroup] by concatenating children
   and wrapping in braces. *)

let rec serialize_node = function
  | CToken { text; _ }
  | CTrivia { text; _ }
  | CMathInline { text; _ }
  | CMathDisplay { text; _ }
  | CVerbatim { text; _ }
  | CUnparsed { text; _ } ->
      text
  | CEnvironment { env_name; body_text; _ } ->
      "\\begin{" ^ env_name ^ "}" ^ body_text ^ "\\end{" ^ env_name ^ "}"
  | CGroup { children; _ } ->
      let buf = Buffer.create 64 in
      Buffer.add_char buf '{';
      List.iter (fun c -> Buffer.add_string buf (serialize_node c)) children;
      Buffer.add_char buf '}';
      Buffer.contents buf

let serialize nodes =
  let buf = Buffer.create 256 in
  List.iter (fun n -> Buffer.add_string buf (serialize_node n)) nodes;
  Buffer.contents buf

let byte_length nodes = String.length (serialize nodes)
