(** Comprehensive LaTeX parser with located AST (spec §4, W40-52). *)

type loc = { line : int; col : int; offset : int }
type cmd = { name : string; opts : string list; args : string list }

type node =
  | Word of string
  | Cmd of cmd
  | Group of node list
  | Environment of { env_name : string; opts : string list; body : node list }
  | MathInline of string
  | MathDisplay of string
  | Comment of string
  | Verbatim of { env_name : string; content : string }
  | Whitespace of string
  | Newline
  | Error of { message : string; position : int }

type located_node = { node : node; loc : loc }

type doc_section = {
  level : int;
  title : string;
  label : string option;
  children : doc_element list;
}

and doc_element =
  | Section of doc_section
  | Paragraph of located_node list
  | Float of {
      kind : string;
      label : string option;
      caption : string option;
      body : located_node list;
    }
  | MathBlock of { env_name : string; content : string }
  | RawNodes of located_node list

type document = {
  preamble : located_node list;
  body : doc_element list;
  labels : (string * loc) list;
  refs : (string * loc) list;
  errors : (string * loc) list;
}

type dirty_region = { dr_start : int; dr_end : int }

val parse : string -> node list
val parse_located : string -> located_node list * (string * loc) list
val parse_with_envs : string -> node list
val extract_document : string -> document
val parse_success : string -> bool
val find_dirty_region : string -> string -> dirty_region
val normalize_ws : string -> string
val normalize_punct : string -> string
val serialize : node list -> string
