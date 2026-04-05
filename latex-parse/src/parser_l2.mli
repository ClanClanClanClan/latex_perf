(** LaTeX parser for commands, groups, environments, and structural elements. *)

type cmd = { name : string; opts : string list; args : string list }

type node =
  | Word of string
  | Cmd of cmd
  | Group of node list
  | Environment of { env_name : string; opts : string list; body : node list }
  | MathInline of string
  | MathDisplay of string
  | Comment of string

type doc_section = {
  level : int;
  title : string;
  label : string option;
  children : doc_element list;
}

and doc_element =
  | Section of doc_section
  | Paragraph of node list
  | Float of {
      kind : string;
      label : string option;
      caption : string option;
      body : node list;
    }
  | MathBlock of string
  | RawNodes of node list

type document = {
  preamble : node list;
  body : doc_element list;
  labels : (string * int) list;
  refs : (string * int) list;
}

val normalize_ws : string -> string
val normalize_punct : string -> string
val parse : string -> node list
val parse_with_envs : string -> node list
val extract_document : node list -> document
val parse_success : string -> bool
val serialize : node list -> string
