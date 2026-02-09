(** LaTeX parser for commands, groups, and structural elements. *)

type cmd = { name : string; opts : string list; args : string list }
type node = Word of string | Cmd of cmd | Group of node list

val normalize_ws : string -> string
(** Collapse runs of whitespace to a single space and trim. *)

val normalize_punct : string -> string
(** Remove spurious spaces around punctuation and brackets. *)

val parse : string -> node list
(** Parse a LaTeX source string into a node tree. *)

val serialize : node list -> string
(** Render a node tree back to normalised LaTeX source. *)
