(** User macro registry: parse, classify, and track user-defined commands.

    Parses [\newcommand], [\renewcommand], and [\providecommand] from LaTeX
    source. Classifies each as supported or unsupported, builds a def-use
    dependency graph, and detects cycles. Supported, acyclic macros can be
    merged into {!Macro_catalogue} for expansion. *)

type macro_kind = Newcommand | Renewcommand | Providecommand

type user_macro_def = {
  kind : macro_kind;
  name : string;  (** Without backslash. *)
  arity : int;  (** 0..9, from [[N]] spec. *)
  opt_default : string option;  (** From [[default]], if present. *)
  body : string;  (** Raw body text. *)
  loc : int;  (** Byte offset in source. *)
}

type support_status = Supported | Unsupported of string
type classified_def = { def : user_macro_def; status : support_status }
type dep_edge = { from_name : string; to_name : string }

type registry = {
  defs : classified_def list;
  edges : dep_edge list;
  has_cycle : bool;
  cycle_path : string list;
  supported_count : int;
  unsupported_count : int;
}

val parse_definitions : string -> user_macro_def list
(** Extract all [\newcommand], [\renewcommand], [\providecommand] definitions
    from a LaTeX source string. *)

val classify : user_macro_def -> classified_def
(** Classify a definition as supported or unsupported based on its body content.
    Unsupported macros include a diagnostic reason string. *)

val build_dep_edges : user_macro_def list -> dep_edge list
(** Build dependency edges between user macros (A depends on B if A's body
    contains [\B]). *)

val detect_cycle : dep_edge list -> string list -> bool * string list
(** [detect_cycle edges names] returns [(has_cycle, cycle_path)]. Only considers
    edges between names in the [names] list. *)

val create : string -> registry
(** Top-level entry point: parse, classify, build edges, detect cycles. *)

val param_to_placeholder : string -> string
(** Convert [#1..#9] parameter references to [$1..$9] placeholders for the
    {!Macro_catalogue} inline template format. *)
