(* L1 Expander - Macro expansion layer for LaTeX Perfectionist v25 *)
(* Expands macros, handles TeX primitives, and manages expansion state *)

(** Expansion state - tracks defined macros, counters, and environments *)
type state

(** Macro definition with parameters and replacement text *)
type macro_def = {
  name: string;
  params: int;  (* Number of parameters, 0-9 *)
  replacement: Lexer_v25.token list;
  is_long: bool;  (* \long macros can contain \par *)
  is_outer: bool;  (* \outer macros have restrictions *)
}

(** Expansion options *)
type options = {
  max_expansion_depth: int;  (* Default: 1000 *)
  max_expansions: int;       (* Default: 100000 *)
  track_source: bool;        (* Track original positions *)
}

(** Expansion result *)
type result = {
  tokens: Lexer_v25.token list;
  state: state;
  stats: expansion_stats;
}

(** Expansion statistics *)
and expansion_stats = {
  expansions_performed: int;
  max_depth_reached: int;
  time_ms: float;
}

(** Create initial expansion state *)
val initial_state : unit -> state

(** Define a macro *)
val define_macro : state -> string -> macro_def -> state

(** Check if a macro is defined *)
val is_defined : state -> string -> bool

(** Get macro definition *)
val get_macro : state -> string -> macro_def option

(** Expand a list of tokens *)
val expand_tokens : ?options:options -> state -> Lexer_v25.token list -> result

(** Expand a token array (for L0 integration) *)
val expand_chunk : ?options:options -> ?state:state -> Lexer_v25.token array -> 
  (Lexer_v25.token array * state)

(** Built-in TeX primitives *)
val register_primitives : state -> state

(** Expansion control *)
val no_expand_next : state -> state  (* \noexpand *)
val expand_after : state -> state    (* \expandafter *)

(** Environment management *)
val begin_environment : state -> string -> state
val end_environment : state -> string -> state
val in_environment : state -> string -> bool

(** Counter management *)
val new_counter : state -> string -> state
val set_counter : state -> string -> int -> state
val get_counter : state -> string -> int option
val step_counter : state -> string -> state

(** State serialization for incremental processing *)
val state_to_string : state -> string
val state_of_string : string -> state option