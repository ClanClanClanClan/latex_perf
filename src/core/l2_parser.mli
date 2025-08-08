(** L2 Incremental Parser - LaTeX Perfectionist v25
    
    Transforms expanded token streams into structured AST.
    Performance target: ≤10ms P95 on 60k tokens.
*)

open Lexer_v25

(** List kinds *)
type list_kind = 
  | Itemize 
  | Enumerate 
  | Description

(** Include types *)
type include_kind = 
  | Input 
  | Include 
  | InputListing 
  | VerbatimInput

(** Argument types *)
type arg =
  | Optional of inline list
  | Required of inline list

(** Block-level AST nodes *)
and block =
  | Section of { level: int; title: inline list; content: block list }
  | Environment of { name: string; args: arg list; body: block list }
  | Paragraph of inline list
  | List of { kind: list_kind; items: block list list }
  | Table of { spec: string; rows: block list list list }
  | MathDisplay of inline list
  | Include of { kind: include_kind; path: string }
  | BlockError of { msg: string; tokens: token list }

(** Inline-level AST nodes *)
and inline =
  | Command of { name: string; args: arg list }
  | Text of string
  | MathInline of inline list
  | Group of inline list
  | Space
  | Newline
  | InlineError of { msg: string; tokens: token list }

(** Top-level document *)
type document = {
  preamble: block list;
  body: block list;
  stats: parse_stats;
}

(** Parsing statistics *)
and parse_stats = {
  total_tokens: int;
  parse_time_ms: float;
  error_count: int;
  max_depth: int;
}

(** Parser state *)
type state

(** Parser options *)
type options = {
  max_errors: int;        (** Stop after this many errors (default: 100) *)
  error_recovery: bool;   (** Enable error recovery (default: true) *)
  track_positions: bool;  (** Track source positions (default: false) *)
  math_mode: bool;       (** Start in math mode (default: false) *)
}

(** Default options *)
val default_options : options

(** Create initial parser state *)
val initial_state : ?options:options -> unit -> state

(** Parse a token stream into AST *)
val parse : ?options:options -> token array -> document

(** Parse incrementally with previous state *)
val parse_incremental : state -> token array -> document * state

(** Pretty-print AST for debugging *)
val pp_document : Format.formatter -> document -> unit
val pp_block : Format.formatter -> block -> unit
val pp_inline : Format.formatter -> inline -> unit