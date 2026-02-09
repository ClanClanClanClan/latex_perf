(** Simple LaTeX control-sequence expander with configurable stripping rules. *)

type cfg = { strip_controls : string list; bfseries_until_brace : bool }

val default : cfg
(** Default configuration: strips [textbf], [emph], [section]; handles
    [bfseries]. *)

val of_json : Yojson.Safe.t -> cfg
(** Parse a configuration from JSON, falling back to {!default} on error. *)

val expand_once : cfg -> string -> string
(** Single-pass expansion: strip configured commands once. *)

val expand_fix : cfg -> string -> string
(** Fixed-point expansion: iterate {!expand_once} until stable. *)

val expand_and_tokenize :
  cfg -> string -> string * Latex_parse_lib.Tokenizer_lite.tok list
(** Expand to fixed point, then tokenise the result. *)
