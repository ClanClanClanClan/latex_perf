(** Simple LaTeX control-sequence expander with configurable stripping rules.

    Supports two modes:
    - Legacy: strip a fixed list of commands (backward compatible)
    - Catalogue: delegate to {!Latex_parse_lib.Macro_catalogue.expand} for full
      v25r2 + argsafe expansion *)

type cfg = {
  strip_controls : string list;
  bfseries_until_brace : bool;
  catalogue : Latex_parse_lib.Macro_catalogue.catalogue option;
}

val default : cfg
(** Default configuration: strips [textbf], [emph], [section]; handles
    [bfseries]. No catalogue loaded. *)

val of_json : Yojson.Safe.t -> cfg
(** Parse a configuration from JSON, falling back to {!default} on error. Does
    not load a catalogue. *)

val of_catalogue : Latex_parse_lib.Macro_catalogue.catalogue -> cfg
(** Create a configuration that delegates to the given macro catalogue. *)

val with_catalogue :
  cfg -> Latex_parse_lib.Macro_catalogue.catalogue option -> cfg
(** Override the catalogue in an existing configuration. *)

val expand_once : cfg -> string -> string
(** Single-pass expansion. In catalogue mode this is a no-op; use {!expand_fix}
    instead. *)

val expand_fix : cfg -> string -> string
(** Fixed-point expansion. In catalogue mode delegates to
    {!Latex_parse_lib.Macro_catalogue.expand}. *)

val expand_and_tokenize :
  cfg -> string -> string * Latex_parse_lib.Tokenizer_lite.tok list
(** Expand to fixed point, then tokenise the result. *)
