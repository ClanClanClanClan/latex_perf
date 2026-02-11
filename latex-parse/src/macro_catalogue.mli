(** Production L1 macro expander with v25r2 + argsafe catalogue support.

    Loads 441 symbol macros (arity-0, Unicode expansions) and 62 argumentful
    macros (epsilon-safe templates) from JSON catalogues. Performs mode-aware
    expansion with bounded iteration (max 256 rounds).

    Symbol categories: Greek letters, math operators, arrows, delimiters, text
    symbols, spacing, font-size switches, named math operators,
    formatting/alignment switches.

    Argumentful categories: text style (NFSS), math style, math alphabets, math
    accents, sectioning, references, document metadata, builtins. *)

(** {1 Token types} *)

type token = TText of string | TOp of string | TDelim of string

val token_to_string : token -> string
(** Extract the string payload from any token variant. *)

(** {1 Catalogue types} *)

type mode = Math | Text | Any | Both

type symbol_entry = {
  name : string;
  mode : mode;
  expansion : token list;
  expand_in_math : bool;
  expand_in_text : bool;
}

type template = Inline of string | Builtin of string

type argsafe_entry = {
  name : string;
  mode : mode;
  category : string;
  positional : int;
  kinds : string list;
  template : template;
}

type entry = Symbol of symbol_entry | Argsafe of argsafe_entry

type catalogue
(** Opaque handle to the loaded macro catalogue (hash tables). *)

(** {1 Loading} *)

val load : v25r2_path:string -> argsafe_path:string -> catalogue
(** Load both catalogues from JSON files. Validates epsilon-safety for all
    argsafe entries at load time (warnings on stderr). *)

val load_v25r2 : string -> symbol_entry list
(** Parse the v25r2 JSON catalogue to a list of symbol entries. *)

val load_argsafe : string -> argsafe_entry list
(** Parse the argsafe JSON catalogue to a list of argumentful entries. *)

val create : symbol_entry list -> argsafe_entry list -> catalogue
(** Build a catalogue from pre-parsed entry lists. *)

(** {1 Query} *)

val symbol_count : catalogue -> int
(** Number of symbol (arity-0) entries. *)

val argsafe_count : catalogue -> int
(** Number of argumentful entries. *)

val lookup : catalogue -> string -> entry option
(** Look up a macro by name (without backslash). *)

(** {1 Expansion} *)

val expand : catalogue -> string -> string
(** Expand all known macros to fixed point (max 256 iterations). Tracks
    math/text context via [$], [$$], [\[], [\(] delimiters. *)

val expand_and_tokenize :
  catalogue -> string -> string * Tokenizer_lite.tok list
(** Expand to fixed point, then tokenise the result. *)

(** {1 Validation} *)

val validate_epsilon : argsafe_entry -> bool * string option
(** Check whether an argsafe entry passes epsilon-safety validation. *)
