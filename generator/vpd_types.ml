(* VPD Types — Validator-Producing DSL core types *)

(** Severity level for a rule *)
type severity = Error | Warning | Info

(** Precondition layer *)
type layer = L0_Lexer | L1_Expanded | L2_Ast | L3_Semantics | L4_Style

(** Detection pattern family. Each family corresponds to a code-generation
    template. *)
type pattern =
  | Count_char of char  (** Count occurrences of a single byte. *)
  | Count_char_strip_math of char
      (** Like [Count_char] but strip math segments first. *)
  | Count_substring of string
      (** Count occurrences of a substring (with overlap). *)
  | Count_substring_strip_math of string
      (** Like [Count_substring] but strip math segments first. *)
  | Multi_substring of string list
      (** Sum of [count_substring] over several needles. *)
  | Multi_substring_strip_math of string list
      (** Like [Multi_substring] but strip math first. *)
  | Char_range of { lo : int; hi : int; exclude : int list }
      (** Scan for bytes whose code falls in [lo..hi], excluding listed codes. *)
  | Regex of string
      (** Match an OCaml [Str] regex; count via [Str.search_forward] loop. *)
  | Line_pred of string  (** Name of a predefined line predicate function. *)
  | Custom of string
      (** Opaque body: verbatim OCaml expression of type [string -> int]. *)

type rule_spec = {
  id : string;  (** e.g. "TYPO-034" *)
  description : string;  (** Human description from rules_v3.yaml *)
  layer : layer;
  severity : severity;
  message : string;  (** Exact message string for the result *)
  pattern : pattern;  (** Detection pattern family + parameters *)
}
(** A single VPD rule specification *)

type manifest = { version : string; rules : rule_spec list }
(** A complete VPD manifest *)
