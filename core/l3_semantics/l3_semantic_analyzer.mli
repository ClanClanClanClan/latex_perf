(* L3 Semantic Analyzer Interface - LaTeX Perfectionist v25 *)

open Data
open Lexer_v25

type semantic_context
(** Semantic context tracking *)

(** Warning levels for semantic issues *)
type warning_level = Hint | Info | Warning

(** Error severity levels *)
type error_severity = Minor | Major | Critical

type semantic_warning = {
  level : warning_level;
  message : string;
  location : Location.t;
  suggestion : string option;
}
(** Semantic warning information *)

type semantic_error = {
  severity : error_severity;
  message : string;
  location : Location.t;
  fix : string option;
}
(** Semantic error information *)

(** Document structure analysis *)
module DocumentStructure : sig
  type section_info = {
    level : int;
    title : string;
    label : string option;
    location : Location.t;
    word_count : int;
  }

  type document_outline = {
    sections : section_info list;
    max_depth : int;
    total_sections : int;
    avg_section_length : float;
  }

  val analyze_structure : token array -> document_outline
end

(** Math mode analysis *)
module MathAnalyzer : sig
  type math_context = Inline | Display | Equation | Align | Gather

  type math_issue =
    | EmptyMath
    | NestedMath
    | UnclosedMath
    | InvalidCommand of string
    | MixedNotation

  val analyze_math_mode : token array -> math_issue list
end

(** Cross-reference analysis *)
module CrossReferences : sig
  type ref_type =
    | Label of string
    | Ref of string
    | PageRef of string
    | Cite of string
    | FootnoteRef of int

  type ref_issue =
    | UndefinedReference of string
    | DuplicateLabel of string
    | UnusedLabel of string
    | ForwardReference of string * int

  val analyze_references : token array -> ref_issue list
end

val create_context : unit -> semantic_context
(** Create initial semantic context *)

val analyze_semantics :
  semantic_context ->
  token array ->
  semantic_context * DocumentStructure.document_outline
(** Perform semantic analysis on token stream *)

val validate_document : token array -> semantic_context * string
(** High-level document validation *)
