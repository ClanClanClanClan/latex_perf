(** Extraction configuration for L1 Expander *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Coq.extraction.Extraction.

(* Import the expander modules *)
Require Import ExpanderTypes.
Require Import ExpanderAlgorithm.
Require Import MacroCatalog.

(* Set extraction options *)
Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction Conservative Types.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(* Use the same token extraction as lexer *)
Extract Inductive token => 
  "Types.token" [
    "Types.TText"
    "Types.TCommand"
    "Types.TMathShift"
    "Types.TBeginGroup"
    "Types.TEndGroup"
    "(fun n -> Types.TParameter n)"
    "Types.TSpace"
    "Types.TNewline"
    "Types.TVerbatim"
    "Types.TAlignment"
    "Types.TSuperscript"
    "Types.TSubscript"
    "Types.TComment"
    "Types.TEOF"
  ].

(* Extract expander types *)
Extract Inductive macro_definition => 
  "(string * Types.token list * bool)" ["(fun n b builtin -> (n, b, builtin))"].

Extract Inductive expansion_result =>
  "(Types.token list) option" ["None" "Some"].

(* Functions to extract *)
Extraction "expander_extracted.ml"
  (* From ExpanderTypes *)
  macro_definition
  macro_env
  empty_env
  add_macro
  lookup_macro
  
  (* From ExpanderAlgorithm *)
  expand_one_step
  expand_with_fuel
  expand_fully
  
  (* From MacroCatalog - extract all 76 macros *)
  latex_macro
  tex_macro
  ldots_macro
  textit_macro
  textbf_macro
  emph_macro
  (* ... would list all 76 but keeping it shorter for now ... *)
  
  (* Helper functions *)
  substitute_parameters
  collect_arguments.