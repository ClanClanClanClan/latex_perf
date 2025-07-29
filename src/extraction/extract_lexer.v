(** Extraction configuration for L0 Lexer *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Coq.extraction.Extraction.

(* Import the lexer *)
Require Import Lexer.

(* Set extraction options *)
Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction Conservative Types.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(* Map Coq types to OCaml types *)
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive prod => "(*)" ["(,)"].
Extract Inductive option => "option" ["None" "Some"].
Extract Inductive nat => "int" ["0" "succ"] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Map Coq strings to OCaml strings *)
Extract Inductive string => "string" ["""""" "(^)"].
Extract Inductive ascii => "char".

(* Extract token type to match our OCaml definition *)
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

(* Functions to extract *)
Extraction "lexer_extracted.ml" 
  initial_state
  lex_char
  lex_string
  lex_string_incremental
  flush_buffer
  token.  (* Include the token type *)