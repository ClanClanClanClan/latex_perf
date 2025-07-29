(**
   LaTeX Perfectionist v25 - OCaml Extraction
   
   This file extracts the verified Coq implementations to OCaml.
   This replaces the stub implementations with formally verified code.
*)

Require Import lexer.LatexCatcodes.
Require Import lexer.LatexLexer.
Require Import lexer.IncrementalLatexLexer.
Require Import expander.ExpanderTypes.
Require Import expander.MacroCatalog.
Require Import expander.ExpanderAlgorithm.

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Configure extraction *)
Extraction Language OCaml.

(* Extract key lexer functions - start simple *)
Extraction "extracted_lexer.ml" 
  LatexLexer.lex
  LatexLexer.lex_from_string.