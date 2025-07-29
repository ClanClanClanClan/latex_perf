(** * OCaml Extraction for LaTeX Lexer
    
    This file configures the extraction of our verified Coq lexer
    to efficient OCaml code for integration with the validation system.
*)

Require Import Lexer.
Require Import Extraction.

(** * Extraction Language *)
Extraction Language OCaml.

(** * Main extraction - let Coq handle the details *)
Recursive Extraction latex_tokenize.