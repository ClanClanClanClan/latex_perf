(* LaTeX Perfectionist v24 - Incremental Lexer Extraction *)
(* Properly extracts the incremental lexing algorithm to OCaml *)

From Coq Require Import Bool Arith List String Ascii ZArith.
From Coq Require Import Extraction.
Require Import lexer.LatexLexer.
Require Import lexer.LatexCatcodes.
Require Import lexer.IncrementalLatexLexer.
Import ListNotations.
Open Scope string_scope.

(** * Extraction Configuration *)

Extraction Language OCaml.

(* Extract the main incremental lexing functions *)
Extract Constant incremental_lex => "IncrementalLexer.incremental_lex".
Extract Constant initial_lex_with_checkpoints => "IncrementalLexer.initial_lex_with_checkpoints".

(* Extract checkpoint operations *)
Extract Constant find_checkpoint_before => "IncrementalLexer.find_checkpoint_before".
Extract Constant create_checkpoint => "IncrementalLexer.create_checkpoint".

(** * Main Extraction *)

Extraction "incremental_lexer.ml"
  lex_incremental
  lex_document_with_checkpoints
  checkpoint_state
  edit_operation
  incremental_result
  find_checkpoint_before
  create_checkpoint.