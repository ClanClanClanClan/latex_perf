Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(* Test error handling for malformed \def *)
Definition test_malformed_def := [
  TCommand "def"; TText "missing_braces"; TText "#1"
].

Compute expand_document_with_errors test_malformed_def.

(* Test error handling for missing arguments *)
Definition test_missing_args := [
  TCommand "textbf"  (* missing required argument *)
].

Compute expand_document_with_errors test_missing_args.

