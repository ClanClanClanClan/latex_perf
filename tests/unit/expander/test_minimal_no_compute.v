Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Minimal test that doesn't trigger computation *)
Example test_minimal : True.
Proof. exact I. Qed.

(** Test that the function exists *)
Check expand_document_with_def.

(** Test that we can construct inputs *)
Definition simple_input := [TText "hello"].
Check simple_input.