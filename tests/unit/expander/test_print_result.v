Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

Definition test_input : list latex_token := [
  TCommand "def"; TCommand "x"; TBeginGroup; TText "hi"; TEndGroup;
  TCommand "x"
].

(** Print the actual result *)
Eval vm_compute in (expand_document_with_def test_input).