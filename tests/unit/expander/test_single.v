Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Single test to debug timeout *)
Example test_single :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "x"; TBeginGroup; TText "hi"; TEndGroup;
    TCommand "x"
  ] in
  output = [TText "hi"].
Proof. reflexivity. Qed.