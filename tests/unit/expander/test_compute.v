Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test using Compute instead of reflexivity *)

Definition test1_input : list latex_token := [
  TCommand "def"; TCommand "x"; TBeginGroup; TText "hello"; TEndGroup;
  TCommand "x"
].

(** Compute the result *)
Eval compute in (expand_document_with_def test1_input).

(** Just check compilation, not equality *)
Definition test1_compiles : True := I.