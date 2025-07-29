Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test using vm_compute which is much faster *)

Definition test_input : list latex_token := [
  TCommand "def"; TCommand "x"; TBeginGroup; TText "hi"; TEndGroup;
  TCommand "x"
].

Definition test_result := Eval vm_compute in (expand_document_with_def test_input).

(** Now we can check the result *)
Example test_works : 
  match test_result with
  | ([TText "hi"], _) => True
  | _ => False
  end.
Proof. 
  unfold test_result.
  exact I.
Qed.