From Coq Require Import List.
Import ListNotations.

Inductive brace : Type := L | R.

Fixpoint balanced (xs : list brace) : bool :=
  match xs with
  | []    => true
  | L :: r =>
      match r with
      | R :: r' => balanced r'
      | _       => false
      end
  | R :: _ => false
  end.

Lemma balanced_lr : balanced [L;R] = true.
Proof. reflexivity. Qed.