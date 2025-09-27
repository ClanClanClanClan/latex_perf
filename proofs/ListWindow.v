From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Window.
  Variable A : Type.

  Lemma firstn_length_append : forall (xs ys : list A),
    firstn (length xs) (xs ++ ys) = xs.
  Proof.
    induction xs as [|x xs IH]; intros ys; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma skipn_length_append : forall (xs ys : list A),
    skipn (length xs) (xs ++ ys) = ys.
  Proof.
    induction xs as [|x xs IH]; intros ys; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma firstn_skipn_length : forall (xs ys : list A),
    firstn (length xs) (xs ++ ys) ++ skipn (length xs) (xs ++ ys) = xs ++ ys.
  Proof.
    intros; now rewrite firstn_length_append, skipn_length_append.
  Qed.
End Window.
