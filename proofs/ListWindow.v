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

  Lemma firstn_skipn_middle_list : forall (pre mid post : list A),
    firstn (length mid)
      (skipn (length pre) (pre ++ mid ++ post)) = mid.
  Proof.
    induction pre as [|x pre IH]; intros mid post; simpl.
    - now apply firstn_length_append.
    - rewrite app_assoc.
      simpl.
      rewrite <- app_assoc.
      apply IH.
  Qed.

  Lemma skipn_add : forall m n (xs : list A),
    skipn (m + n) xs = skipn n (skipn m xs).
  Proof.
    induction m as [|m IH]; intros n xs; simpl.
    - reflexivity.
    - destruct xs as [|x xs']; simpl.
      + now rewrite skipn_nil.
      + apply IH.
  Qed.

  Lemma firstn_add : forall off len (xs : list A),
    firstn (off + len) xs = firstn off xs ++ firstn len (skipn off xs).
  Proof.
    induction off as [|off IH]; intros len xs; simpl.
    - reflexivity.
    - destruct xs as [|x xs]; simpl; [now rewrite firstn_nil|].
      rewrite IH.
      reflexivity.
  Qed.

  Lemma decompose_firstn_skipn : forall off len (xs : list A),
    xs = firstn off xs ++ firstn len (skipn off xs) ++ skipn (off + len) xs.
  Proof.
    intros off len xs.
    rewrite <- firstn_skipn with (l:=xs) (n:=off) at 1.
    apply (List.app_inv_head (firstn off xs)).
    rewrite skipn_add.
    rewrite firstn_skipn with (l:=skipn off xs) (n:=len).
    reflexivity.
  Qed.
End Window.
