(** * LabelsUnique — label uniqueness detection (spec W53-57) *)

From Coq Require Import List Bool Arith PeanoNat.
Import ListNotations.

Definition count_occ (key : nat) (labels : list nat) : nat :=
  List.length (List.filter (Nat.eqb key) labels).

Definition has_dup (key : nat) (labels : list nat) : bool :=
  Nat.ltb 1 (count_occ key labels).

Theorem empty_no_dup : forall k, has_dup k nil = false.
Proof. reflexivity. Qed.

Theorem single_no_dup : forall k, has_dup k (k :: nil) = false.
Proof.
  intro k. unfold has_dup, count_occ.
  replace (filter (Nat.eqb k) (k :: nil)) with (k :: @nil nat)
    by (simpl; rewrite Nat.eqb_refl; reflexivity).
  reflexivity.
Qed.

Theorem pair_dup : forall k, has_dup k (k :: k :: nil) = true.
Proof.
  intro k. unfold has_dup, count_occ.
  replace (filter (Nat.eqb k) (k :: k :: nil)) with (k :: k :: @nil nat)
    by (simpl; repeat rewrite Nat.eqb_refl; reflexivity).
  reflexivity.
Qed.

Definition labels_unique_zero_admits : True := I.
