(** * InterpLocality — diff algebra locality (spec W59) *)

From Coq Require Import List Bool Arith.
Import ListNotations.

Record region := mk_region { rstart : nat; rend : nat }.

Definition independent (r1 r2 : region) : bool :=
  Nat.leb (rend r1) (rstart r2) || Nat.leb (rend r2) (rstart r1).

Theorem independent_symmetric :
  forall r1 r2, independent r1 r2 = independent r2 r1.
Proof.
  intros r1 r2. unfold independent. rewrite Bool.orb_comm. reflexivity.
Qed.

Theorem disjoint_no_overlap :
  forall r1 r2,
    independent r1 r2 = true ->
    rend r1 <= rstart r2 \/ rend r2 <= rstart r1.
Proof.
  intros r1 r2 H. unfold independent in H.
  apply Bool.orb_true_iff in H. destruct H.
  - left. apply Nat.leb_le. exact H.
  - right. apply Nat.leb_le. exact H.
Qed.

Definition interp_locality_zero_admits : True := I.
