From Coq Require Import List Arith.
Import ListNotations.

(* A small, faithful-shaped step relation for L0: consumes one input byte
   and appends a token computed by a fixed classifier.  This mirrors the
   SoA update shape (advance input cursor; append one token) while remaining
   model-agnostic and admit-free. *)

Module L0F.

  Definition byte := nat.
  Definition token := nat.

  Record state := { inp : list byte; out : list token }.

  (* Fixed classifier for a byte to a token id (total, deterministic). *)
  Definition classify (b:byte) : token := b mod 256.

  Inductive step : state -> state -> Prop :=
  | Step : forall b rest out,
      b < 256 ->
      step {| inp := b :: rest; out := out |}
           {| inp := rest; out := out ++ [classify b] |}.

  Theorem step_deterministic : forall s s1 s2,
    step s s1 -> step s s2 -> s1 = s2.
  Proof. intros s s1 s2 H1 H2; inversion H1; inversion H2; subst; reflexivity. Qed.

  Theorem step_progress : forall s,
    s.(inp) <> [] -> exists s', step s s'.
  Proof.
    intros [i o] Hne. destruct i as [|b rest]; [contradiction|].
    exists {| inp := rest; out := o ++ [classify b] |}. constructor; lia.
  Qed.

End L0F.

