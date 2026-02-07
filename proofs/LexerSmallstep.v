(* A tiny small-step model to anchor determinism/totality statements for L0.
   Deliberately minimal and free of manual admits so the CI stays clean. *)

From Coq Require Import List String Arith Lia.
Import ListNotations.

Module L0.

  (* Simplified input as a list of bytes (nat 0..255) and an output tape of tokens (nat). *)
  Record state := { inp : list nat; out : list nat }.

  (* A single reduction consumes one byte and appends a token = that byte (toy model). *)
  Inductive step : state -> state -> Prop :=
  | Step_consume : forall b rest out,
      b < 256 ->
      step {| inp := b :: rest; out := out |}
           {| inp := rest; out := out ++ [b] |}.

  (* Determinism: one state has at most one next state. *)
  Theorem step_deterministic : forall s s1 s2,
    step s s1 -> step s s2 -> s1 = s2.
  Proof.
    intros [inp out] s1 s2 H1 H2.
    destruct inp as [|b rest]; inversion H1.
    inversion H1; inversion H2; subst; reflexivity.
  Qed.

  (* Totality-on-nonempty: if input is nonempty, a step exists. *)
  Theorem step_total_nonempty : forall s,
    s.(inp) <> [] ->
    Forall (fun b => b < 256) s.(inp) ->
    exists s', step s s'.
  Proof.
    intros [i o] Hne Hall.
    destruct i as [|b rest]; [contradiction|].
    inversion Hall; subst.
    exists {| inp := rest; out := o ++ [b] |}.
    constructor; assumption.
  Qed.

End L0.
