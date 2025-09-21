(* A tiny small-step model to anchor determinism/totality statements for L0.
   This is deliberately minimal and admit-free to keep CI zero-admit. *)

From Coq Require Import List String Arith.
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
    intros s s1 s2 H1 H2. inversion H1; inversion H2; subst; auto.
  Qed.

  (* Totality-on-nonempty: if input is nonempty, a step exists. *)
  Theorem step_total_nonempty : forall s,
    s.(inp) <> [] -> exists s', step s s'.
  Proof.
    intros [i o] Hne. destruct i as [|b rest]; [contradiction|].
    exists {| inp := rest; out := o ++ [b] |}. constructor; lia.
  Qed.

End L0.

