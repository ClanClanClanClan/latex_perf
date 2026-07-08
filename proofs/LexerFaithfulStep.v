From Coq Require Import List Arith Lia.
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
  Proof.
    intros [inp out] s1 s2 H1 H2.
    destruct inp as [|b rest]; inversion H1.
    inversion H1; inversion H2; subst; reflexivity.
  Qed.

  Theorem step_progress : forall s,
    s.(inp) <> [] ->
    Forall (fun b => b < 256) s.(inp) ->
    exists s', step s s'.
  Proof.
    intros [i o] Hne Hall.
    destruct i as [|b rest]; [contradiction|].
    inversion Hall; subst.
    exists {| inp := rest; out := o ++ [classify b] |}.
    constructor; assumption.
  Qed.

  (* Stage 1 (FAITHFUL-SEMANTICS Tier 3): a total tokenizer over a byte
     list.  It is the batch (whole-input) analogue of [step]: exactly one
     token is produced per input byte, via the same fixed [classify].
     Being defined as [map classify] it is manifestly total and every byte
     maps to exactly one token — the 1-byte -> 1-token faithfulness the plan
     calls for. *)
  Fixpoint tokenize (bs : list byte) : list token :=
    match bs with
    | [] => []
    | b :: rest => classify b :: tokenize rest
    end.

  (* [tokenize] agrees with the point-free [map classify] specification. *)
  Lemma tokenize_is_map : forall bs, tokenize bs = map classify bs.
  Proof.
    induction bs as [|b rest IH]; simpl; [reflexivity|].
    rewrite IH; reflexivity.
  Qed.

  (* Byte -> token count faithfulness: one token out per byte in. *)
  Theorem tokenize_preserves_byte_count :
    forall bs, length (tokenize bs) = length bs.
  Proof.
    induction bs as [|b rest IH]; simpl; [reflexivity|].
    rewrite IH; reflexivity.
  Qed.

End L0F.
