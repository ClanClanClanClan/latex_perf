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

(* ========================================================================= *)
(* Stage 2 (FAITHFUL-SEMANTICS Tier 3): aux-state evolution.                  *)
(*                                                                            *)
(* pdflatex runs the document more than once because cross references         *)
(* (\ref -> \label) are resolved through an auxiliary (.aux) file that is     *)
(* only complete after a full pass.  We model the auxiliary bookkeeping as    *)
(* an [aux_state] that accumulates the set of DEFINED labels (\label{...})    *)
(* and the set of USED references (\ref{...}).  A "pass" folds the document's  *)
(* token stream through [aux_step_token].                                     *)
(*                                                                            *)
(* Faithfulness target: the SET of defined labels CONVERGES after the first   *)
(* pass.  Re-running the same document does not define any new label and does *)
(* not lose any previously-defined label; hence reference resolution is       *)
(* stable from the second pass on.  Note the subtlety flagged in the plan:    *)
(* [aux_step_token] PREPENDS, so the underlying [defined_labels] LIST grows   *)
(* on every pass (see [naive_list_eq_is_false] below).  Convergence is a fact *)
(* about the SET (membership), not the concrete list.                         *)
(* ========================================================================= *)

Module L0Aux.

  Inductive pdflatex_token :=
  | Tok_text
  | Tok_label_def (n : nat)
  | Tok_label_ref (n : nat).

  Record aux_state := mk_aux { defined_labels : list nat; used_refs : list nat }.

  (* One token's effect on the auxiliary state: a label definition prepends
     to [defined_labels], a reference prepends to [used_refs], plain text is
     inert. *)
  Definition aux_step_token (s : aux_state) (t : pdflatex_token) : aux_state :=
    match t with
    | Tok_label_def n => mk_aux (n :: defined_labels s) (used_refs s)
    | Tok_label_ref n => mk_aux (defined_labels s) (n :: used_refs s)
    | Tok_text        => s
    end.

  (* One full pass: fold every token of the document through [aux_step_token]. *)
  Fixpoint aux_step_pass (s : aux_state) (toks : list pdflatex_token) : aux_state :=
    match toks with
    | []          => s
    | t :: rest   => aux_step_pass (aux_step_token s t) rest
    end.

  Definition empty_aux : aux_state := mk_aux [] [].

  (* The multiset (here: list) of labels a token stream defines, in the plain
     document order.  This is the intended "specification" of the definitions
     a single pass contributes, independent of the prepend/order artefacts of
     [aux_step_token]. *)
  Fixpoint collect_defs (toks : list pdflatex_token) : list nat :=
    match toks with
    | []                     => []
    | Tok_label_def n :: rest => n :: collect_defs rest
    | _ :: rest               => collect_defs rest
    end.

  (* Membership characterisation of the labels defined after a pass: a pass
     from state [s] defines exactly the labels [s] already had, plus the
     labels [collect_defs toks] the document contributes.  Proof folds over
     the token stream with [s] generalised. *)
  Lemma pass_defined_iff :
    forall toks s n,
      In n (defined_labels (aux_step_pass s toks))
      <-> In n (collect_defs toks) \/ In n (defined_labels s).
  Proof.
    induction toks as [|t rest IH]; intros s n; simpl.
    - (* empty pass: defined set unchanged *)
      split; [intro H; right; exact H | intros [[] | H]; exact H].
    - destruct t as [| m | m]; simpl.
      + (* Tok_text: inert *)
        apply IH.
      + (* Tok_label_def m: prepends m *)
        rewrite IH; simpl. tauto.
      + (* Tok_label_ref m: defined set unchanged *)
        rewrite IH. tauto.
  Qed.

  (* KEY LEMMA — 2-pass convergence of the defined-label SET.

     Running the same document a second time (starting from the state that the
     first pass produced) yields exactly the same SET of defined labels as the
     first pass: for every label id [n], [n] is defined after pass 2 iff it is
     defined after pass 1.  This is the faithful statement of pdflatex's
     "definitions converge after the first pass" property, and it is precisely
     the invariant that makes \ref resolution stable from pass 2 onward.

     It is NON-VACUOUS: [defined_labels] is inhabited exactly when the document
     contains \label tokens (see [collect_defs]); the corresponding raw
     list-equality is FALSE because the list keeps growing
     (see [naive_list_eq_is_false]).  The content is in the SET stabilising. *)
  Theorem aux_pass_stable_after_2 :
    forall toks n,
      In n (defined_labels (aux_step_pass (aux_step_pass empty_aux toks) toks))
      <-> In n (defined_labels (aux_step_pass empty_aux toks)).
  Proof.
    intros toks n.
    rewrite (pass_defined_iff toks (aux_step_pass empty_aux toks) n).
    rewrite (pass_defined_iff toks empty_aux n).
    unfold empty_aux; simpl.
    (* both sides reduce to [In n (collect_defs toks)] *)
    tauto.
  Qed.

  (* Companion: the naive list-level idempotence is genuinely FALSE, which is
     why the convergence theorem is stated at the SET level.  A second pass
     over a document with one label duplicates that label in the list. *)
  Example naive_list_eq_is_false :
    aux_step_pass (aux_step_pass empty_aux [Tok_label_def 0]) [Tok_label_def 0]
    <> aux_step_pass empty_aux [Tok_label_def 0].
  Proof.
    simpl. intro H. inversion H.
  Qed.

  (* And the SET-level theorem does hold on that same witness, confirming the
     statement is not vacuously true. *)
  Example stable_on_witness :
    In 0 (defined_labels
            (aux_step_pass (aux_step_pass empty_aux [Tok_label_def 0])
                           [Tok_label_def 0]))
    <-> In 0 (defined_labels (aux_step_pass empty_aux [Tok_label_def 0])).
  Proof. apply aux_pass_stable_after_2. Qed.

End L0Aux.
