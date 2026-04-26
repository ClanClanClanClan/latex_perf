(** * RewritePreservesSemanticsConcrete — concrete discharge of
      RewritePreservesSemantics.Section_preservation
      (v26.3.1 PR #3 of the §5 successor cycle).

    [proofs/RewritePreservesSemantics.v] proves token-level preservation of
    whitespace edits via a [Section Semantic_preservation] parametric over:
      - [token : Type]
      - [tokens : bytes -> list token]
    with two hypotheses ([tokens_ws_empty], [tokens_concat]) consumed
    together by the three in-section theorems.

    Per [proofs/ADMISSIBILITY_MAP.md], the v26.3.1 discharge target is to
    instantiate against a concrete tokenizer model on trivia-only chunks.

    The discharge lives here: [token := nat] (a non-whitespace byte) and
    [tokens := filter (negb ∘ is_ws_byte)]. With this instantiation:
      - [tokens_ws_empty] follows from `filter` returning [] on a list
        where every element fails the predicate.
      - [tokens_concat] is precisely the standard [filter_app] lemma.
    Both close the Section unconditionally.

    LIMITATION (intentional, see V26_3_1_PLAN.md §1.3 + ADMISSIBILITY_MAP).
    This concrete tokenizer is a byte-level filter; it does NOT model
    [Parser_l2]'s lookahead semantics (e.g., `\[`). The result is therefore
    a sound discharge for trivia-only edits at the byte level — exactly the
    surface the v26.3 [Cst_edit] rewrite engine touches in practice.
    Stronger discharge against the real [Parser_l2] is v27 WS7 work.

    Zero admits, zero axioms. *)

From Coq Require Import List Arith Bool.
From LaTeXPerfectionist Require Import RewritePreservesSemantics.
Import ListNotations.

(** Concrete carriers. *)
Definition token : Type := nat.

Definition tokens (bs : bytes) : list token :=
  filter (fun b => negb (is_ws_byte b)) bs.

(** ── Discharge of [tokens_ws_empty] ──────────────────────────────────── *)

(** [filter p xs = []] iff every element of [xs] fails [p]. We use the
    direction we need. *)
Lemma filter_negb_is_ws_empty :
  forall bs, all_ws bs = true ->
             filter (fun b => negb (is_ws_byte b)) bs = [].
Proof.
  induction bs as [|b rest IH]; intros Hall.
  - reflexivity.
  - simpl in Hall.
    apply Bool.andb_true_iff in Hall as [Hb Hrest].
    simpl. rewrite Hb. simpl. apply IH. exact Hrest.
Qed.

Lemma tokens_ws_empty_concrete :
  forall bs, all_ws bs = true -> tokens bs = [].
Proof.
  exact filter_negb_is_ws_empty.
Qed.

(** ── Discharge of [tokens_concat] ────────────────────────────────────── *)

Lemma filter_app :
  forall (A : Type) (p : A -> bool) (xs ys : list A),
    filter p (xs ++ ys) = filter p xs ++ filter p ys.
Proof.
  intros A p. induction xs as [|x rest IH]; intros ys.
  - reflexivity.
  - simpl. rewrite IH. destruct (p x); reflexivity.
Qed.

Lemma tokens_concat_concrete :
  forall xs ys, tokens (xs ++ ys) = tokens xs ++ tokens ys.
Proof.
  intros xs ys. unfold tokens. apply filter_app.
Qed.

(** ── Unconditional in-section theorems ──────────────────────────────── *)

(** Apply the Section to the concrete carriers. *)

Theorem ws_replacement_preserves_tokens_concrete :
  forall pre mid_old mid_new post,
    all_ws mid_old = true ->
    all_ws mid_new = true ->
    tokens (pre ++ mid_old ++ post) = tokens (pre ++ mid_new ++ post).
Proof.
  apply ws_replacement_preserves_tokens.
  - exact tokens_ws_empty_concrete.
  - exact tokens_concat_concrete.
Qed.

Theorem ws_deletion_preserves_tokens_concrete :
  forall pre mid post,
    all_ws mid = true ->
    tokens (pre ++ mid ++ post) = tokens (pre ++ post).
Proof.
  apply ws_deletion_preserves_tokens.
  - exact tokens_ws_empty_concrete.
  - exact tokens_concat_concrete.
Qed.

Theorem ws_insertion_preserves_tokens_concrete :
  forall pre mid post,
    all_ws mid = true ->
    tokens (pre ++ post) = tokens (pre ++ mid ++ post).
Proof.
  apply ws_insertion_preserves_tokens.
  - exact tokens_ws_empty_concrete.
  - exact tokens_concat_concrete.
Qed.

(** ── Sanity examples ────────────────────────────────────────────────── *)

Example tokens_keeps_non_ws :
  tokens [65; 32; 66] = [65; 66].
Proof. reflexivity. Qed.

Example tokens_drops_ws :
  tokens [9; 32; 10; 13] = [].
Proof. reflexivity. Qed.

Example replacement_example :
  tokens ([65] ++ [32; 32] ++ [66]) =
  tokens ([65] ++ [9] ++ [66]).
Proof.
  apply ws_replacement_preserves_tokens_concrete; reflexivity.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition rewrite_preserves_semantics_concrete_zero_admits : True := I.
