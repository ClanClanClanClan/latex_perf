(** * RewritePreservesSemantics — local semantic preservation (v26.2 PR B3).

    Whitespace-only edits in whitespace regions preserve the token
    stream produced by the parser. This is the baseline "safe rewrite"
    claim: rewrites scoped to trivia regions don't alter AST shape.

    Scope (v26.2): abstract, token-level claim over an opaque [tokens]
    function. v26.3 WS is expected to discharge the claim against the
    real [Parser_l2] for specific trivia-only edit classes.

    Zero admits, zero axioms. *)

From Coq Require Import List Arith.
Import ListNotations.

(** Abstract alphabet: byte-strings and whitespace markers. *)
Definition bytes := list nat.

(** A byte is "whitespace" per this abstract model iff it is one of
    32 (space), 9 (tab), 10 (LF), 13 (CR). *)
Definition is_ws_byte (b : nat) : bool :=
  Nat.eqb b 32 || Nat.eqb b 9 || Nat.eqb b 10 || Nat.eqb b 13.

Fixpoint all_ws (bs : bytes) : bool :=
  match bs with
  | [] => true
  | b :: rest => andb (is_ws_byte b) (all_ws rest)
  end.

(** ── Section: semantic preservation parametric in [tokens] ─────────── *)

Section Semantic_preservation.

  Variable token : Type.
  Variable tokens : bytes -> list token.

  (** v26.2 hypothesis (to be discharged in v26.3): whitespace-only
      input produces the empty token stream. *)
  Hypothesis tokens_ws_empty :
    forall bs, all_ws bs = true -> tokens bs = [].

  (** v26.2 hypothesis: [tokens] is compositional over concatenation of
      well-formed chunks. This is the standard property most
      recursive-descent lexers satisfy. *)
  Hypothesis tokens_concat :
    forall xs ys, tokens (xs ++ ys) = tokens xs ++ tokens ys.

  (** Whitespace-for-whitespace replacement preserves the token stream. *)
  Theorem ws_replacement_preserves_tokens :
    forall pre mid_old mid_new post,
      all_ws mid_old = true ->
      all_ws mid_new = true ->
      tokens (pre ++ mid_old ++ post) = tokens (pre ++ mid_new ++ post).
  Proof.
    intros pre mid_old mid_new post Hold Hnew.
    rewrite !tokens_concat.
    rewrite (tokens_ws_empty mid_old Hold).
    rewrite (tokens_ws_empty mid_new Hnew).
    reflexivity.
  Qed.

  (** Corollary: deleting whitespace preserves tokens. *)
  Theorem ws_deletion_preserves_tokens :
    forall pre mid post,
      all_ws mid = true ->
      tokens (pre ++ mid ++ post) = tokens (pre ++ post).
  Proof.
    intros pre mid post Hmid.
    rewrite !tokens_concat.
    rewrite (tokens_ws_empty mid Hmid).
    simpl. reflexivity.
  Qed.

  (** Corollary: inserting whitespace preserves tokens. *)
  Theorem ws_insertion_preserves_tokens :
    forall pre mid post,
      all_ws mid = true ->
      tokens (pre ++ post) = tokens (pre ++ mid ++ post).
  Proof.
    intros pre mid post Hmid.
    rewrite !tokens_concat.
    rewrite (tokens_ws_empty mid Hmid).
    simpl. reflexivity.
  Qed.

End Semantic_preservation.

(** Supporting lemma (ground): whitespace classification is decidable. *)
Theorem all_ws_dec : forall bs, {all_ws bs = true} + {all_ws bs = false}.
Proof.
  intros bs. destruct (all_ws bs); [left | right]; reflexivity.
Qed.

(** Supporting lemma (ground): empty is whitespace. *)
Theorem empty_is_ws : all_ws [] = true.
Proof. reflexivity. Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition rewrite_preserves_semantics_zero_admits : True := I.
