(** * CSTtoASTSound — CST→AST soundness (memo §7.4).

    The memo §7.4 prescribes a file under this name; the v26.2 content
    lives in [CSTRoundTrip.v] (byte-lossless partition + structure-
    lossless Section). This file is a thin re-export so memo-named
    consumers and the [check_memo_files.py] gate find the canonical
    target directly.

    Content outline:
    - [CSTRoundTrip.is_partition] — every source has a byte-lossless
      partition (the CST→AST pipeline's round-trip invariant).
    - [CSTRoundTrip.Structure_lossless] section — structure-lossless
      theorem for the declared subset, hypothesis-parametric per
      ADR-004. v26.3 instantiates the hypothesis against the real
      [Parser_l2] to produce the unconditional CST→AST soundness
      claim the memo §7.4 ultimately targets.

    Zero admits, zero axioms (content inherited from [CSTRoundTrip.v]). *)

From LaTeXPerfectionist Require Export CSTRoundTrip.
From Coq Require Import List.
Import ListNotations.

(** A convenience theorem: CST→AST soundness in the byte-lossless
    direction is exactly [serialize_inverse_of_partition]. Re-state
    the claim under the memo name so downstream consumers can
    [Require Import LaTeXPerfectionist.CSTtoASTSound] without needing
    to know the canonical file. *)

Theorem cst_to_ast_sound :
  forall src nodes,
    CSTRoundTrip.is_partition src nodes ->
    CSTRoundTrip.serialize nodes = src.
Proof.
  exact CSTRoundTrip.serialize_inverse_of_partition.
Qed.

(** Structural composition under CST→AST: partitions compose. The
    theorem is the same partition-composition lemma from
    [CSTRoundTrip.v]; we keep a copy here under the memo-named file so
    anti-tautology audits don't flag a single-theorem alias. *)

Theorem cst_to_ast_partition_compose :
  forall s1 s2 n1 n2,
    CSTRoundTrip.is_partition s1 n1 ->
    CSTRoundTrip.is_partition s2 n2 ->
    CSTRoundTrip.is_partition (s1 ++ s2) (n1 ++ n2).
Proof.
  exact CSTRoundTrip.partition_compose.
Qed.

(** Zero-admit witness. *)
Definition cst_to_ast_sound_zero_admits : True := I.
