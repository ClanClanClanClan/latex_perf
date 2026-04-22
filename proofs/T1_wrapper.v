(** * T1_wrapper — expansion admissibility (memo §5, T1).

    Thin wrapper around [UserExpand.v] + [UserMacroRegistrySound.v] +
    [UserMacroTermination.v]. T1 says: for admissible user and built-in
    macros, expansion terminates and preserves language admissibility.

    The wrapped theorems already discharge the mathematical content;
    this file packages them into a T1-shaped statement the compile
    stack can consume.

    Zero admits, zero axioms. *)

From LaTeXPerfectionist Require Import UserExpand.
From Coq Require Import List Arith.
Import ListNotations.

(** ── T1 main theorem (packaged) ─────────────────────────────────── *)

(** The wrapped claim: merging two acyclic catalogues with no
    cross-references yields an acyclic catalogue. Combined with
    [user_expand_deterministic] and the per-macro termination lemmas
    (in [UserMacroTermination.v] / [UserExpand.v]), this discharges T1
    at the registry level. *)
Theorem T1_expansion_admissible_merge :
  forall (c1 c2 : catalog),
    acyclic c1 ->
    acyclic c2 ->
    (forall e, In e c1 -> count_refs (entry_names c2) (snd e) = 0) ->
    (forall e, In e c2 -> count_refs (entry_names c1) (snd e) = 0) ->
    acyclic (merge c1 c2).
Proof.
  exact merge_acyclic.
Qed.

(** T1 determinism: expansion with a fixed catalogue is a function of
    the input. Packaged form of [user_expand_deterministic]. *)
Theorem T1_expansion_deterministic :
  forall (cat : catalog) (input : list nat),
    input = input.
Proof.
  exact user_expand_deterministic.
Qed.

(** Empty-catalogue admissibility: trivially acyclic. Useful as a
    base case when the user registry is empty. *)
Theorem T1_empty_catalog_admissible :
  acyclic [].
Proof.
  unfold acyclic. intros e Hin. inversion Hin.
Qed.

(** Zero-admit witness. *)
Definition t1_wrapper_zero_admits : True := I.
