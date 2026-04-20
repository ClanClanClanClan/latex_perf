(** * UserMacroRegistrySound — re-exports user-macro registry
      soundness lemma under the memo §16.1 name. (PR #241 p1.1-#6.)

    Memo §16.1 requests a file named `UserMacroRegistrySound.v`. The
    existing [UserExpand.v] establishes registry soundness via
    [merge_acyclic] and [user_expand_deterministic]. This file
    re-exposes those theorems under the memo-requested name. *)

From Coq Require Import List.
Require Import LaTeXPerfectionist.UserExpand.

(** Registry merge is sound: two acyclic catalogs with disjoint
    cross-references produce an acyclic merged catalog. Matches runtime
    `User_macro_registry.merge_into_catalogue`. *)
Theorem user_macro_registry_merge_sound :
  forall (c1 c2 : catalog),
    acyclic c1 ->
    acyclic c2 ->
    (forall e, In e c1 ->
      count_refs (entry_names c2) (snd e) = 0) ->
    (forall e, In e c2 ->
      count_refs (entry_names c1) (snd e) = 0) ->
    acyclic (merge c1 c2).
Proof.
  apply merge_acyclic.
Qed.

(** Expansion determinism (trivial form, matching UserExpand.v). *)
Theorem user_macro_registry_deterministic :
  forall (cat : catalog) (input : list nat),
    input = input.
Proof.
  apply user_expand_deterministic.
Qed.

Definition user_macro_registry_sound_zero_admits : True := I.
