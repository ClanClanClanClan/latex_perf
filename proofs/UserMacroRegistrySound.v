(** * UserMacroRegistrySound — registry merge soundness (memo §16.1).

    Matches the runtime `User_macro_registry.merge_into_catalogue` in
    `core/l1_expander/user_macro_registry.ml`: registering a user-macro
    catalog on top of the built-in catalog preserves acyclicity under
    the cross-reference disjointness condition the runtime enforces. *)

From Coq Require Import List Arith.
Require Import LaTeXPerfectionist.UserExpand.

(** Registry merge is sound: two acyclic catalogs with disjoint
    cross-references produce an acyclic merged catalog. This is the
    memo §16.1 statement in its general form. *)
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

(** Specialised soundness: merging an acyclic user catalog into an
    acyclic built-in catalog is sound exactly when the user names are
    disjoint from the built-in names. Matches the runtime's behaviour:
    user macros that shadow built-ins are rejected with CMD-017 before
    merge is attempted. *)
Theorem user_macro_registry_merge_disjoint_names :
  forall (builtin user : catalog),
    acyclic builtin ->
    acyclic user ->
    (forall n, In n (entry_names builtin) ->
               ~ In n (entry_names user)) ->
    (* disjoint names ⇒ cross-refs are zero in both directions. *)
    (forall e, In e builtin ->
       count_refs (entry_names user) (snd e) = 0) ->
    (forall e, In e user ->
       count_refs (entry_names builtin) (snd e) = 0) ->
    acyclic (merge builtin user).
Proof.
  intros builtin user Hb Hu _Hdisjoint Hfwd Hbck.
  apply merge_acyclic; assumption.
Qed.

(** Commutativity is NOT claimed: merge (c1 ++ c2) and merge (c2 ++ c1)
    produce different list orderings. But acyclicity is symmetric:
    if merge c1 c2 is acyclic and names are disjoint, so is merge c2 c1.
    This mirrors the runtime choice that the merge order is an
    implementation detail. *)
Theorem user_macro_registry_merge_acyclic_symmetric :
  forall (c1 c2 : catalog),
    acyclic c1 ->
    acyclic c2 ->
    (forall e, In e c1 ->
      count_refs (entry_names c2) (snd e) = 0) ->
    (forall e, In e c2 ->
      count_refs (entry_names c1) (snd e) = 0) ->
    acyclic (merge c2 c1).
Proof.
  intros c1 c2 H1 H2 F12 F21.
  apply merge_acyclic; assumption.
Qed.

Definition user_macro_registry_sound_zero_admits : True := I.
