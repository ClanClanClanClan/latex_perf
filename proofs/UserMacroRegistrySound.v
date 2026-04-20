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

(** Bridge between [mem_nat] (decidable boolean membership) and [In]
    (propositional membership). Straightforward induction. *)
Lemma mem_nat_true_In : forall x l, mem_nat x l = true -> In x l.
Proof.
  intros x l. induction l as [|y ys IH]; simpl; intro H.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:Heq.
    + apply Nat.eqb_eq in Heq. left; symmetry; exact Heq.
    + right. apply IH. exact H.
Qed.

Lemma mem_nat_In_true : forall x l, In x l -> mem_nat x l = true.
Proof.
  intros x l. induction l as [|y ys IH]; simpl; intro H.
  - destruct H.
  - destruct H as [Heq | HIn].
    + subst. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb x y); auto.
Qed.

Lemma not_In_mem_nat_false : forall x l, ~ In x l -> mem_nat x l = false.
Proof.
  intros x l H. destruct (mem_nat x l) eqn:E; auto.
  exfalso. apply H. apply mem_nat_true_In. exact E.
Qed.

(** A body is "closed" under a name list when every reference it makes is
    to a name in that list. This is the runtime invariant enforced by
    [User_macro_registry.merge_into_catalogue]: macro bodies are normalised
    so that every name token resolves to a catalog entry (unresolved names
    are rejected before merge is attempted). *)
Definition body_closed (names : list nat) (body : list nat) : Prop :=
  forall x, In x body -> In x names.

Definition catalog_bodies_closed (cat : catalog) : Prop :=
  forall e, In e cat -> body_closed (entry_names cat) (snd e).

(** Bridging lemma: a body closed under [names1] has zero cross-references
    to any [names2] disjoint from [names1]. This is the only place the
    runtime's "names are disjoint" policy becomes load-bearing — without
    it the cross-ref hypotheses of [merge_acyclic] have to be given
    externally. *)
Lemma body_closed_disjoint_zero :
  forall (names1 names2 body : list nat),
    body_closed names1 body ->
    (forall n, In n names1 -> ~ In n names2) ->
    count_refs names2 body = 0.
Proof.
  intros names1 names2 body Hclosed Hdisj.
  induction body as [|x xs IH]; simpl; auto.
  assert (Hx_in1 : In x names1) by (apply Hclosed; left; reflexivity).
  assert (Hx_notin2 : ~ In x names2) by (apply Hdisj; exact Hx_in1).
  rewrite (not_In_mem_nat_false _ _ Hx_notin2). simpl.
  apply IH. intros y Hy. apply Hclosed. right. exact Hy.
Qed.

(** Specialised soundness: merging an acyclic user catalog into an
    acyclic built-in catalog is sound when the user names are disjoint
    from the built-in names AND both catalogs' bodies are closed under
    their own names. Matches the runtime's behaviour:
    - user macros that shadow built-ins are rejected with CMD-017
      (disjoint names)
    - unresolved references in macro bodies are rejected before merge
      (bodies closed) *)
Theorem user_macro_registry_merge_disjoint_names :
  forall (builtin user : catalog),
    acyclic builtin ->
    acyclic user ->
    catalog_bodies_closed builtin ->
    catalog_bodies_closed user ->
    (forall n, In n (entry_names builtin) ->
               ~ In n (entry_names user)) ->
    acyclic (merge builtin user).
Proof.
  intros builtin user Hb Hu Hcb Hcu Hdisjoint.
  apply merge_acyclic; try assumption.
  - intros e He.
    apply (body_closed_disjoint_zero (entry_names builtin) (entry_names user)).
    + exact (Hcb e He).
    + exact Hdisjoint.
  - intros e He.
    apply (body_closed_disjoint_zero (entry_names user) (entry_names builtin)).
    + exact (Hcu e He).
    + intros n Hn Hcontra. apply (Hdisjoint n Hcontra). exact Hn.
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
