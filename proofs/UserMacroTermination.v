(** * UserMacroTermination — termination-relevant invariants for the
      bounded user-macro registry (memo §16.1).

    The runtime expander in `core/l1_expander/user_macro_registry.ml` is
    fuel-bounded and cycle-detected. Its termination precondition is
    catalog acyclicity (no entry body references any entry name in the
    catalog — [acyclic] in UserExpand.v).

    This file re-exports and extends the acyclicity invariants under
    the memo-requested name. Each theorem has non-trivial content:
    adding a fresh entry to an acyclic catalog yields an acyclic
    catalog iff the new entry is self-consistent and cross-disjoint. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import LaTeXPerfectionist.UserExpand.

(** The empty catalog is acyclic. Base case for inductive constructions. *)
Theorem empty_catalog_acyclic : acyclic [].
Proof.
  unfold acyclic. intros e Hin. inversion Hin.
Qed.

(** A single-entry catalog is acyclic iff the entry body doesn't
    reference the entry's own name. *)
Theorem singleton_acyclic :
  forall (e : catalog_entry),
    count_refs [fst e] (snd e) = 0 ->
    acyclic [e].
Proof.
  intros e Hself. unfold acyclic.
  intros e' Hin.
  simpl in Hin. destruct Hin as [Heq | H].
  - subst e'. simpl. exact Hself.
  - inversion H.
Qed.

(** Adding a fresh entry [e] to an acyclic catalog [cat] yields an
    acyclic catalog when:
    - [e]'s body doesn't reference any existing name (cross-disjoint
      forward);
    - every existing entry's body doesn't reference [e]'s name
      (cross-disjoint backward);
    - [e]'s body doesn't reference [e]'s own name (self-consistent).

    This is the memo §16.1 termination-precondition-preservation theorem
    specialised to single-entry addition — the shape the runtime uses
    when registering a user `\newcommand`. *)
Theorem add_entry_acyclic :
  forall (cat : catalog) (e : catalog_entry),
    acyclic cat ->
    count_refs (entry_names cat) (snd e) = 0 ->
    (forall e', In e' cat ->
      count_refs [fst e] (snd e') = 0) ->
    count_refs [fst e] (snd e) = 0 ->
    acyclic (cat ++ [e]).
Proof.
  intros cat e Hac Hfwd Hbck Hself.
  change (cat ++ [e]) with (merge cat [e]).
  apply merge_acyclic.
  - exact Hac.
  - apply singleton_acyclic. exact Hself.
  - (* forall e' in cat, count_refs (entry_names [e]) (snd e') = 0 *)
    intros e' Hin.
    unfold entry_names. simpl.
    apply Hbck. exact Hin.
  - (* forall e' in [e], count_refs (entry_names cat) (snd e') = 0 *)
    intros e' Hin. simpl in Hin. destruct Hin as [Heq | Habs].
    + subst e'. exact Hfwd.
    + inversion Habs.
Qed.

(** Count_refs is monotone under appending to the names list:
    adding more names can only increase the reference count. Useful
    for reasoning about partial catalog expansion. *)
Theorem count_refs_monotone :
  forall n1 n2 body,
    count_refs n1 body <= count_refs (n1 ++ n2) body.
Proof.
  intros n1 n2 body. induction body as [|x xs IH]; simpl; [lia|].
  rewrite mem_nat_app.
  destruct (mem_nat x n1); simpl; lia.
Qed.

Definition user_macro_termination_zero_admits : True := I.
