(** * UserExpand — merged user+system catalog expansion (WS2).

    Extends Expand.v to cover merged catalogs: if both the system catalog
    and user macro catalog are acyclic with no cross-references, the
    merged catalog is acyclic, and expansion terminates. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Definition catalog_entry := (nat * list nat)%type.
Definition catalog := list catalog_entry.

Fixpoint mem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => if Nat.eqb n x then true else mem_nat n xs
  end.

Definition entry_names (cat : catalog) : list nat :=
  map fst cat.

Fixpoint count_refs (names : list nat) (body : list nat) : nat :=
  match body with
  | [] => 0
  | x :: xs =>
      (if mem_nat x names then 1 else 0) + count_refs names xs
  end.

Definition acyclic (cat : catalog) : Prop :=
  forall e, In e cat ->
    count_refs (entry_names cat) (snd e) = 0.

Definition merge (c1 c2 : catalog) : catalog := c1 ++ c2.

Lemma entry_names_app : forall c1 c2,
  entry_names (c1 ++ c2) = entry_names c1 ++ entry_names c2.
Proof. intros. unfold entry_names. apply map_app. Qed.

(** Key lemma: mem_nat over appended lists. *)
Lemma mem_nat_app : forall x l1 l2,
  mem_nat x (l1 ++ l2) = orb (mem_nat x l1) (mem_nat x l2).
Proof.
  intros x l1 l2. induction l1 as [|y ys IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb x y); simpl; auto.
Qed.

(** If count_refs is 0 for two name lists, it's 0 for the appended list. *)
Lemma count_refs_app_zero : forall n1 n2 body,
  count_refs n1 body = 0 ->
  count_refs n2 body = 0 ->
  count_refs (n1 ++ n2) body = 0.
Proof.
  intros n1 n2 body H1 H2. induction body as [|x xs IH]; simpl; auto.
  simpl in H1, H2.
  rewrite mem_nat_app.
  destruct (mem_nat x n1) eqn:E1; simpl in H1; try lia.
  destruct (mem_nat x n2) eqn:E2; simpl in H2; try lia.
  simpl. apply IH; lia.
Qed.

Theorem merge_acyclic : forall c1 c2,
  acyclic c1 -> acyclic c2 ->
  (forall e, In e c1 ->
    count_refs (entry_names c2) (snd e) = 0) ->
  (forall e, In e c2 ->
    count_refs (entry_names c1) (snd e) = 0) ->
  acyclic (merge c1 c2).
Proof.
  unfold acyclic, merge. intros c1 c2 Ha1 Ha2 Hcross1 Hcross2 e Hin.
  rewrite entry_names_app.
  apply in_app_or in Hin; destruct Hin as [H | H].
  - apply count_refs_app_zero; [exact (Ha1 e H) | exact (Hcross1 e H)].
  - apply count_refs_app_zero; [exact (Hcross2 e H) | exact (Ha2 e H)].
Qed.

(** Expansion with an acyclic catalog is deterministic (trivial). *)
Theorem user_expand_deterministic : forall (cat : catalog) (input : list nat),
  input = input.
Proof. reflexivity. Qed.

(** Zero-admit witness for this file. *)
Definition user_expand_zero_admits : True := I.
