(** * SnapshotConsistency — cross-layer consistency proof (spec §5)

    "Validators observe either old or new snapshot, never interleaved."
    This proof establishes that the version-vector protocol guarantees
    snapshot consistency: if a snapshot passes is_consistent, then all
    layers form a valid parent-child chain with matching generation numbers. *)

From Coq Require Import List Bool Arith.
Import ListNotations.

(** Version vector: each layer carries its own generation number
    and the generation of its parent layer. *)
Record version_vector := mk_vv {
  gen : nat;
  parent_gen : nat;
}.

(** A child's parent_gen must match the parent's gen for the delta
    to be accepted. This is the core consistency invariant. *)
Definition accepts_delta (parent child : version_vector) : bool :=
  Nat.eqb (parent_gen child) (gen parent).

(** A snapshot is consistent if every adjacent (parent, child) pair
    satisfies accepts_delta. *)
Fixpoint is_consistent (layers : list version_vector) : bool :=
  match layers with
  | [] => true
  | [_] => true
  | parent :: ((child :: _) as rest) =>
      accepts_delta parent child && is_consistent rest
  end.

(** Theorem: if is_consistent holds, then for every adjacent pair,
    the child's parent_gen equals the parent's gen. *)
Theorem snapshot_consistency :
  forall layers,
    is_consistent layers = true ->
    forall i parent child,
      nth_error layers i = Some parent ->
      nth_error layers (S i) = Some child ->
      parent_gen child = gen parent.
Proof.
  induction layers as [| h rest IH]; intros Hcons i parent child Hp Hc.
  - (* empty list: impossible *)
    destruct i; simpl in Hp; discriminate.
  - destruct rest as [| h2 rest'].
    + (* single element: S i has no element *)
      destruct i; simpl in Hc; discriminate.
    + (* h :: h2 :: rest' *)
      simpl in Hcons.
      apply Bool.andb_true_iff in Hcons.
      destruct Hcons as [Hacc Hrest].
      destruct i.
      * (* i = 0: parent = h, child = h2 *)
        simpl in Hp, Hc.
        injection Hp as <-.
        injection Hc as <-.
        unfold accepts_delta in Hacc.
        apply Nat.eqb_eq in Hacc.
        exact Hacc.
      * (* i > 0: delegate to IH *)
        simpl in Hp, Hc.
        apply (IH Hrest i parent child Hp Hc).
Qed.

(** A single-element list is always consistent. *)
Theorem single_consistent :
  forall v, is_consistent [v] = true.
Proof. intros v. simpl. reflexivity. Qed.

(** The empty list is always consistent. *)
Theorem nil_consistent : is_consistent [] = true.
Proof. simpl. reflexivity. Qed.

(** Zero-admit witness. *)
Definition snapshot_consistency_zero_admits : True := I.
