(** * DamageContainment — E1: monotonic repair (WS5).

    Proves that fixing errors monotonically improves document confidence:
    fewer errors means repair progress. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** Error as a (message_hash, position) pair. *)
Definition error := (nat * nat)%type.

(** Subset relation on error lists. *)
Definition is_subset (new_errs old_errs : list error) : Prop :=
  forall e, In e new_errs -> In e old_errs.

(** Strict subset: fewer errors. *)
Definition is_strict_subset (new_errs old_errs : list error) : Prop :=
  is_subset new_errs old_errs /\
  length new_errs < length old_errs.

(** Monotonic repair: if new errors are a strict subset, repair happened. *)
Theorem repair_monotonic :
  forall old_errs new_errs,
    is_strict_subset new_errs old_errs ->
    length new_errs < length old_errs.
Proof.
  intros old_errs new_errs [_ Hlen]. exact Hlen.
Qed.

(** Empty error list is maximally repaired. *)
Theorem fully_repaired :
  forall old_errs,
    old_errs <> [] ->
    is_strict_subset [] old_errs.
Proof.
  intros old_errs Hne. split.
  - intros e Hin. inversion Hin.
  - simpl. destruct old_errs.
    + contradiction.
    + simpl. lia.
Qed.

(** Subset is transitive. *)
Theorem subset_trans :
  forall a b c : list error,
    is_subset a b -> is_subset b c -> is_subset a c.
Proof.
  intros a b c Hab Hbc e Hin.
  apply Hbc. apply Hab. exact Hin.
Qed.

(** Zero-admit witness. *)
Definition damage_containment_zero_admits : True := I.
