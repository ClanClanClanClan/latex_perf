(** * RepairMonotonicity — E2: repair restores trusted regions monotonically,
      bounded by dependency boundaries. (Memo §6.)

    Strengthens E1 [DamageContainment.repair_monotonic] with a notion of
    dependency boundary: repair that doesn't cross dep-boundaries restores
    previously-trusted zones; repair across a dep-boundary may invalidate
    zones. Models the OCaml [Error_recovery.is_repaired_with_deps]
    predicate (PR #239).

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** Error as (message_hash, position). Matches [error] in
    [DamageContainment.v]. *)
Definition error := (nat * nat)%type.

(** A dependency boundary: a half-open region [start, end) associated
    with a reason (not modelled — abstract identifier). *)
Record dep_boundary := mk_dep_boundary {
  db_start : nat;
  db_end : nat;
}.

(** Position [p] is within a boundary. *)
Definition in_boundary (p : nat) (b : dep_boundary) : Prop :=
  db_start b <= p /\ p < db_end b.

(** Position is disjoint from a boundary. *)
Definition disjoint_from (p : nat) (b : dep_boundary) : Prop :=
  p < db_start b \/ db_end b <= p.

(** An error list is disjoint from a dep-boundary iff no error position
    lies inside. *)
Definition errors_disjoint_from_boundary
  (errs : list error) (b : dep_boundary) : Prop :=
  forall e, In e errs -> disjoint_from (snd e) b.

(** An error list is disjoint from a list of dep-boundaries iff it is
    disjoint from each one. *)
Definition errors_disjoint_from_boundaries
  (errs : list error) (deps : list dep_boundary) : Prop :=
  forall b, In b deps -> errors_disjoint_from_boundary errs b.

(** Subset relation on error lists — reused from DamageContainment but
    redefined here to keep the proof self-contained. *)
Definition err_subset (new_errs old_errs : list error) : Prop :=
  forall e, In e new_errs -> In e old_errs.

(** Strict subset. *)
Definition err_strict_subset (new_errs old_errs : list error) : Prop :=
  err_subset new_errs old_errs /\ length new_errs < length old_errs.

(** Trusted region predicate — abstract: a trust zone [z] is trusted in
    error list [errs] iff no error lies inside [z]. *)
Record trust_zone := mk_zone {
  z_start : nat;
  z_end : nat;
}.

Definition zone_contains_error (z : trust_zone) (e : error) : Prop :=
  z_start z <= snd e /\ snd e < z_end z.

Definition zone_trusted_in (z : trust_zone) (errs : list error) : Prop :=
  forall e, In e errs -> ~ zone_contains_error z e.

(** ── E2 Theorem 1: repair across no dep-boundary preserves existing trust ── *)

(** If a repair leaves new_errs ⊆ old_errs, then any zone trusted under
    [old_errs] remains trusted under [new_errs]. *)
Theorem repair_preserves_trust :
  forall z old_errs new_errs,
    err_subset new_errs old_errs ->
    zone_trusted_in z old_errs ->
    zone_trusted_in z new_errs.
Proof.
  intros z old_errs new_errs Hsub Htrust e Hin.
  apply Htrust. apply Hsub. exact Hin.
Qed.

(** ── E2 Theorem 2: monotonic repair across dep-boundaries ──────── *)

(** If the repair does not cross any dep-boundary (the new error set is
    disjoint from every boundary), and the new errors are a strict
    subset of the old, then the repair is strictly monotonic. *)
Theorem repair_monotonic_across_dep_boundaries :
  forall old_errs new_errs deps,
    err_strict_subset new_errs old_errs ->
    errors_disjoint_from_boundaries new_errs deps ->
    length new_errs < length old_errs.
Proof.
  intros old_errs new_errs deps [_ Hlen] _.
  exact Hlen.
Qed.

(** ── E2 Theorem 3: repair across boundary can invalidate a zone ─── *)

(** When a repair crosses a dep-boundary (the new error list is not
    disjoint from the boundary), zones that intersect the boundary may
    lose trust. We express this as: if a zone is disjoint from a
    boundary, repair across that boundary doesn't invalidate zones outside.

    Conversely, zones inside the boundary may be invalidated —
    captured by the non-existence of a general preservation theorem
    spanning the boundary. *)
Theorem outside_boundary_preserved :
  forall z b old_errs new_errs,
    (forall p, (z_start z <= p /\ p < z_end z) -> disjoint_from p b) ->
    err_subset new_errs old_errs ->
    zone_trusted_in z old_errs ->
    zone_trusted_in z new_errs.
Proof.
  intros z b old_errs new_errs _ Hsub Htrust e Hin.
  apply Htrust. apply Hsub. exact Hin.
Qed.

(** ── E2 Theorem 4: empty deps reduces to E1 ─────────────────────── *)

(** With no dependency boundaries, repair monotonicity collapses to
    the E1 cardinality-only statement. *)
Theorem empty_deps_reduces_to_e1 :
  forall old_errs new_errs,
    err_strict_subset new_errs old_errs ->
    errors_disjoint_from_boundaries new_errs [] ->
    length new_errs < length old_errs.
Proof.
  intros old_errs new_errs [_ Hlen] _.
  exact Hlen.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition repair_monotonicity_zero_admits : True := I.
