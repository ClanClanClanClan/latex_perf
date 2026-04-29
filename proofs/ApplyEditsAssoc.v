(** * ApplyEditsAssoc — apply_edits associative-reorder theorem.

    Per `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md`: prove that
    [RewritePreservesCST.apply_edits_concrete] is invariant under
    reordering of pairwise non-overlapping edits.  Currently the
    implementation applies edits sequentially over the mutating
    buffer; the spec wants the strong claim that for non-overlapping
    edits, the order of application doesn't matter.

    Multi-stage:
    - Stage 1 (this commit): define [non_overlapping] + sanity
      lemmas (decidability, symmetry, consistency with the existing
      [RewritePreservesCST.edits_conflict] predicate).
    - Stage 2: parallel-application Fixpoint (sort by start, apply
      each in original-source offset order).
    - Stage 3: equivalence of parallel and sequential on
      pairwise-non-overlapping edit lists.
    - Stage 4: associativity / permutation invariance for the
      parallel applier; combined with Stage 3, the
      [apply_edits_concrete_associative_subset] headline theorem.
    - Stage 5: wire into [proofs/ADMISSIBILITY_MAP.md] +
      [docs/MERGING_GUARANTEES.md] (or similar).
    - Stage 6: release-bump.

    Zero admits, zero axioms. *)

From Coq Require Import List Arith Lia.
From LaTeXPerfectionist Require Import CSTRoundTrip RewritePreservesCST.
Import ListNotations.

(** ── Stage 1: non_overlapping predicate + sanity lemmas ──────────── *)

(** Two edits are non-overlapping iff their pre-edit byte ranges do
    not overlap (boundary-touching is allowed; insertions at the
    same point are non-overlapping by convention).  Defined as the
    negation of [RewritePreservesCST.edits_conflict] for consistency
    with the existing rewrite-engine semantics. *)
Definition non_overlapping (e1 e2 : edit) : Prop :=
  e1.(e_end) <= e2.(e_start) \/ e2.(e_end) <= e1.(e_start).

(** Symmetry: order of arguments doesn't matter. *)
Lemma non_overlapping_sym :
  forall a b, non_overlapping a b -> non_overlapping b a.
Proof.
  intros a b [H | H]; unfold non_overlapping; tauto.
Qed.

(** Reflexivity hazard: a well-formed non-empty-range edit is NOT
    non-overlapping with itself.  This rules out `non_overlapping
    e e` for genuine edits. *)
Lemma non_overlapping_self_iff :
  forall e,
    non_overlapping e e <-> e.(e_end) <= e.(e_start).
Proof.
  intros e. unfold non_overlapping. split.
  - intros [H | H]; assumption.
  - intros H. left. exact H.
Qed.

(** A well-formed edit (start <= end) with strictly positive range
    cannot be non-overlapping with itself. *)
Lemma non_overlapping_self_strict :
  forall e,
    edit_wf e ->
    e.(e_start) < e.(e_end) ->
    ~ non_overlapping e e.
Proof.
  intros e _ Hpos Hno.
  apply non_overlapping_self_iff in Hno. lia.
Qed.

(** Decidability: non_overlapping is decidable because both clauses
    are nat-comparisons. *)
Lemma non_overlapping_dec :
  forall a b, {non_overlapping a b} + {~ non_overlapping a b}.
Proof.
  intros a b. unfold non_overlapping.
  destruct (le_dec (e_end a) (e_start b)) as [H1 | H1].
  - left. left. exact H1.
  - destruct (le_dec (e_end b) (e_start a)) as [H2 | H2].
    + left. right. exact H2.
    + right. intros [H | H]; contradiction.
Qed.

(** Consistency with the existing [edits_conflict] predicate: for
    well-formed edits with strictly positive ranges, [non_overlapping]
    is the negation of [edits_conflict].  Insertions (start = end)
    are handled differently — see [edits_conflict]'s degenerate
    first-disjunct (always False under the current definition). *)
Lemma non_overlapping_iff_not_conflict_strict :
  forall a b,
    edit_wf a ->
    edit_wf b ->
    a.(e_start) < a.(e_end) ->
    b.(e_start) < b.(e_end) ->
    non_overlapping a b <-> ~ edits_conflict a b.
Proof.
  intros a b Ha Hb Hapos Hbpos.
  unfold non_overlapping, edits_conflict, edit_wf in *. split.
  - intros [H | H] [Hcontra | Hcontra].
    + destruct Hcontra as [_ [_ Hfalse]]. exact Hfalse.
    + lia.
    + destruct Hcontra as [_ [_ Hfalse]]. exact Hfalse.
    + lia.
  - intros Hno.
    destruct (le_dec (e_end a) (e_start b)) as [H1 | H1]; [left; lia |].
    destruct (le_dec (e_end b) (e_start a)) as [H2 | H2]; [right; lia |].
    exfalso. apply Hno. right. split; lia.
Qed.

(** Pairwise extension.  Stages 2–4 use [pairwise_non_overlapping]
    against [pairwise_non_conflicting] from RewritePreservesCST. *)
Definition pairwise_non_overlapping (es : list edit) : Prop :=
  forall i j,
    i < length es -> j < length es -> i <> j ->
    match nth_error es i, nth_error es j with
    | Some a, Some b => non_overlapping a b
    | _, _ => True
    end.

(** ── Stage 1 zero-admit witness ───────────────────────────────────── *)

Definition apply_edits_assoc_stage1_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 apply_edits_assoc STAGE 2 — parallel-application Fixpoint
    ─────────────────────────────────────────────────────────────────

    Per V27_APPLY_EDITS_ASSOC_PLAN.md Stage 2.

    Critical observation: [apply_edits_concrete] applies edits
    sequentially over a mutating buffer.  Each edit's [e_start] /
    [e_end] are interpreted relative to the CURRENT buffer (post
    earlier edits), NOT the original source.  So even for
    pairwise-non-overlapping edits in the original source,
    [apply_edits_concrete src [e1;e2]] generally differs from
    [apply_edits_concrete src [e2;e1]] when the edits change buffer
    length and the offsets shift.

    Concrete counter-example:
      src = [97;98;99;100;101;102]              (* "abcdef" *)
      e1  = mk_edit 1 3 [88]                    (* replace "bc" with "X" *)
      e2  = mk_edit 4 5 [89;90]                 (* replace "e" with "YZ" *)
      [e1;e2]: after e1 buf="aXdef" (len 5); e2 with e_start=4 hits
               byte 4 of "aXdef" = 'e' but post-edit drop 5 leaves [].
      [e2;e1]: after e2 buf="abcdYZf" (len 7); e1 with e_start=1
               hits 'b' as expected.
      Results differ.

    The "parallel" applier interprets every offset relative to the
    ORIGINAL source.  Implementation: sort edits by [e_start]
    descending, then apply sequentially.  Applying the rightmost
    edit first leaves all smaller offsets unchanged in the
    remaining buffer; iterate.  For pairwise-non-overlapping edits,
    this matches the byte-by-byte original-offset semantic
    (Stage 3 proves equivalence). *)

(** Insert [e] into [es] at the position that maintains descending
    order by [e_start].  Stable on equal keys (existing element
    appears later than the inserted one). *)
Fixpoint insert_desc (e : edit) (es : list edit) : list edit :=
  match es with
  | [] => [e]
  | x :: rest =>
      if Nat.leb x.(e_start) e.(e_start)
      then e :: x :: rest
      else x :: insert_desc e rest
  end.

(** Sort by [e_start] descending using insertion sort. *)
Fixpoint sort_by_start_desc (es : list edit) : list edit :=
  match es with
  | [] => []
  | e :: rest => insert_desc e (sort_by_start_desc rest)
  end.

(** The parallel applier: apply edits in original-source offset
    semantics by sorting descending and using the sequential
    applier from RewritePreservesCST. *)
Definition apply_edits_parallel (src : bytes) (es : list edit) : bytes :=
  apply_edits_concrete src (sort_by_start_desc es).

(** Sanity Example: parallel application matches the byte-by-byte
    original-offset semantic on a 6-byte source with two
    non-overlapping edits. *)
Example apply_edits_parallel_disjoint_example :
  let src := [97; 98; 99; 100; 101; 102] in   (* "abcdef" *)
  let e1 := mk_edit 1 3 [88] in                (* replace "bc" with "X" *)
  let e2 := mk_edit 4 5 [89; 90] in            (* replace "e" with "YZ" *)
  apply_edits_parallel src [e1; e2]
    = [97; 88; 100; 89; 90; 102].              (* "aXdYZf" *)
Proof. reflexivity. Qed.

(** Sanity Example: order independence on the parallel applier
    (Stage 4 generalises this to a permutation theorem). *)
Example apply_edits_parallel_disjoint_swap :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  apply_edits_parallel src [e1; e2] = apply_edits_parallel src [e2; e1].
Proof. reflexivity. Qed.

(** Length preservation: insert_desc grows the list by exactly 1. *)
Lemma insert_desc_length :
  forall e es, length (insert_desc e es) = S (length es).
Proof.
  intros e es. induction es as [|x rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb (e_start x) (e_start e)); simpl;
      [reflexivity | rewrite IH; reflexivity].
Qed.

(** Sort preserves length. *)
Lemma sort_by_start_desc_length :
  forall es, length (sort_by_start_desc es) = length es.
Proof.
  induction es as [|e rest IH]; simpl.
  - reflexivity.
  - rewrite insert_desc_length, IH. reflexivity.
Qed.

(** ── Stage 2 zero-admit witness ───────────────────────────────────── *)

Definition apply_edits_assoc_stage2_zero_admits : True := I.
