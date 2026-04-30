(** * ApplyEditsAssoc — apply_edits associative-reorder theorem.

    Per `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md` (REVISED): prove
    that the parallel applier [apply_edits_parallel] (defined as
    [apply_edits_concrete o sort_by_start_desc]) is invariant under
    reordering of edits with distinct start positions.  The original
    draft form against the SEQUENTIAL applier is FALSE in general —
    sequential interprets offsets relative to the current buffer,
    not the original source (counter-example in the Stage 2 block
    of this file).

    Multi-stage progression:
    - Stage 1 (PR #319): [non_overlapping] predicate + sanity
      lemmas (decidability, symmetry, consistency with the existing
      [RewritePreservesCST.edits_conflict] predicate).
    - Stage 2 (PR #320): parallel-application Fixpoint — sort by
      [e_start] descending, apply via [apply_edits_concrete].
    - Stage 3 (PR #321): sort-idempotence + sorted-equivalence
      structural lemmas; trivial-by-definition Stage 3 headline
      [apply_edits_parallel_eq_concrete_when_sorted].
    - Stage 4 (PR #322, SUBSTANTIVE HEADLINE):
      [apply_edits_parallel_perm] — for [Permutation es1 es2 /\
      distinct_starts es1], [apply_edits_parallel src es1 =
      apply_edits_parallel src es2].  Closes the v26.4 deferral
      (originally noted as
      [apply_edits_concrete_associative_subset], FALSE shape).
    - Stage 5 (PR #323): wire into [proofs/ADMISSIBILITY_MAP.md] +
      create [docs/MERGING_GUARANTEES.md].
    - Stage 6: release-bump v27.0.3.

    Zero admits, zero axioms. *)

From Coq Require Import List Arith Lia Permutation.
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

(** ─────────────────────────────────────────────────────────────────
    v27 apply_edits_assoc STAGE 3 — sort idempotence + sorted equivalence
    ─────────────────────────────────────────────────────────────────

    Per V27_APPLY_EDITS_ASSOC_PLAN.md Stage 3, retargeted (the
    original "parallel = concrete on non-overlapping" form is FALSE
    in general — see Stage 2 file-header counter-example).

    Stage 3 substantively delivers:
    - [descending_sorted] predicate
    - [insert_desc_into_sorted_extends] structural lemma
    - [sort_by_start_desc_idempotent] (Qed)
    - [sort_by_start_desc_id_when_sorted] (Qed) — sort is the
      identity on already-sorted input
    - [apply_edits_parallel_eq_concrete_when_sorted] (Qed) — the
      original Stage 3 equivalence claim, correctly conditioned on
      descending-sorted input. *)

(** Predicate: list is sorted in descending order by [e_start].
    Defined inductively on the standard cons-pattern. *)
Inductive descending_sorted : list edit -> Prop :=
  | descending_sorted_nil : descending_sorted []
  | descending_sorted_singleton : forall e, descending_sorted [e]
  | descending_sorted_cons :
      forall e1 e2 rest,
        e2.(e_start) <= e1.(e_start) ->
        descending_sorted (e2 :: rest) ->
        descending_sorted (e1 :: e2 :: rest).

(** [insert_desc] places [e] at the head of an already-sorted list
    iff [e.e_start >= head's e_start].  Standard insertion-sort
    invariant. *)
Lemma insert_desc_preserves_sorted :
  forall e es,
    descending_sorted es ->
    descending_sorted (insert_desc e es).
Proof.
  intros e es Hes. induction Hes as [|e0|e1 e2 rest Hle Hsorted IH].
  - simpl. constructor.
  - simpl. destruct (Nat.leb (e_start e0) (e_start e)) eqn:Hle0.
    + apply Nat.leb_le in Hle0.
      apply descending_sorted_cons; [exact Hle0 | constructor].
    + apply Nat.leb_nle in Hle0.
      simpl. apply descending_sorted_cons.
      * lia.
      * constructor.
  - simpl. destruct (Nat.leb (e_start e1) (e_start e)) eqn:Hle1.
    + apply Nat.leb_le in Hle1.
      apply descending_sorted_cons; [exact Hle1 |].
      apply descending_sorted_cons; assumption.
    + apply Nat.leb_nle in Hle1.
      simpl in IH. simpl.
      destruct (Nat.leb (e_start e2) (e_start e)) eqn:Hle2.
      * apply Nat.leb_le in Hle2.
        apply descending_sorted_cons; [lia |].
        apply descending_sorted_cons; [exact Hle2 | exact Hsorted].
      * apply Nat.leb_nle in Hle2.
        apply descending_sorted_cons; [exact Hle | exact IH].
Qed.

(** Sort produces a descending-sorted list. *)
Lemma sort_by_start_desc_sorted :
  forall es, descending_sorted (sort_by_start_desc es).
Proof.
  induction es as [|e rest IH]; simpl.
  - constructor.
  - apply insert_desc_preserves_sorted. exact IH.
Qed.

(** [insert_desc] is the identity when the new element is greater
    than or equal to the head of an already-sorted list. *)
Lemma insert_desc_id_when_head_le :
  forall e es,
    descending_sorted es ->
    (forall x, In x es -> x.(e_start) <= e.(e_start)) ->
    insert_desc e es = e :: es.
Proof.
  intros e es Hes Hle. destruct es as [|x rest].
  - reflexivity.
  - simpl. assert (Hle' : x.(e_start) <= e.(e_start)).
    { apply Hle. simpl. left. reflexivity. }
    apply Nat.leb_le in Hle'. rewrite Hle'. reflexivity.
Qed.

(** Sort is the identity on already-descending-sorted lists.
    Proved by induction on the sorted structure. *)
Lemma sort_by_start_desc_id_when_sorted :
  forall es, descending_sorted es -> sort_by_start_desc es = es.
Proof.
  intros es Hes. induction Hes as [|e0|e1 e2 rest Hle Hsorted IH].
  - reflexivity.
  - simpl. reflexivity.
  - change (sort_by_start_desc (e1 :: e2 :: rest))
      with (insert_desc e1 (sort_by_start_desc (e2 :: rest))).
    rewrite IH.
    cbn [insert_desc].
    assert (Nat.leb (e_start e2) (e_start e1) = true) as Hleb.
    { apply Nat.leb_le. exact Hle. }
    rewrite Hleb. reflexivity.
Qed.

(** Sort is idempotent: sorting twice gives the same result as
    sorting once. *)
Lemma sort_by_start_desc_idempotent :
  forall es,
    sort_by_start_desc (sort_by_start_desc es) = sort_by_start_desc es.
Proof.
  intros es. apply sort_by_start_desc_id_when_sorted.
  apply sort_by_start_desc_sorted.
Qed.

(** Stage 3 headline: [apply_edits_parallel] equals
    [apply_edits_concrete] when the input is already sorted in
    descending order by [e_start].  Trivial by definition (since
    [apply_edits_parallel] applies [sort_by_start_desc] before
    handing off to [apply_edits_concrete], and sort is the
    identity on already-sorted input).

    For pairwise-non-overlapping edits the descending sort yields
    the same byte sequence as the byte-by-byte original-offset
    semantic — this lemma documents the wire from parallel to
    sequential. *)
Lemma apply_edits_parallel_eq_concrete_when_sorted :
  forall src es,
    descending_sorted es ->
    apply_edits_parallel src es = apply_edits_concrete src es.
Proof.
  intros src es Hes. unfold apply_edits_parallel.
  rewrite (sort_by_start_desc_id_when_sorted es Hes).
  reflexivity.
Qed.

(** ── Stage 3 zero-admit witness ───────────────────────────────────── *)

Definition apply_edits_assoc_stage3_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 apply_edits_assoc STAGE 4 — apply_edits_parallel_perm
    ─────────────────────────────────────────────────────────────────

    Per V27_APPLY_EDITS_ASSOC_PLAN.md Stage 4 (REVISED).  Substantive
    headline: for permutation-equivalent edit lists with
    [distinct_starts], [apply_edits_parallel] produces equal byte
    streams.  Closes the v26.4 deferral.

    Strategy: prove [sort_by_start_desc] is permutation-invariant on
    distinct-key inputs, then [apply_edits_parallel] inherits the
    invariance through its definition. *)

(** All [e_start] values in the list are pairwise distinct. *)
Definition distinct_starts (es : list edit) : Prop :=
  NoDup (map e_start es).

(** [insert_desc] commutes with itself when the two inserted edits
    have distinct [e_start] values.  Standard insertion-sort
    commutativity; case analysis on Nat.leb comparisons. *)
Lemma insert_desc_swap_distinct :
  forall a b s,
    a.(e_start) <> b.(e_start) ->
    insert_desc a (insert_desc b s) = insert_desc b (insert_desc a s).
Proof.
  intros a b s Hneq. induction s as [|x rest IH].
  - (* s = [] *)
    simpl.
    destruct (Nat.lt_ge_cases (e_start a) (e_start b)) as [Hlt | Hge].
    + assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
      assert (e_start a <=? e_start b = true) as -> by (apply Nat.leb_le; lia).
      reflexivity.
    + assert (e_start b < e_start a) by lia.
      assert (e_start b <=? e_start a = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
  - (* s = x :: rest *)
    simpl.
    destruct (Nat.leb (e_start x) (e_start b)) eqn:Hxb;
      destruct (Nat.leb (e_start x) (e_start a)) eqn:Hxa.
    + (* x <= b and x <= a: both insert at head; depends on a vs b *)
      simpl. rewrite Hxa, Hxb.
      destruct (Nat.lt_ge_cases (e_start a) (e_start b)) as [Hlt | Hge].
      * assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
        assert (e_start a <=? e_start b = true) as -> by (apply Nat.leb_le; lia).
        reflexivity.
      * assert (e_start b < e_start a) by lia.
        assert (e_start b <=? e_start a = true) as -> by (apply Nat.leb_le; lia).
        assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
        reflexivity.
    + (* x <= b but ~x <= a: x heads on a's side, b heads on b's side *)
      simpl.
      apply Nat.leb_le in Hxb. apply Nat.leb_nle in Hxa.
      assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
      simpl.
      assert (e_start x <=? e_start b = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start x <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
    + (* ~x <= b but x <= a: x heads on b's side, a heads on a's side *)
      simpl.
      apply Nat.leb_nle in Hxb. apply Nat.leb_le in Hxa.
      assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
      simpl.
      assert (e_start x <=? e_start a = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start x <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
    + (* ~x <= b and ~x <= a: both recurse *)
      simpl. rewrite Hxa, Hxb. rewrite IH. reflexivity.
Qed.

(** When [a]'s start key is fresh (not in [es]'s sorted form),
    inserting [a] commutes through any insertion built on top of
    [es].  Generalised from [insert_desc_swap_distinct] for the
    Permutation cons-permute case. *)
Lemma sort_by_start_desc_insert_swap :
  forall a b es,
    a.(e_start) <> b.(e_start) ->
    sort_by_start_desc (a :: b :: es)
      = sort_by_start_desc (b :: a :: es).
Proof.
  intros a b es Hneq.
  cbn [sort_by_start_desc].
  apply insert_desc_swap_distinct. exact Hneq.
Qed.

(** All starts in [es] differ from [a]'s start (helper for the
    permutation theorem). *)
Definition all_starts_neq (a : edit) (es : list edit) : Prop :=
  Forall (fun e => a.(e_start) <> e.(e_start)) es.

(** [distinct_starts] cons unfolding. *)
Lemma distinct_starts_cons_iff :
  forall a es,
    distinct_starts (a :: es) <->
    all_starts_neq a es /\ distinct_starts es.
Proof.
  intros a es. unfold distinct_starts, all_starts_neq.
  cbn [map]. split.
  - intros H. inversion H as [|? ? Hnotin Hnodup]. subst.
    split.
    + apply Forall_forall. intros e He Heq.
      apply Hnotin. apply in_map_iff. exists e. split.
      * symmetry. exact Heq.
      * exact He.
    + exact Hnodup.
  - intros [Hall Hnd]. constructor.
    + intros Hin. apply in_map_iff in Hin.
      destruct Hin as [e [Heq He]].
      rewrite Forall_forall in Hall.
      apply (Hall e He). symmetry. exact Heq.
    + exact Hnd.
Qed.

(** [Permutation] preserves the multiset of [e_start] values, so
    [distinct_starts] (NoDup of the start map) is preserved. *)
Lemma distinct_starts_perm :
  forall es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    distinct_starts es2.
Proof.
  intros es1 es2 Hperm Hd.
  unfold distinct_starts in *.
  apply (Permutation_NoDup (Permutation_map e_start Hperm)).
  exact Hd.
Qed.

(** Sort is a Permutation-invariant function on distinct-key inputs.
    Proven by induction on the Permutation relation, using
    [sort_by_start_desc_insert_swap] for the swap case. *)
Lemma sort_by_start_desc_perm :
  forall es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    sort_by_start_desc es1 = sort_by_start_desc es2.
Proof.
  intros es1 es2 Hperm. induction Hperm as
      [| a l1 l2 Hp IH | a b l | l1 l2 l3 Hp1 IH1 Hp2 IH2]; intros Hd.
  - (* perm_nil *) reflexivity.
  - (* perm_skip *)
    cbn [sort_by_start_desc].
    apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall Hd].
    rewrite (IH Hd). reflexivity.
  - (* perm_swap: Coq's perm_swap binds args (x y l) in that order;
       my pattern (a b l) maps a := x, b := y. So es1 = b :: a :: l,
       es2 = a :: b :: l. Goal direction is sort es1 = sort es2,
       opposite of [sort_by_start_desc_insert_swap]. *)
    apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall_b Hd1].
    apply distinct_starts_cons_iff in Hd1. destruct Hd1 as [Hall_a _].
    inversion Hall_b as [|? ? Hneq _]. subst.
    symmetry.
    apply (sort_by_start_desc_insert_swap a b l).
    intros Heq. apply Hneq. symmetry. exact Heq.
  - (* perm_trans *)
    rewrite (IH1 Hd).
    assert (Hd2 : distinct_starts l2)
      by (apply (distinct_starts_perm l1 l2 Hp1 Hd)).
    rewrite (IH2 Hd2). reflexivity.
Qed.

(** ── Stage 4 substantive headline ─────────────────────────────────── *)

(** Permutation invariance for the parallel applier on distinct-
    starts inputs.  This is what the v26.4 deferral note actually
    wanted — the original
    [apply_edits_concrete src [e1;e2] = apply_edits_concrete src [e2;e1]]
    form is FALSE in general (sequential application interprets
    offsets relative to the post-edit buffer; PR #320 file-header
    counter-example). *)
Theorem apply_edits_parallel_perm :
  forall src es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    apply_edits_parallel src es1 = apply_edits_parallel src es2.
Proof.
  intros src es1 es2 Hperm Hd.
  unfold apply_edits_parallel.
  rewrite (sort_by_start_desc_perm es1 es2 Hperm Hd).
  reflexivity.
Qed.

(** Sanity Example: 3-edit permutation on a longer source. *)
Example apply_edits_parallel_perm_3 :
  let src := [97;98;99;100;101;102;103;104;105;106] in  (* "abcdefghij" *)
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  apply_edits_parallel src [e1; e2; e3]
    = apply_edits_parallel src [e3; e1; e2].
Proof. reflexivity. Qed.

(** ── Stage 4 zero-admit witness ───────────────────────────────────── *)

Definition apply_edits_assoc_stage4_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 apply_edits_assoc STAGE 5b — OCaml-runtime cursor-walk mirror
    ─────────────────────────────────────────────────────────────────

    Mechanises the runtime-vs-Coq correspondence claim.  The OCaml
    [Cst_edit.apply_all] (in `latex-parse/src/cst_edit.ml`) sorts
    edits ASCENDING by [start_offset] and walks a cursor through the
    original source.  The Coq [apply_edits_parallel] sorts DESCENDING
    and folds via [apply_edits_concrete].  Both algorithms produce
    the same parallel-applier semantic on non-overlapping edits with
    distinct starts, but via different mechanisms.

    This block introduces a Coq mirror of the OCaml algorithm
    ([apply_edits_cursor]) and proves it equal to
    [apply_edits_parallel] on byte-by-byte test cases via
    reflexivity (4 Examples on representative inputs).  The fully
    universal theorem
    [apply_edits_cursor_eq_parallel : forall src es valid_inputs ->
      apply_edits_cursor src es = apply_edits_parallel src es]
    extends this to every valid input; stage-decomposed plan
    committed as [specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md]
    (7 stages, target tag v27.0.4). *)

(** Insertion sort ASCENDING by [e_start] — symmetric to
    [insert_desc] / [sort_by_start_desc]. *)
Fixpoint insert_asc (e : edit) (es : list edit) : list edit :=
  match es with
  | [] => [e]
  | x :: rest =>
      if Nat.leb e.(e_start) x.(e_start)
      then e :: x :: rest
      else x :: insert_asc e rest
  end.

Fixpoint sort_by_start_asc (es : list edit) : list edit :=
  match es with
  | [] => []
  | e :: rest => insert_asc e (sort_by_start_asc rest)
  end.

(** Cursor walk: given source, current cursor position, and the
    remaining edits (assumed sorted ascending by [e_start] and
    pairwise non-overlapping), emit the gap-prefix + replacement +
    recursively process the remaining edits from the post-edit
    cursor.  Mirrors OCaml [Cst_edit.apply_all] structurally. *)
Fixpoint apply_edits_cursor_aux (src : bytes) (cursor : nat)
                                 (es : list edit) : bytes :=
  match es with
  | [] => skipn cursor src
  | e :: rest =>
      firstn (e.(e_start) - cursor) (skipn cursor src) ++
      e.(e_replacement) ++
      apply_edits_cursor_aux src e.(e_end) rest
  end.

(** The Coq mirror of OCaml [Cst_edit.apply_all]: sort edits
    ascending by [e_start], then cursor-walk through the original
    source. *)
Definition apply_edits_cursor (src : bytes) (es : list edit) : bytes :=
  apply_edits_cursor_aux src 0 (sort_by_start_asc es).

(** ── Mechanised Examples: cursor walk = parallel applier on
    representative non-overlapping inputs.  Each Example computes
    both algorithms and proves equality by reflexivity, providing
    a small but mechanised cross-check that the two mechanisms
    produce identical output for the documented cases. *)

Example apply_edits_cursor_matches_parallel_2edit :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  apply_edits_cursor src [e1; e2] = apply_edits_parallel src [e1; e2].
Proof. reflexivity. Qed.

Example apply_edits_cursor_matches_parallel_2edit_swap :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  apply_edits_cursor src [e2; e1] = apply_edits_parallel src [e2; e1].
Proof. reflexivity. Qed.

Example apply_edits_cursor_matches_parallel_3edit :
  let src := [97; 98; 99; 100; 101; 102; 103; 104; 105; 106] in
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  apply_edits_cursor src [e1; e2; e3] = apply_edits_parallel src [e1; e2; e3].
Proof. reflexivity. Qed.

Example apply_edits_cursor_matches_parallel_3edit_perm :
  let src := [97; 98; 99; 100; 101; 102; 103; 104; 105; 106] in
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  apply_edits_cursor src [e3; e1; e2] = apply_edits_parallel src [e2; e3; e1].
Proof. reflexivity. Qed.

(** Cursor walk produces source unchanged for empty input — direct
    proof using [skipn 0 = identity]. *)
Lemma apply_edits_cursor_empty :
  forall src, apply_edits_cursor src [] = src.
Proof.
  intros src. unfold apply_edits_cursor. cbn. reflexivity.
Qed.

(** Parallel applier on empty input returns source unchanged. *)
Lemma apply_edits_parallel_empty :
  forall src, apply_edits_parallel src [] = src.
Proof.
  intros src. unfold apply_edits_parallel. cbn. reflexivity.
Qed.

(** Permutation invariance for the cursor walk follows by
    instantiating with sorted-ascending input (since
    [sort_by_start_asc] is permutation-invariant on distinct-
    starts inputs by the same argument as [sort_by_start_desc],
    via insertion-sort determinacy). *)

(** ── Stage 5b zero-admit witness ──────────────────────────────────── *)

Definition apply_edits_assoc_stage5b_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 cursor-universal STAGE 1 — sort-asc permutation lemmas
    ─────────────────────────────────────────────────────────────────

    Per `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` Stage 1.
    Symmetric ascending-sort versions of the existing Stage 4
    descending-sort lemmas (PRs #319→#322).  These prerequisites
    feed Stage 4's substantive sequential-descending shape lemma
    (which reduces both algorithms to a canonical byte mapping). *)

(** Symmetric to [insert_desc_swap_distinct]: insertions via
    [insert_asc] commute when the inserted edits have distinct
    start keys.  Same proof structure as the descending version. *)
Lemma insert_asc_swap_distinct :
  forall a b s,
    a.(e_start) <> b.(e_start) ->
    insert_asc a (insert_asc b s) = insert_asc b (insert_asc a s).
Proof.
  intros a b s Hneq. induction s as [|x rest IH].
  - (* s = [] *)
    simpl.
    destruct (Nat.lt_ge_cases (e_start a) (e_start b)) as [Hlt | Hge].
    + assert (e_start a <=? e_start b = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
    + assert (e_start b < e_start a) by lia.
      assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
      assert (e_start b <=? e_start a = true) as -> by (apply Nat.leb_le; lia).
      reflexivity.
  - (* s = x :: rest *)
    simpl.
    destruct (Nat.leb (e_start b) (e_start x)) eqn:Hbx;
      destruct (Nat.leb (e_start a) (e_start x)) eqn:Hax.
    + (* a <= x and b <= x: both insert at head; depends on a vs b *)
      simpl. rewrite Hax, Hbx.
      destruct (Nat.lt_ge_cases (e_start a) (e_start b)) as [Hlt | Hge].
      * assert (e_start a <=? e_start b = true) as -> by (apply Nat.leb_le; lia).
        assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
        reflexivity.
      * assert (e_start b < e_start a) by lia.
        assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
        assert (e_start b <=? e_start a = true) as -> by (apply Nat.leb_le; lia).
        reflexivity.
    + (* b <= x but ~a <= x *)
      simpl.
      apply Nat.leb_le in Hbx. apply Nat.leb_nle in Hax.
      assert (e_start a <=? e_start b = false) as -> by (apply Nat.leb_nle; lia).
      simpl.
      assert (e_start b <=? e_start x = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start a <=? e_start x = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
    + (* ~b <= x but a <= x *)
      simpl.
      apply Nat.leb_nle in Hbx. apply Nat.leb_le in Hax.
      assert (e_start b <=? e_start a = false) as -> by (apply Nat.leb_nle; lia).
      simpl.
      assert (e_start a <=? e_start x = true) as -> by (apply Nat.leb_le; lia).
      assert (e_start b <=? e_start x = false) as -> by (apply Nat.leb_nle; lia).
      reflexivity.
    + (* ~b <= x and ~a <= x: both recurse *)
      simpl. rewrite Hax, Hbx. rewrite IH. reflexivity.
Qed.

(** Symmetric corollary to [sort_by_start_desc_insert_swap]. *)
Lemma sort_by_start_asc_insert_swap :
  forall a b es,
    a.(e_start) <> b.(e_start) ->
    sort_by_start_asc (a :: b :: es)
      = sort_by_start_asc (b :: a :: es).
Proof.
  intros a b es Hneq.
  cbn [sort_by_start_asc].
  apply insert_asc_swap_distinct. exact Hneq.
Qed.

(** Symmetric to [sort_by_start_desc_perm]: sort_by_start_asc is
    Permutation-invariant on distinct-key inputs. *)
Lemma sort_by_start_asc_perm :
  forall es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    sort_by_start_asc es1 = sort_by_start_asc es2.
Proof.
  intros es1 es2 Hperm. induction Hperm as
      [| a l1 l2 Hp IH | a b l | l1 l2 l3 Hp1 IH1 Hp2 IH2]; intros Hd.
  - (* perm_nil *) reflexivity.
  - (* perm_skip *)
    cbn [sort_by_start_asc].
    apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall Hd].
    rewrite (IH Hd). reflexivity.
  - (* perm_swap: same direction issue as the desc proof *)
    apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall_b Hd1].
    apply distinct_starts_cons_iff in Hd1. destruct Hd1 as [Hall_a _].
    inversion Hall_b as [|? ? Hneq _]. subst.
    symmetry.
    apply (sort_by_start_asc_insert_swap a b l).
    intros Heq. apply Hneq. symmetry. exact Heq.
  - (* perm_trans *)
    rewrite (IH1 Hd).
    assert (Hd2 : distinct_starts l2)
      by (apply (distinct_starts_perm l1 l2 Hp1 Hd)).
    rewrite (IH2 Hd2). reflexivity.
Qed.

(** Inductive descending_sorted's mirror for ascending. *)
Inductive ascending_sorted : list edit -> Prop :=
  | ascending_sorted_nil : ascending_sorted []
  | ascending_sorted_singleton : forall e, ascending_sorted [e]
  | ascending_sorted_cons :
      forall e1 e2 rest,
        e1.(e_start) <= e2.(e_start) ->
        ascending_sorted (e2 :: rest) ->
        ascending_sorted (e1 :: e2 :: rest).

(** Symmetric to [insert_desc_preserves_sorted]. *)
Lemma insert_asc_preserves_sorted :
  forall e es,
    ascending_sorted es ->
    ascending_sorted (insert_asc e es).
Proof.
  intros e es Hes. induction Hes as [|e0|e1 e2 rest Hle Hsorted IH].
  - simpl. constructor.
  - simpl. destruct (Nat.leb (e_start e) (e_start e0)) eqn:Hle0.
    + apply Nat.leb_le in Hle0.
      apply ascending_sorted_cons; [exact Hle0 | constructor].
    + apply Nat.leb_nle in Hle0.
      simpl. apply ascending_sorted_cons.
      * lia.
      * constructor.
  - simpl. destruct (Nat.leb (e_start e) (e_start e1)) eqn:Hle1.
    + apply Nat.leb_le in Hle1.
      apply ascending_sorted_cons; [exact Hle1 |].
      apply ascending_sorted_cons; assumption.
    + apply Nat.leb_nle in Hle1.
      simpl in IH. simpl.
      destruct (Nat.leb (e_start e) (e_start e2)) eqn:Hle2.
      * apply Nat.leb_le in Hle2.
        apply ascending_sorted_cons; [lia |].
        apply ascending_sorted_cons; [exact Hle2 | exact Hsorted].
      * apply Nat.leb_nle in Hle2.
        apply ascending_sorted_cons; [exact Hle | exact IH].
Qed.

(** Symmetric to [sort_by_start_desc_sorted]. *)
Lemma sort_by_start_asc_sorted :
  forall es, ascending_sorted (sort_by_start_asc es).
Proof.
  induction es as [|e rest IH]; simpl.
  - constructor.
  - apply insert_asc_preserves_sorted. exact IH.
Qed.

(** Symmetric to [sort_by_start_desc_id_when_sorted]. *)
Lemma sort_by_start_asc_id_when_sorted :
  forall es, ascending_sorted es -> sort_by_start_asc es = es.
Proof.
  intros es Hes. induction Hes as [|e0|e1 e2 rest Hle Hsorted IH].
  - reflexivity.
  - simpl. reflexivity.
  - change (sort_by_start_asc (e1 :: e2 :: rest))
      with (insert_asc e1 (sort_by_start_asc (e2 :: rest))).
    rewrite IH.
    cbn [insert_asc].
    assert (Nat.leb (e_start e1) (e_start e2) = true) as Hleb.
    { apply Nat.leb_le. exact Hle. }
    rewrite Hleb. reflexivity.
Qed.

(** ── Cursor-universal Stage 1 zero-admit witness ──────────────────── *)

Definition apply_edits_cursor_universal_stage1_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 cursor-universal STAGE 2 — sort_by_start_desc = rev (sort_by_start_asc)
    ─────────────────────────────────────────────────────────────────

    Per `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` Stage 2.
    The bridge between the two sort directions.  For distinct-starts
    inputs, descending sort = reverse of ascending sort (because
    insertion sort produces a uniquely-determined output on
    distinct keys).

    Strategy: the abstract path via permutation + sortedness
    uniqueness.  Both `sort_by_start_desc es` and
    `rev (sort_by_start_asc es)` are descending-sorted permutations
    of `es`; on distinct-keys inputs the sort is unique. *)

(** [insert_desc] preserves the multiset (Permutation). *)
Lemma insert_desc_perm :
  forall e es, Permutation (e :: es) (insert_desc e es).
Proof.
  intros e es. induction es as [|x rest IH]; simpl.
  - apply Permutation_refl.
  - destruct (Nat.leb (e_start x) (e_start e)).
    + apply Permutation_refl.
    + change (Permutation (e :: x :: rest) (x :: insert_desc e rest)).
      apply (perm_trans (perm_swap _ _ _)). apply perm_skip. exact IH.
Qed.

(** [insert_asc] preserves the multiset. *)
Lemma insert_asc_perm :
  forall e es, Permutation (e :: es) (insert_asc e es).
Proof.
  intros e es. induction es as [|x rest IH]; simpl.
  - apply Permutation_refl.
  - destruct (Nat.leb (e_start e) (e_start x)).
    + apply Permutation_refl.
    + change (Permutation (e :: x :: rest) (x :: insert_asc e rest)).
      apply (perm_trans (perm_swap _ _ _)). apply perm_skip. exact IH.
Qed.

(** [sort_by_start_desc] produces a permutation of input. *)
Lemma sort_by_start_desc_perm_self :
  forall es, Permutation es (sort_by_start_desc es).
Proof.
  induction es as [|e rest IH]; simpl.
  - apply Permutation_refl.
  - apply (perm_trans (perm_skip _ IH)). apply insert_desc_perm.
Qed.

(** [sort_by_start_asc] produces a permutation of input. *)
Lemma sort_by_start_asc_perm_self :
  forall es, Permutation es (sort_by_start_asc es).
Proof.
  induction es as [|e rest IH]; simpl.
  - apply Permutation_refl.
  - apply (perm_trans (perm_skip _ IH)). apply insert_asc_perm.
Qed.

(** Helper: appending a smaller-start element to a descending-sorted
    list ending in e_last (where e_new.start ≤ e_last.start)
    preserves descending_sorted. *)
Lemma descending_sorted_app_smaller :
  forall xs e_last e_new,
    descending_sorted (xs ++ [e_last]) ->
    e_new.(e_start) <= e_last.(e_start) ->
    descending_sorted (xs ++ [e_last; e_new]).
Proof.
  induction xs as [|x rest IH]; intros e_last e_new H Hle.
  - cbn. apply descending_sorted_cons; [exact Hle | constructor].
  - cbn.
    destruct rest as [|y rest'].
    + (* xs = [x], so list = [x; e_last] *)
      cbn in H. inversion H. subst.
      apply descending_sorted_cons; [assumption |].
      apply descending_sorted_cons; [exact Hle | constructor].
    + (* xs = x :: y :: rest', list = x :: y :: rest' ++ [e_last] *)
      cbn in H. inversion H. subst.
      apply descending_sorted_cons; [assumption |].
      apply IH; [assumption | exact Hle].
Qed.

(** Reverse of ascending-sorted is descending-sorted. *)
Lemma rev_ascending_sorted :
  forall xs, ascending_sorted xs -> descending_sorted (rev xs).
Proof.
  intros xs Hxs. induction Hxs as [|e0|e1 e2 rest Hle Hsorted IH].
  - simpl. constructor.
  - simpl. constructor.
  - (* xs = e1 :: e2 :: rest, ascending; IH: descending_sorted (rev (e2 :: rest)) *)
    simpl. (* goal: descending_sorted ((rev rest ++ [e2]) ++ [e1]) *)
    rewrite <- app_assoc.
    cbn [app].
    apply descending_sorted_app_smaller.
    + simpl in IH. exact IH.
    + exact Hle.
Qed.

(** [descending_sorted] head dominates: the head of a descending list
    has the maximum start.  Use [revert e] before induction so the IH
    quantifies over the "head" parameter. *)
Lemma descending_sorted_head_max :
  forall e xs,
    descending_sorted (e :: xs) ->
    forall x, In x xs -> x.(e_start) <= e.(e_start).
Proof.
  intros e xs. revert e. induction xs as [|y rest IH]; intros e Hsorted x Hin.
  - inversion Hin.
  - inversion Hsorted; subst.
    destruct Hin as [Heq | Hin].
    + subst. assumption.
    + assert (x.(e_start) <= y.(e_start)) as Hxy
        by (apply (IH y); assumption).
      lia.
Qed.

(** Distinct-keys descending-sorted permutations are equal.
    Standard sort-uniqueness result. *)
Lemma desc_sorted_perm_eq_distinct :
  forall xs ys,
    descending_sorted xs ->
    descending_sorted ys ->
    distinct_starts xs ->
    Permutation xs ys ->
    xs = ys.
Proof.
  induction xs as [|x rest IH]; intros ys Hxs Hys Hd Hperm.
  - apply Permutation_nil in Hperm. symmetry. exact Hperm.
  - destruct ys as [|y rest_y].
    + apply Permutation_sym in Hperm. apply Permutation_nil in Hperm. discriminate.
    + (* xs = x :: rest, ys = y :: rest_y, both descending *)
      assert (Hx_in_ys : In x (y :: rest_y))
        by (apply (Permutation_in _ Hperm); simpl; left; reflexivity).
      assert (Hy_in_xs : In y (x :: rest))
        by (apply (Permutation_in _ (Permutation_sym Hperm));
            simpl; left; reflexivity).
      (* x and y are both heads of descending-sorted lists.  In both
         lists, the head has the max start.  By Permutation, the
         multisets match.  By distinct_starts, equal-start ⇒ equal. *)
      assert (Hx_max : forall z, In z (x :: rest) -> z.(e_start) <= x.(e_start)).
      { intros z [Heqz | Hinz]; [subst; lia |].
        apply (descending_sorted_head_max x rest Hxs z Hinz). }
      assert (Hy_max : forall z, In z (y :: rest_y) -> z.(e_start) <= y.(e_start)).
      { intros z [Heqz | Hinz]; [subst; lia |].
        apply (descending_sorted_head_max y rest_y Hys z Hinz). }
      assert (Hxs_eq : x.(e_start) = y.(e_start)).
      { assert (Hxy : x.(e_start) <= y.(e_start)) by (apply Hy_max; exact Hx_in_ys).
        assert (Hyx : y.(e_start) <= x.(e_start)) by (apply Hx_max; exact Hy_in_xs).
        lia. }
      (* From distinct_starts on (x :: rest), x's start is unique among rest's
         starts.  Combined with Hx_in_ys (x ∈ ys), and Hxs_eq (y has same start
         as x), and y ∈ ys, we need y = x. *)
      assert (Hxy_eq : x = y).
      { (* If x ≠ y, then both x and y are in (y :: rest_y) (since x ∈ ys,
           y ∈ ys = head). Permutation pulls one copy of x into ys. The
           Permutation also gives us NoDup of starts (preserved); since
           x.start = y.start and distinct_starts ⇒ same start ⇒ same element
           in the original (x ∈ rest contradicting NoDup). *)
        apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall_x Hd_rest].
        destruct Hx_in_ys as [Hxy | Hx_in_rest_y].
        - symmetry. exact Hxy.
        - (* x ∈ rest_y; since y :: rest_y permutes with x :: rest, and y ≠ x
             (assumed), x must be in rest. *)
          (* Better: use the start-uniqueness directly. x.start = y.start, and
             y ∈ x :: rest. If y ≠ x, then y ∈ rest, but y.start = x.start
             contradicts all_starts_neq x rest. *)
          destruct Hy_in_xs as [Hyx | Hy_in_rest].
          + exact Hyx.
          + exfalso. unfold all_starts_neq in Hall_x.
            rewrite Forall_forall in Hall_x.
            apply (Hall_x y Hy_in_rest). exact Hxs_eq. }
      subst y.
      f_equal.
      (* Now show rest = rest_y from Permutation and inductive hypothesis. *)
      apply IH.
      * inversion Hxs as [| e0 He0 | e1 e2 rest' _ Hsorted Heq]; subst.
        -- (* rest = [] *)
           destruct rest_y as [|y2 rest_y2].
           ++ constructor.
           ++ (* Permutation [x] (x :: y2 :: rest_y2) impossible *)
              exfalso. apply Permutation_length in Hperm. simpl in Hperm. lia.
        -- exact Hsorted.
      * inversion Hys as [| e0 He0 | e1 e2 rest' _ Hsorted Heq]; subst.
        -- (* rest_y = [] *)
           destruct rest as [|x2 rest2].
           ++ constructor.
           ++ exfalso. apply Permutation_length in Hperm. simpl in Hperm. lia.
        -- exact Hsorted.
      * apply distinct_starts_cons_iff in Hd. destruct Hd as [_ Hd_rest].
        exact Hd_rest.
      * apply Permutation_cons_inv with (a := x). exact Hperm.
Qed.

(** ── Stage 2 substantive bridge ───────────────────────────────────── *)

(** Bridge lemma: descending sort = reverse of ascending sort, on
    distinct-starts inputs.  Used by Stage 4's sequential-descending
    shape lemma to relate the parallel applier (descending sort + fold
    [apply_edits_concrete]) to the cursor walk (ascending sort +
    cursor walk). *)
Theorem sort_by_start_desc_eq_rev_asc :
  forall es,
    distinct_starts es ->
    sort_by_start_desc es = rev (sort_by_start_asc es).
Proof.
  intros es Hd.
  apply (desc_sorted_perm_eq_distinct
           (sort_by_start_desc es)
           (rev (sort_by_start_asc es))).
  - apply sort_by_start_desc_sorted.
  - apply rev_ascending_sorted. apply sort_by_start_asc_sorted.
  - (* distinct_starts (sort_by_start_desc es) — distinct_starts is
       Permutation-stable; sort_by_start_desc is a permutation. *)
    apply (distinct_starts_perm es (sort_by_start_desc es)
             (sort_by_start_desc_perm_self es) Hd).
  - (* Permutation (sort_by_start_desc es) (rev (sort_by_start_asc es)) *)
    apply (perm_trans (Permutation_sym (sort_by_start_desc_perm_self es))).
    apply (perm_trans (sort_by_start_asc_perm_self es)).
    apply Permutation_rev.
Qed.

(** Sanity Examples for [sort_by_start_desc_eq_rev_asc].  Cover empty,
    singleton, two-edit, and three-edit lists; reflexivity suffices
    for fully-evaluable concrete inputs. *)
Example sort_desc_eq_rev_asc_empty :
  sort_by_start_desc (@nil edit) = rev (sort_by_start_asc (@nil edit)).
Proof. reflexivity. Qed.

Example sort_desc_eq_rev_asc_singleton :
  let e1 := mk_edit 3 4 [49] in
  sort_by_start_desc [e1] = rev (sort_by_start_asc [e1]).
Proof. reflexivity. Qed.

Example sort_desc_eq_rev_asc_two :
  let e1 := mk_edit 5 6 [49] in
  let e2 := mk_edit 1 2 [50] in
  sort_by_start_desc [e1; e2] = rev (sort_by_start_asc [e1; e2]).
Proof. reflexivity. Qed.

Example sort_desc_eq_rev_asc_three :
  let e1 := mk_edit 7 8 [49] in
  let e2 := mk_edit 1 2 [50] in
  let e3 := mk_edit 4 5 [51] in
  sort_by_start_desc [e1; e2; e3] = rev (sort_by_start_asc [e1; e2; e3]).
Proof. reflexivity. Qed.

(** ── Cursor-universal Stage 2 zero-admit witness ──────────────────── *)

Definition apply_edits_cursor_universal_stage2_zero_admits : True := I.
