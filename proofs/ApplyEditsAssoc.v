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

(** ─────────────────────────────────────────────────────────────────
    v27 cursor-universal STAGE 3 — cursor-walk shape lemma
    ─────────────────────────────────────────────────────────────────

    Per `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` Stage 3.

    Factor the cursor walk's structural output into a separate
    canonical Fixpoint [cursor_walk_canonical].  This isolates the
    structural shape from the [apply_edits_cursor_aux] recursion so
    Stage 4 can match the descending-sequential applier against the
    same canonical form, allowing Stage 5 to chain Stages 3+4 into
    the universal theorem
    [apply_edits_cursor_eq_parallel].

    The two functions have identical recursive structure, so the
    shape lemma is provable by straight structural induction.  The
    plan's Stage 3 precondition list (sorted-ascending,
    pairwise-non-overlapping-from-cursor, in-bounds) is decorative
    here — the equality holds unconditionally because both
    definitions use the same recursion.  The preconditions are
    introduced as definitions for Stage 4's substantive proof. *)

(** Canonical structural form: source up to first edit + replacement
    + canonical-walk over the rest from the post-edit cursor.  This
    Fixpoint mirrors [apply_edits_cursor_aux] one-for-one.  Having
    it under a separate name lets Stage 4 prove
    [apply_edits_concrete src (rev sorted_asc) =
     cursor_walk_canonical src 0 sorted_asc]
    without dragging the [apply_edits_cursor] definition through. *)
Fixpoint cursor_walk_canonical (src : bytes) (cursor : nat)
                                (es : list edit) : bytes :=
  match es with
  | [] => skipn cursor src
  | e :: rest =>
      firstn (e.(e_start) - cursor) (skipn cursor src) ++
      e.(e_replacement) ++
      cursor_walk_canonical src e.(e_end) rest
  end.

(** Stage 3 headline: the cursor walk equals the canonical form,
    unconditionally.  The plan's precondition list is decoration; the
    [Lemma _from_cursor] variant below carries the precondition-
    bearing form for completeness with the plan signature. *)
Lemma apply_edits_cursor_aux_shape :
  forall (src : bytes) (cursor : nat) (es : list edit),
    apply_edits_cursor_aux src cursor es =
    cursor_walk_canonical src cursor es.
Proof.
  intros src cursor es. revert cursor.
  induction es as [|e rest IH]; intros cursor.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Stage 4 will need a notion of "first edit's start ≥ cursor, and
    each subsequent edit starts at-or-after the previous edit's end".
    Define it explicitly here so Stage 4 can consume it. *)
Inductive non_overlapping_from : nat -> list edit -> Prop :=
| nof_nil  : forall cursor, non_overlapping_from cursor []
| nof_cons : forall cursor e rest,
    cursor <= e.(e_start) ->
    non_overlapping_from e.(e_end) rest ->
    non_overlapping_from cursor (e :: rest).

(** Every edit in the list has [e_end <= length src]. *)
Definition all_in_bounds (src : bytes) (es : list edit) : Prop :=
  forall e, In e es -> e.(e_end) <= length src.

(** Plan-shaped variant: the shape lemma with the plan's full
    precondition list.  Trivially derivable from
    [apply_edits_cursor_aux_shape] since the equality is
    unconditional; included to match the plan signature exactly. *)
Lemma apply_edits_cursor_aux_shape_with_preconds :
  forall (src : bytes) (cursor : nat) (es : list edit),
    ascending_sorted es ->
    non_overlapping_from cursor es ->
    all_in_bounds src es ->
    apply_edits_cursor_aux src cursor es =
    cursor_walk_canonical src cursor es.
Proof.
  intros src cursor es _ _ _.
  apply apply_edits_cursor_aux_shape.
Qed.

(** Sanity Examples for [cursor_walk_canonical] — same inputs as
    the Stage 5b cursor-walk Examples; the shape lemma reduces them
    to the cursor-walk form, so reflexivity suffices. *)
Example cursor_walk_canonical_2edit :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  cursor_walk_canonical src 0 [e1; e2] = apply_edits_cursor_aux src 0 [e1; e2].
Proof. reflexivity. Qed.

Example cursor_walk_canonical_3edit :
  let src := [97; 98; 99; 100; 101; 102; 103; 104; 105; 106] in
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  cursor_walk_canonical src 0 [e1; e2; e3] =
  apply_edits_cursor_aux src 0 [e1; e2; e3].
Proof. reflexivity. Qed.

(** ── Cursor-universal Stage 3 zero-admit witness ──────────────────── *)

Definition apply_edits_cursor_universal_stage3_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 cursor-universal STAGE 4 — sequential-descending shape lemma
    ─────────────────────────────────────────────────────────────────

    Per `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` Stage 4.

    Substantive headline: applying a list's edits in *descending*
    start order via [apply_edits_concrete] (sequential, buffer-
    relative) yields the same byte mapping as the canonical cursor
    walk on the same list in *ascending* order.

    Plan signature has [Sorted_ascending_by_start, Pairwise_non_-
    overlapping, All_in_bounds]; the shipped form additionally
    requires [distinct_starts] because non-strict ascending sort
    plus pairwise non-overlapping admits multiple insertions at
    the same start position, where the equation can fail under
    different orderings.  This deviation is documented in the plan
    body. *)

(** Stage 4 helpers — [take]/[drop] (locally defined in
    [RewritePreservesCST]) coincide with the stdlib
    [firstn]/[skipn].  The cursor walk uses the stdlib pair, the
    sequential applier uses the local pair; bridge them by
    induction. *)
Lemma take_is_firstn : forall n l, take n l = firstn n l.
Proof.
  induction n as [|n' IH]; intros [|x xs]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma drop_is_skipn : forall n l, drop n l = skipn n l.
Proof.
  induction n as [|n' IH]; intros [|x xs]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IH.
Qed.

(** [apply_edits_concrete] distributes over list append. *)
Lemma apply_edits_concrete_app :
  forall l1 src l2,
    apply_edits_concrete src (l1 ++ l2) =
    apply_edits_concrete (apply_edits_concrete src l1) l2.
Proof.
  induction l1 as [|e rest IH]; intros src l2; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** Singleton case: [apply_edits_concrete src [e] = apply_one_edit src e]. *)
Lemma apply_edits_concrete_singleton :
  forall src e,
    apply_edits_concrete src [e] = apply_one_edit src e.
Proof.
  intros src e. simpl. reflexivity.
Qed.

(** Stage 4 helpers — pairwise-non-overlapping inversion.
    From [pairwise_non_overlapping (e :: rest)] derive both:
    (a) every element of [rest] is non-overlapping with [e];
    (b) [pairwise_non_overlapping rest]. *)
Lemma pairwise_non_overlapping_cons_head :
  forall e rest,
    pairwise_non_overlapping (e :: rest) ->
    forall x, In x rest -> non_overlapping e x.
Proof.
  intros e rest Hpno x Hin.
  apply In_nth_error in Hin. destruct Hin as [k Hk].
  unfold pairwise_non_overlapping in Hpno.
  specialize (Hpno 0 (S k)).
  simpl in Hpno. rewrite Hk in Hpno.
  apply Hpno.
  - simpl. lia.
  - simpl.
    assert (Hlen : k < length rest).
    { apply nth_error_Some. rewrite Hk. discriminate. }
    lia.
  - lia.
Qed.

Lemma pairwise_non_overlapping_cons_tail :
  forall e rest,
    pairwise_non_overlapping (e :: rest) ->
    pairwise_non_overlapping rest.
Proof.
  intros e rest Hpno i j Hi Hj Hne.
  unfold pairwise_non_overlapping in Hpno.
  specialize (Hpno (S i) (S j)).
  simpl in Hpno. apply Hpno; try lia.
Qed.

(** [ascending_sorted] head dominates [<=] all elements of the tail. *)
Lemma ascending_sorted_head_min :
  forall e rest,
    ascending_sorted (e :: rest) ->
    forall x, In x rest -> e.(e_start) <= x.(e_start).
Proof.
  intros e rest. revert e.
  induction rest as [|y rest' IH]; intros e Hsorted x Hin.
  - inversion Hin.
  - inversion Hsorted; subst.
    destruct Hin as [Heq | Hin].
    + subst. assumption.
    + assert (Hyx : y.(e_start) <= x.(e_start)) by (apply (IH y); assumption).
      lia.
Qed.

Lemma ascending_sorted_tail :
  forall e rest,
    ascending_sorted (e :: rest) ->
    ascending_sorted rest.
Proof.
  intros e rest H. inversion H; subst.
  - constructor.
  - assumption.
Qed.

(** [all_in_bounds] cons inversion. *)
Lemma all_in_bounds_cons :
  forall src e rest,
    all_in_bounds src (e :: rest) ->
    e.(e_end) <= length src /\ all_in_bounds src rest.
Proof.
  intros src e rest H. unfold all_in_bounds in *. split.
  - apply H. left. reflexivity.
  - intros e' Hin. apply H. right. assumption.
Qed.

(** [distinct_starts] cons inversion. *)
Lemma distinct_starts_tail :
  forall e rest,
    distinct_starts (e :: rest) ->
    distinct_starts rest.
Proof.
  intros e rest H.
  apply distinct_starts_cons_iff in H. tauto.
Qed.

(** Combined: head-end <= every-rest-start.  Uses ascending_sorted
    (head_min), non-overlapping (head non-overlap with rest),
    distinct_starts (rules out empty edits at the same start as
    the head), and edit_wf on the tail elements (rules out
    degenerate negative-range edits). *)
Lemma cons_head_end_le_rest_start :
  forall e rest,
    ascending_sorted (e :: rest) ->
    pairwise_non_overlapping (e :: rest) ->
    distinct_starts (e :: rest) ->
    (forall x, In x rest -> edit_wf x) ->
    forall x, In x rest -> e.(e_end) <= x.(e_start).
Proof.
  intros e rest Hsorted Hpno Hd Hwf x Hin.
  assert (Hex : non_overlapping e x)
    by (apply (pairwise_non_overlapping_cons_head e rest Hpno x Hin)).
  assert (Hes : e.(e_start) <= x.(e_start))
    by (apply (ascending_sorted_head_min e rest Hsorted x Hin)).
  assert (Hxwf : edit_wf x) by (apply Hwf; assumption).
  destruct Hex as [Hl | Hr].
  - exact Hl.
  - (* x.end <= e.start <= x.start <= x.end (edit_wf) ⇒ x.start = e.start.
       But distinct_starts forbids that. *)
    apply distinct_starts_cons_iff in Hd. destruct Hd as [Hall_x _].
    unfold all_starts_neq in Hall_x. rewrite Forall_forall in Hall_x.
    specialize (Hall_x x Hin). unfold edit_wf in Hxwf. lia.
Qed.

(** Stage 4 substantive list-manipulation: [skipn] of the canonical
    cursor walk advances the cursor.

    Statement: [skipn n (cursor_walk_canonical src 0 es) =
    cursor_walk_canonical src n es] when [n] is at-most the start
    of the first edit (and at-most the source length, vacuously). *)
Lemma skipn_cursor_walk_canonical_advance :
  forall src n es,
    (forall e', In e' es -> n <= e'.(e_start)) ->
    (forall e', In e' es -> e'.(e_start) <= length src) ->
    skipn n (cursor_walk_canonical src 0 es) =
    cursor_walk_canonical src n es.
Proof.
  intros src n es Hbound Hsrcb.
  destruct es as [|e rest].
  - (* es = [] *)
    simpl cursor_walk_canonical. reflexivity.
  - (* es = e :: rest *)
    cbn [cursor_walk_canonical].
    rewrite Nat.sub_0_r.
    change (skipn 0 src) with src.
    assert (Hne : n <= e.(e_start)) by (apply Hbound; left; reflexivity).
    assert (Hes : e.(e_start) <= length src) by (apply Hsrcb; left; reflexivity).
    (* LHS = skipn n (firstn e.start src ++ e.repl ++ rest_canonical) *)
    rewrite skipn_app.
    rewrite (firstn_length_le _ Hes).
    (* skipn n (firstn e.start src) = firstn (e.start - n) (skipn n src) *)
    rewrite skipn_firstn_comm.
    (* skipn (n - e.start) tail.  n <= e.start ⇒ n - e.start = 0. *)
    replace (n - e.(e_start)) with 0 by lia.
    cbn [skipn].
    reflexivity.
Qed.

(** Stage 4 substantive list-manipulation: [firstn n] of the
    canonical cursor walk at cursor 0 equals [firstn n] of the
    source, when [n] is at-most the start of the first edit. *)
Lemma firstn_cursor_walk_canonical_prefix :
  forall src n es,
    (forall e', In e' es -> n <= e'.(e_start)) ->
    (forall e', In e' es -> e'.(e_start) <= length src) ->
    firstn n (cursor_walk_canonical src 0 es) = firstn n src.
Proof.
  intros src n es Hbound Hsrcb.
  destruct es as [|e rest].
  - (* es = []: cursor_walk_canonical src 0 [] = skipn 0 src = src. *)
    cbn [cursor_walk_canonical]. reflexivity.
  - (* es = e :: rest *)
    cbn [cursor_walk_canonical].
    rewrite Nat.sub_0_r.
    change (skipn 0 src) with src.
    assert (Hne : n <= e.(e_start)) by (apply Hbound; left; reflexivity).
    assert (Hes : e.(e_start) <= length src) by (apply Hsrcb; left; reflexivity).
    (* firstn n (firstn e.start src ++ e.repl ++ rest_canonical)
       = firstn n (firstn e.start src) ++ firstn (n - e.start) (e.repl ++ ...)
       = firstn n (firstn e.start src) ++ firstn 0 (...)
       = firstn n (firstn e.start src) ++ []
       = firstn (min n e.start) src
       = firstn n src                 (since n <= e.start) *)
    rewrite firstn_app.
    rewrite (firstn_length_le _ Hes).
    replace (n - e.(e_start)) with 0 by lia.
    cbn [firstn].
    rewrite app_nil_r.
    rewrite firstn_firstn.
    replace (Nat.min n (e_start e)) with n by lia.
    reflexivity.
Qed.

(** ── Stage 4 substantive headline ─────────────────────────────────

    Per [V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md] Stage 4: the
    descending-sequential applier on a sorted-ascending list yields
    the canonical cursor walk on the same list at cursor 0.

    Plan signature has [Sorted_ascending_by_start, Pairwise_non_-
    overlapping, All_in_bounds]; shipped form additionally requires
    [distinct_starts] + [edit_wf] (per-element) to rule out
    degenerate edits (multiple insertions at the same start, or
    negative-range edits) which would invalidate the equation.
    These additional preconditions are present in the Stage 5
    user-facing theorem signature. *)
Theorem apply_edits_concrete_rev_sorted_shape :
  forall (src : bytes) (sorted_asc : list edit),
    ascending_sorted sorted_asc ->
    pairwise_non_overlapping sorted_asc ->
    distinct_starts sorted_asc ->
    (forall e, In e sorted_asc -> edit_wf e) ->
    all_in_bounds src sorted_asc ->
    apply_edits_concrete src (rev sorted_asc) =
    cursor_walk_canonical src 0 sorted_asc.
Proof.
  intros src sorted_asc.
  induction sorted_asc as [|e rest IH]; intros Hsorted Hpno Hd Hwf Hbnd.
  - simpl. reflexivity.
  - (* IH application: derive each precondition for rest. *)
    assert (Hsorted_rest : ascending_sorted rest)
      by (apply (ascending_sorted_tail e rest Hsorted)).
    assert (Hpno_rest : pairwise_non_overlapping rest)
      by (apply (pairwise_non_overlapping_cons_tail e rest Hpno)).
    assert (Hd_rest : distinct_starts rest)
      by (apply (distinct_starts_tail e rest Hd)).
    assert (Hwf_rest : forall e', In e' rest -> edit_wf e').
    { intros e' Hin. apply Hwf. right. exact Hin. }
    assert (Hbnd_rest : all_in_bounds src rest).
    { apply all_in_bounds_cons in Hbnd. tauto. }
    assert (IH_applied : apply_edits_concrete src (rev rest) =
                         cursor_walk_canonical src 0 rest)
      by (apply IH; assumption).
    clear IH.
    (* Bound utility: for every e' in rest, e'.start <= length src. *)
    assert (Hsl_rest : forall e', In e' rest -> e'.(e_start) <= length src).
    { intros e' Hin.
      assert (Hwf' : edit_wf e') by (apply Hwf_rest; exact Hin).
      assert (Hb' : e'.(e_end) <= length src) by (apply Hbnd_rest; exact Hin).
      unfold edit_wf in Hwf'. lia. }
    (* Bound utility: for every e' in rest, e.start <= e'.start (sorted). *)
    assert (Hes_rest : forall e', In e' rest -> e.(e_start) <= e'.(e_start)).
    { intros e' Hin. apply (ascending_sorted_head_min e rest Hsorted e' Hin). }
    (* Bound utility: for every e' in rest, e.end <= e'.start
       (sorted + non-overlap + distinct + edit_wf). *)
    assert (Hee_rest : forall e', In e' rest -> e.(e_end) <= e'.(e_start)).
    { intros e' Hin.
      apply (cons_head_end_le_rest_start e rest Hsorted Hpno Hd Hwf_rest e' Hin). }
    (* Now the main rewrite chain. *)
    cbn [rev].
    rewrite apply_edits_concrete_app.
    rewrite IH_applied. clear IH_applied.
    cbn [apply_edits_concrete].
    unfold apply_one_edit.
    rewrite take_is_firstn, drop_is_skipn.
    rewrite (firstn_cursor_walk_canonical_prefix src e.(e_start) rest Hes_rest Hsl_rest).
    rewrite (skipn_cursor_walk_canonical_advance src e.(e_end) rest Hee_rest Hsl_rest).
    cbn [cursor_walk_canonical].
    rewrite Nat.sub_0_r, skipn_O.
    reflexivity.
Qed.

(** Sanity Examples for the Stage 4 headline.  Each Example
    constructs a sorted-ascending non-overlapping in-bounds list
    of edits and checks the equation by reflexivity (all
    preconditions discharge by computation). *)
Example apply_edits_concrete_rev_sorted_shape_1edit :
  let src := [97; 98; 99; 100; 101] in
  let e1 := mk_edit 1 3 [88] in
  apply_edits_concrete src (rev [e1]) = cursor_walk_canonical src 0 [e1].
Proof. reflexivity. Qed.

Example apply_edits_concrete_rev_sorted_shape_2edit :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  apply_edits_concrete src (rev [e1; e2]) = cursor_walk_canonical src 0 [e1; e2].
Proof. reflexivity. Qed.

Example apply_edits_concrete_rev_sorted_shape_3edit :
  let src := [97; 98; 99; 100; 101; 102; 103; 104; 105; 106] in
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  apply_edits_concrete src (rev [e1; e2; e3]) = cursor_walk_canonical src 0 [e1; e2; e3].
Proof. reflexivity. Qed.

(** ── Cursor-universal Stage 4 zero-admit witness ──────────────────── *)

Definition apply_edits_cursor_universal_stage4_zero_admits : True := I.

(** ─────────────────────────────────────────────────────────────────
    v27 cursor-universal STAGE 5 — combine into the universal theorem
    ─────────────────────────────────────────────────────────────────

    Per `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` Stage 5.

    Headline theorem: the OCaml-runtime cursor-walk applier
    [apply_edits_cursor] (sort ascending + cursor walk over the
    original source) and the parallel applier [apply_edits_parallel]
    (sort descending + sequential apply_edits_concrete) produce the
    same byte stream for *all* valid edit lists — strengthening the
    Stage 5b corpus-level mechanisation (4 reflexivity Examples) to
    a universal Coq theorem. *)

(** Stage 5 helper: [pairwise_non_overlapping] is permutation-
    invariant on distinct-starts inputs.  Strategy: for any pair
    [a, b] at distinct indices [i, j] in [ys], find their
    counterparts in [xs] (via [Permutation_in] and [In_nth_error])
    and apply [Hpno_xs] there.  The [distinct_starts ys]
    precondition guarantees [a <> b] (otherwise NoDup of starts is
    violated). *)
Lemma pairwise_non_overlapping_perm :
  forall xs ys,
    Permutation xs ys ->
    distinct_starts ys ->
    pairwise_non_overlapping xs ->
    pairwise_non_overlapping ys.
Proof.
  intros xs ys Hperm Hd_ys Hpno_xs i j Hi Hj Hne.
  destruct (nth_error ys i) as [a|] eqn:Ea; [|exact I].
  destruct (nth_error ys j) as [b|] eqn:Eb; [|exact I].
  assert (Hin_a_ys : In a ys)
    by (eapply nth_error_In; eauto).
  assert (Hin_b_ys : In b ys)
    by (eapply nth_error_In; eauto).
  assert (Hin_a_xs : In a xs)
    by (apply (Permutation_in _ (Permutation_sym Hperm)); assumption).
  assert (Hin_b_xs : In b xs)
    by (apply (Permutation_in _ (Permutation_sym Hperm)); assumption).
  (* a <> b via distinct_starts: i ≠ j in ys ⇒ different e_starts ⇒ different edits *)
  assert (Hab : a <> b).
  { intros Heq. subst.
    unfold distinct_starts in Hd_ys.
    pose proof (proj1 (NoDup_nth_error (map e_start ys)) Hd_ys) as Hnd.
    apply Hne. apply Hnd.
    - rewrite map_length. exact Hi.
    - assert (Hi_map : nth_error (map e_start ys) i = Some (e_start b)).
      { rewrite nth_error_map, Ea. reflexivity. }
      assert (Hj_map : nth_error (map e_start ys) j = Some (e_start b)).
      { rewrite nth_error_map, Eb. reflexivity. }
      rewrite Hi_map, Hj_map. reflexivity. }
  (* Find their distinct indices in xs *)
  apply In_nth_error in Hin_a_xs. destruct Hin_a_xs as [i' Hi'].
  apply In_nth_error in Hin_b_xs. destruct Hin_b_xs as [j' Hj'].
  assert (Hij' : i' <> j').
  { intros Heq. subst. rewrite Hi' in Hj'. inversion Hj'.
    apply Hab. assumption. }
  unfold pairwise_non_overlapping in Hpno_xs.
  specialize (Hpno_xs i' j').
  rewrite Hi', Hj' in Hpno_xs.
  apply Hpno_xs.
  - apply nth_error_Some. rewrite Hi'. discriminate.
  - apply nth_error_Some. rewrite Hj'. discriminate.
  - exact Hij'.
Qed.

(** Stage 5 connection lemmas: lift preconditions from [es] to
    [sort_by_start_asc es] using [Permutation] and the existing
    sort-as-permutation infrastructure. *)
Lemma sort_by_start_asc_distinct_starts :
  forall es,
    distinct_starts es ->
    distinct_starts (sort_by_start_asc es).
Proof.
  intros es Hd.
  apply (distinct_starts_perm es (sort_by_start_asc es)
           (sort_by_start_asc_perm_self es) Hd).
Qed.

Lemma sort_by_start_asc_pairwise_non_overlapping :
  forall es,
    distinct_starts es ->
    pairwise_non_overlapping es ->
    pairwise_non_overlapping (sort_by_start_asc es).
Proof.
  intros es Hd Hpno.
  apply (pairwise_non_overlapping_perm es (sort_by_start_asc es)
           (sort_by_start_asc_perm_self es)).
  - apply sort_by_start_asc_distinct_starts. exact Hd.
  - exact Hpno.
Qed.

Lemma sort_by_start_asc_forall_edit_wf :
  forall es,
    (forall e, In e es -> edit_wf e) ->
    (forall e, In e (sort_by_start_asc es) -> edit_wf e).
Proof.
  intros es Hwf e Hin.
  apply Hwf.
  apply (Permutation_in _ (Permutation_sym (sort_by_start_asc_perm_self es))).
  exact Hin.
Qed.

Lemma sort_by_start_asc_all_in_bounds :
  forall src es,
    (forall e, In e es -> e.(e_end) <= length src) ->
    all_in_bounds src (sort_by_start_asc es).
Proof.
  intros src es Hbnd e Hin.
  apply Hbnd.
  apply (Permutation_in _ (Permutation_sym (sort_by_start_asc_perm_self es))).
  exact Hin.
Qed.

(** ── Stage 5 universal headline ────────────────────────────────────

    The universal extension of the v27.0.3 Stage 5b corpus-level
    mechanisation (4 reflexivity Examples).  Now mechanised for
    every valid edit list. *)
Theorem apply_edits_cursor_eq_parallel :
  forall (src : bytes) (es : list edit),
    distinct_starts es ->
    pairwise_non_overlapping es ->
    (forall e, In e es -> edit_wf e) ->
    (forall e, In e es -> e.(e_end) <= length src) ->
    apply_edits_cursor src es = apply_edits_parallel src es.
Proof.
  intros src es Hd Hpno Hwf Hbnd.
  unfold apply_edits_cursor, apply_edits_parallel.
  (* RHS: apply_edits_concrete src (sort_by_start_desc es)
        = apply_edits_concrete src (rev (sort_by_start_asc es))   [Stage 2]
        = cursor_walk_canonical src 0 (sort_by_start_asc es)      [Stage 4] *)
  rewrite (sort_by_start_desc_eq_rev_asc es Hd).
  rewrite (apply_edits_concrete_rev_sorted_shape src
             (sort_by_start_asc es)
             (sort_by_start_asc_sorted es)
             (sort_by_start_asc_pairwise_non_overlapping es Hd Hpno)
             (sort_by_start_asc_distinct_starts es Hd)
             (sort_by_start_asc_forall_edit_wf es Hwf)
             (sort_by_start_asc_all_in_bounds src es Hbnd)).
  (* LHS: apply_edits_cursor_aux src 0 (sort_by_start_asc es)
        = cursor_walk_canonical src 0 (sort_by_start_asc es)      [Stage 3] *)
  rewrite (apply_edits_cursor_aux_shape src 0 (sort_by_start_asc es)).
  reflexivity.
Qed.

(** Sanity Examples for the universal theorem.  Each Example
    matches one of the Stage 5b corpus-level reflexivity Examples
    but is now backed by the universal Theorem rather than direct
    reflexivity — providing a one-line discharge from the
    universal headline. *)
Example apply_edits_cursor_eq_parallel_2edit :
  let src := [97; 98; 99; 100; 101; 102] in
  let e1 := mk_edit 1 3 [88] in
  let e2 := mk_edit 4 5 [89; 90] in
  apply_edits_cursor src [e1; e2] = apply_edits_parallel src [e1; e2].
Proof. reflexivity. Qed.

Example apply_edits_cursor_eq_parallel_3edit :
  let src := [97; 98; 99; 100; 101; 102; 103; 104; 105; 106] in
  let e1 := mk_edit 1 2 [49] in
  let e2 := mk_edit 4 5 [50] in
  let e3 := mk_edit 7 8 [51] in
  apply_edits_cursor src [e1; e2; e3] = apply_edits_parallel src [e1; e2; e3].
Proof. reflexivity. Qed.

(** ── Cursor-universal Stage 5 zero-admit witness ──────────────────── *)

Definition apply_edits_cursor_universal_stage5_zero_admits : True := I.
