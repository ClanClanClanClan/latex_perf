# V27_APPLY_EDITS_ASSOC_PLAN — apply_edits associative-reorder Coq theorem

**Goal:** Prove that `apply_edits_concrete` (the v26.3 byte-edit
applier) is invariant under reordering of non-overlapping edits.
Currently the implementation applies edits sequentially over the
mutating buffer; the spec wants the strong claim that for
non-overlapping edits, the order of application doesn't matter.

**Tag target:** v27.0.x patch or v27.1.x cycle.

**Scope estimate:** 3–5 sessions.

## Why this matters

`apply_edits_concrete` currently has a sequential semantics: edit
N+1 is applied to the buffer after edit N. This means edit N+1's
offsets are interpreted *relative to the post-edit-N buffer*, not
relative to the original source. For overlapping edits this is
necessary; for non-overlapping ones it complicates the spec.

The "parallel-application" form computes all offsets relative to
the original source. The desired theorem:

```coq
Theorem apply_edits_concrete_associative_subset :
  forall (src : list nat) (e1 e2 : edit),
    non_overlapping e1 e2 ->
    apply_edits_concrete src [e1; e2] = apply_edits_concrete src [e2; e1].
```

Currently shipped: `RewritePreservesCST` byte-count invariants.
Missing: associativity / order-independence.

## Stage decomposition

### Stage 1 — Define `non_overlapping`
**Branch:** `v27.0/apply-edits-stage1-non-overlapping`

Add `Definition non_overlapping (e1 e2 : edit) : Prop` to
`proofs/RewriteEngine.v` (or similar). Two edits don't overlap iff
their byte ranges in the original source are disjoint.

```coq
Definition edit_range (e : edit) : nat * nat :=
  (e.(edit_start), e.(edit_start) + e.(edit_old_length)).

Definition non_overlapping (e1 e2 : edit) : Prop :=
  let (s1, e1_end) := edit_range e1 in
  let (s2, e2_end) := edit_range e2 in
  e1_end <= s2 \/ e2_end <= s1.
```

**Acceptance:** Definition + sanity lemmas (decidability,
reflexivity-on-self exclusion, symmetry).

### Stage 2 — Parallel-application Fixpoint
**Branch:** `v27.0/apply-edits-stage2-parallel`

Define a parallel applier that uses original-source offsets:

```coq
Fixpoint apply_edits_parallel_aux (src : list nat) (offset : nat)
                                  (edits : list edit) : list nat := ...

Definition apply_edits_parallel (src : list nat) (edits : list edit)
    : list nat :=
  apply_edits_parallel_aux src 0 (sort_by_start edits).
```

The key insight: sort edits by `edit_start` first, then apply each
in order — this makes the offset bookkeeping straightforward.

**Acceptance:** `apply_edits_parallel` defined; type-checks; one
example test (apply 2 disjoint edits to a 10-byte string).

### Stage 3 — Sort idempotence + sorted equivalence (REVISED)
**Branch:** `v27.0/apply-edits-stage3-equivalence` (PR #321)

**Revision rationale:** the original Stage 3 form
`apply_edits_parallel src edits = apply_edits_concrete src edits`
under `pairwise_non_overlapping edits` is **false** in general —
sequential application interprets each edit's offsets relative to
the *current* (post-earlier-edits) buffer, not the original source.
A pairwise-non-overlapping but not-yet-sorted edit list yields
different sequential vs parallel results.  See PR #320 file-header
counter-example.

The revised Stage 3 ships the structural lemmas Stage 4 needs and
the *correctly-conditioned* parallel-vs-concrete equivalence:

```coq
Inductive descending_sorted : list edit -> Prop := ...

Lemma insert_desc_preserves_sorted          : Qed
Lemma sort_by_start_desc_sorted             : Qed  (* sort produces sorted *)
Lemma insert_desc_id_when_head_le           : Qed
Lemma sort_by_start_desc_id_when_sorted     : Qed  (* sort is id on sorted *)
Lemma sort_by_start_desc_idempotent         : Qed
Lemma apply_edits_parallel_eq_concrete_when_sorted : Qed
```

The Stage 3 headline `apply_edits_parallel_eq_concrete_when_sorted`
is trivial by definition (sort is the identity on already-sorted
input).  Stage 4 carries the substantive content — permutation
invariance for the parallel applier, which is what the v26.4
deferral note actually wanted.

**Acceptance:** all 6 lemmas Qed; `Print Assumptions` Closed.

### Stage 4 — Permutation invariance for the parallel applier (REVISED)
**Branch:** `v27.0/apply-edits-stage4-perm`

**Revision rationale:** the original Stage 4 headline
`apply_edits_concrete src [e1;e2] = apply_edits_concrete src [e2;e1]`
under `non_overlapping e1 e2` is **false** in general (PR #320
counter-example).  The substantive theorem the v26.4 deferral note
wanted is permutation invariance for the *parallel* applier (which
uses original-source offsets):

```coq
Theorem apply_edits_parallel_perm :
  forall (src : list nat) (edits1 edits2 : list edit),
    Permutation edits1 edits2 ->
    distinct_starts edits1 ->         (* unique e_start; rules out
                                         insertions at same point *)
    apply_edits_parallel src edits1 = apply_edits_parallel src edits2.
```

`distinct_starts` (or a similar predicate) is required because
two insertions at the same offset are technically pairwise
non-overlapping per `non_overlapping_self_iff` but apply in
order-dependent fashion.  For genuine non-empty edits with
non-overlapping ranges, `distinct_starts` follows from
`pairwise_non_overlapping`.

**Proof sketch:** show `sort_by_start_desc edits1 = sort_by_start_desc
edits2` when `Permutation edits1 edits2 /\ distinct_starts edits1`
(insertion sort is determined by the multiset of keys when keys
are unique).  Then `apply_edits_parallel = apply_edits_concrete o
sort_by_start_desc` gives equality of outputs.

**Acceptance:** `apply_edits_parallel_perm` Qed; `Print Assumptions`
Closed under the global context.

### Stage 5 — Wire into ADMISSIBILITY_MAP / docs
**Branch:** `v27.0/apply-edits-stage5-docs`

Update `proofs/ADMISSIBILITY_MAP.md` with the new theorem.
`docs/MERGING_GUARANTEES.md` (if exists) gets the spec-level
explanation.

### Stage 6 — Release-bump (patch or minor depending on cumulative scope)
Tag.

## Multi-session memory protocol

`~/.claude/.../memory/v27_apply_edits_assoc_status.md` carries
state.

## Acceptance criteria (state at end of Stage 3)

- [x] `non_overlapping` Definition + decidability + symmetry +
  consistency-with-`edits_conflict` lemmas (Stage 1, PR #319).
- [x] `apply_edits_parallel` Fixpoint defined via
  `sort_by_start_desc` + `apply_edits_concrete` (Stage 2, PR #320).
- [x] Sort idempotence + identity-when-sorted + Stage 3 sorted-
  equivalence headline (Stage 3, PR #321).
- [ ] `apply_edits_parallel_perm` Qed — parallel is permutation-
  invariant on `distinct_starts` inputs (Stage 4 — substantive
  headline; replaces the original false `apply_edits_concrete_
  associative_subset` form).
- [ ] All `Print Assumptions` Closed under the global context.
- [ ] ADMISSIBILITY_MAP updated (Stage 5).
- [ ] CHANGELOG `[v27.0.x]` entry (Stage 6 release-bump).
