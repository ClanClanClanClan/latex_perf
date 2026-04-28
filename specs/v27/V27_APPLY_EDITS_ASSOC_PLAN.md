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

### Stage 3 — Equivalence: parallel = sequential for non-overlapping
**Branch:** `v27.0/apply-edits-stage3-equivalence`

Prove:

```coq
Lemma apply_edits_parallel_equals_concrete :
  forall (src : list nat) (edits : list edit),
    pairwise_non_overlapping edits ->
    apply_edits_parallel src edits = apply_edits_concrete src edits.
```

Where `pairwise_non_overlapping := forall i j, i <> j -> non_overlapping (nth i) (nth j)`.

**Acceptance:** Lemma Qed-proved by induction on the edit list.

### Stage 4 — Associativity / reorder
**Branch:** `v27.0/apply-edits-stage4-assoc`

Prove the parallel form is order-independent (since it uses
original-source offsets):

```coq
Lemma apply_edits_parallel_perm :
  forall (src : list nat) (edits1 edits2 : list edit),
    Permutation edits1 edits2 ->
    pairwise_non_overlapping edits1 ->
    apply_edits_parallel src edits1 = apply_edits_parallel src edits2.
```

Combined with Stage 3:

```coq
Theorem apply_edits_concrete_associative_subset :
  forall (src : list nat) (e1 e2 : edit),
    non_overlapping e1 e2 ->
    apply_edits_concrete src [e1; e2] = apply_edits_concrete src [e2; e1].
```

**Acceptance:** Theorem Qed-proved. Closed under the global context.

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

## Acceptance criteria

- [ ] `non_overlapping` Definition + decidability lemma.
- [ ] `apply_edits_parallel` Fixpoint defined.
- [ ] `apply_edits_parallel_equals_concrete` Qed (parallel = sequential
  on non-overlapping edits).
- [ ] `apply_edits_parallel_perm` Qed (parallel is permutation-invariant).
- [ ] `apply_edits_concrete_associative_subset` Qed (the headline).
- [ ] `Print Assumptions` Closed under the global context.
- [ ] ADMISSIBILITY_MAP updated.
- [ ] CHANGELOG entry.
