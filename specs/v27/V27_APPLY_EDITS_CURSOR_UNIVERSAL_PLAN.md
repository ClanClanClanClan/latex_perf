# V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN — universal cursor-walk = parallel-applier theorem

**Goal:** Universally Qed-prove that the Coq cursor-walk applier
(`apply_edits_cursor`, OCaml-runtime mirror) equals the parallel
applier (`apply_edits_parallel`, defined via descending sort) for
all valid edit lists.  Strengthens the v27.0.3 corpus-level
mechanisation (4 reflexivity Examples on representative inputs)
to a universal Coq theorem.

**Tag target:** v27.0.4 (small patch release; pure proof, 0
runtime change, ~80–200 LoC of Coq).

**Scope estimate:** 4–6 sessions across stages.

**Predecessor work (DONE in v27.0.3 cycle):**
- `proofs/ApplyEditsAssoc.v` Stage 5b: `apply_edits_cursor`
  Definition + 4 corpus-level Examples (`apply_edits_cursor_matches
  _parallel_*`) + empty-list base lemmas.

## Headline theorem

```coq
Theorem apply_edits_cursor_eq_parallel :
  forall (src : bytes) (es : list edit),
    distinct_starts es ->
    pairwise_non_overlapping es ->
    (forall e, In e es -> edit_wf e) ->
    (forall e, In e es -> e.(e_end) <= length src) ->
    apply_edits_cursor src es = apply_edits_parallel src es.
```

This is the universal extension of the v27.0.3 corpus mechanisation.
Once shipped, the `MERGING_GUARANTEES.md` claim "OCaml `apply_all`
and Coq `apply_edits_parallel` produce the same byte sequence on
non-overlapping distinct-starts edits" is mechanically backed for
**all** valid inputs, not just the documented examples.

## Stage decomposition

### Stage 1 — sort-asc/sort-desc Permutation lemmas
**Branch:** `v27.0/cursor-univ-stage1-sort-perm`

Symmetric versions of the existing Stage 4 sort-desc lemmas:
- `Lemma insert_asc_swap_distinct` (Qed) — symmetric to
  `insert_desc_swap_distinct`
- `Lemma sort_by_start_asc_perm` (Qed) — symmetric to
  `sort_by_start_desc_perm`
- `Lemma sort_by_start_asc_sorted` (Qed) — sort produces ascending
  order.  (Originally named `_sorted_ascending` in this plan; renamed
  during PR #325 to mirror the existing `sort_by_start_desc_sorted`
  symbol.)
- `Lemma sort_by_start_asc_id_when_sorted` (Qed) — identity on
  already-sorted-ascending input

**Acceptance:** all 4 Qed; all `Print Assumptions` Closed.  (PR
#325 actually shipped 6 lemmas + 1 Inductive `ascending_sorted`;
see the cycle-acceptance checklist at the end of this file for the
full list.)

### Stage 2 — sort_asc/sort_desc are reverses on distinct-starts inputs
**Branch:** `v27.0/cursor-univ-stage2-rev-bridge`

Key bridging lemma:

```coq
Lemma sort_by_start_desc_eq_rev_asc :
  forall es,
    distinct_starts es ->
    sort_by_start_desc es = rev (sort_by_start_asc es).
```

**Proof strategy:** induction on `es`. Base: `[] = rev []`.
Inductive: `sort_desc (e :: rest) = insert_desc e (sort_desc rest)`,
and `sort_asc (e :: rest) = insert_asc e (sort_asc rest)`. Show
`insert_desc e xs = rev (insert_asc e (rev xs))` for sorted xs.

This connects the descending and ascending forms structurally.

**Acceptance:** Lemma Qed; tested via Examples.

### Stage 3 — cursor-walk shape lemma
**Branch:** `v27.0/cursor-univ-stage3-cursor-shape`

Prove that `apply_edits_cursor_aux` on sorted-ascending
non-overlapping input produces a specific shape:

```coq
Lemma apply_edits_cursor_aux_shape :
  forall (src : bytes) (cursor : nat) (es : list edit),
    Sorted_ascending_by_start es ->        (* head smallest *)
    Pairwise_non_overlapping_from cursor es ->
    All_in_bounds src cursor es ->
    apply_edits_cursor_aux src cursor es =
    cursor_walk_canonical src cursor es.
```

Where `cursor_walk_canonical` is a non-recursive byte-mapping
function that directly produces the expected concatenation of
gap-prefixes + replacements + tail.

This isolates the cursor-walk's structural output independent of
the recursion shape.

**Acceptance:** Lemma Qed.

### Stage 4 — sequential-descending shape lemma
**Branch:** `v27.0/cursor-univ-stage4-seq-shape`

Symmetric: prove that `apply_edits_concrete src (rev sorted_asc)`
produces the same canonical byte mapping for valid inputs.

```coq
Lemma apply_edits_concrete_rev_sorted_shape :
  forall (src : bytes) (sorted_asc : list edit),
    Sorted_ascending_by_start sorted_asc ->
    Pairwise_non_overlapping sorted_asc ->
    All_in_bounds src 0 sorted_asc ->
    apply_edits_concrete src (rev sorted_asc) =
    cursor_walk_canonical src 0 sorted_asc.
```

**Proof strategy:** induct on `sorted_asc`. For `e :: rest`, the
descending sequential applier processes `rev rest ++ [e]`:
- After applying `rev rest` (the smaller-start edits all to the
  right of `e.e_end`), the buffer has source[0..e.e_start)
  unchanged + processed-rest tail.
- Final `apply_one_edit` for `e` splices `e.replacement` at
  `e.e_start`.
- Recurse via IH on `rest`.

This is the technically interesting stage — needs careful manipulation
of `take`/`drop`/`firstn`/`skipn` over the partial buffer.

**Acceptance:** Lemma Qed.

### Stage 5 — combine into the universal theorem
**Branch:** `v27.0/cursor-univ-stage5-combine`

Combine Stages 1–4 into the headline:

```coq
Theorem apply_edits_cursor_eq_parallel :
  forall src es,
    distinct_starts es ->
    pairwise_non_overlapping es ->
    (forall e, In e es -> edit_wf e) ->
    (forall e, In e es -> e.(e_end) <= length src) ->
    apply_edits_cursor src es = apply_edits_parallel src es.
Proof.
  intros src es Hd Hp Hwf Hbnd.
  unfold apply_edits_cursor, apply_edits_parallel.
  rewrite (sort_by_start_desc_eq_rev_asc es Hd).
  rewrite (apply_edits_concrete_rev_sorted_shape src
             (sort_by_start_asc es) ...).
  rewrite <- (apply_edits_cursor_aux_shape src 0
               (sort_by_start_asc es) ...).
  reflexivity.
Qed.
```

**Acceptance:** Theorem Qed; `Print Assumptions` Closed.

### Stage 6 — wire into ADMISSIBILITY_MAP + docs
**Branch:** `v27.0/cursor-univ-stage6-docs`

- Update `proofs/ADMISSIBILITY_MAP.md` "Rewrite engine —
  associative-reorder" entry: add the universal theorem
  reference; mark the v27.0.3 corpus-level mechanisation as
  superseded by Stage 5's universal Qed.
- Update `docs/MERGING_GUARANTEES.md` Runtime correspondence
  section: remove the "achievable via induction; multi-session
  future extension" framing; replace with citation of the
  shipped `apply_edits_cursor_eq_parallel` Theorem.
- Update `proofs/ApplyEditsAssoc.v` file header: mark Stage 5b
  as the corpus-mechanisation, this work as the universal
  extension, and remove the "queued as follow-up" framing.

**Acceptance:** docs reference the actual shipped Theorem; no
"queued / multi-session / future" framing remains for this work.

### Stage 7 — release-bump v27.0.4
**Branch:** `v27.0/cursor-univ-release-bump`

Standard: `scripts/release.sh 27.0.4`, CHANGELOG `[v27.0.4]`
entry, version bumps, post-merge tag.

## Multi-session memory protocol

`~/.claude/.../memory/v27_apply_edits_cursor_universal_status.md`
carries cross-session state per the established WS8 / T5 / apply_edits
template:
1. **What's done** — file:line markers for new theorems; each Qed.
2. **What's next** — the next stage's first concrete action.
3. **State-of-mind** — proof obligations open, pitfalls,
   take/drop/firstn/skipn manipulation tactics that worked vs
   didn't.
4. **Verification numbers** — theorem count delta, gate state.

## Acceptance criteria for the cycle (state at end of Stage 1)

- [x] All Stage 1 sort-asc lemmas Qed (PR #325): shipped
  `insert_asc_swap_distinct`, `sort_by_start_asc_insert_swap`,
  `sort_by_start_asc_perm`, `insert_asc_preserves_sorted`,
  `sort_by_start_asc_sorted`, `sort_by_start_asc_id_when_sorted`,
  plus `ascending_sorted` Inductive (6 lemmas + 1 Inductive,
  +2 over the original 4-lemma plan estimate).
- [ ] Stage 2 `sort_by_start_desc_eq_rev_asc` Qed.
- [ ] Stage 3 cursor-walk shape lemma Qed.
- [ ] Stage 4 sequential-descending shape lemma Qed (the
  technically substantive piece).
- [ ] Stage 5 universal theorem
  `apply_edits_cursor_eq_parallel` Qed.  All `Print Assumptions`
  Closed under the global context.
- [ ] ADMISSIBILITY_MAP "Rewrite engine — associative-reorder"
  entry references the universal theorem.
- [ ] `docs/MERGING_GUARANTEES.md` Runtime correspondence
  section cites the shipped Theorem (no "future extension"
  framing).
- [ ] `proofs/ApplyEditsAssoc.v` file header reflects the
  universal extension as shipped.
- [ ] CHANGELOG `[v27.0.4]` entry.
- [ ] Tag `v27.0.4` on main.

## Why this matters

Without this cycle:
- The MERGING_GUARANTEES claim "OCaml apply_all = Coq
  apply_edits_parallel" is mechanised on 4 representative inputs
  (Stage 5b reflexivity Examples) but not universally.
- The user-facing docs say "achievable via induction; multi-
  session future extension" — exactly the deferral pattern that
  `feedback_no_multi_week_dismissal.md` corrects against.

With this cycle:
- The runtime-Coq correspondence is mechanically certified for
  every valid edit list (any size, any shape that satisfies
  `distinct_starts /\ pairwise_non_overlapping /\ in-bounds`).
- The "queued as future" framing is replaced with a shipped
  theorem reference.
- The OCaml `apply_all` semantics has a Coq-side mirror with a
  proven-equal universal theorem — closing the gap between the
  shipped binary's behaviour and the proof tree.
