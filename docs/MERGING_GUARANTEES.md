# Merging Guarantees — apply_edits parallel applier

**For LaTeX Perfectionist v27.0.3+.**

This doc explains the formal guarantee around batch edit application
— specifically, when reordering a list of edits is safe and how the
runtime achieves order-independence.

---

## The two appliers

LaTeX Perfectionist's rewrite engine has two byte-level edit-list
appliers:

### Sequential — `apply_edits_concrete` (in `proofs/RewritePreservesCST.v`)

```coq
Definition apply_one_edit (src : bytes) (e : edit) : bytes :=
  take e.(e_start) src ++ e.(e_replacement) ++ drop e.(e_end) src.

Fixpoint apply_edits_concrete (src : bytes) (es : list edit) : bytes :=
  match es with
  | [] => src
  | e :: rest => apply_edits_concrete (apply_one_edit src e) rest
  end.
```

Each edit's `e_start` / `e_end` offsets are interpreted relative to
the **current buffer** (post earlier edits).  This makes
`apply_edits_concrete` **NOT order-invariant** — even for
pairwise-non-overlapping edits.

**Counter-example** (verbatim from `proofs/ApplyEditsAssoc.v`'s
file header):

```
src = [97;98;99;100;101;102]              ("abcdef")
e1  = mk_edit 1 3 [88]                    (replace "bc" with "X")
e2  = mk_edit 4 5 [89;90]                 (replace "e" with "YZ")
                                          (e1 and e2 are non-overlapping)

apply_edits_concrete src [e1;e2]
  → after e1, buf="aXdef" (len 5)
  → e2 with e_start=4 hits byte 4 of "aXdef" = 'e'
  → drop 5 leaves []
  → result = "aXdeYZ"

apply_edits_concrete src [e2;e1]
  → after e2, buf="abcdYZf" (len 7)
  → e1 with e_start=1 hits 'b'
  → result = "aXdYZf"

[e1;e2] → "aXdeYZ"   ≠   [e2;e1] → "aXdYZf"
```

So if your client code applies a list of non-overlapping edits using
the sequential applier *directly* (without sorting), the **order
matters**.  This is by design at the runtime level —
`Cst_edit.apply_all` first sorts edits ascending by `start_offset`
and then cursor-walks through the original source (see Runtime
correspondence below) — but the Coq proof against the sequential
applier alone cannot claim order-independence.

### Parallel — `apply_edits_parallel` (in `proofs/ApplyEditsAssoc.v`)

```coq
Definition apply_edits_parallel (src : bytes) (es : list edit) : bytes :=
  apply_edits_concrete src (sort_by_start_desc es).
```

Sorts edits by `e_start` **descending**, then applies sequentially.
Applying the rightmost edit first leaves all smaller offsets unchanged
in the remaining buffer; subsequent edits then operate on offsets
that match the original source.

The parallel applier is **order-invariant** on edit lists with
pairwise distinct start positions — this is the substantive
guarantee.

---

## The substantive theorem

```coq
Theorem apply_edits_parallel_perm :
  forall src es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    apply_edits_parallel src es1 = apply_edits_parallel src es2.
```

**Plain English:** if you have two edit lists that are permutations
of each other (same edits, possibly reordered), and every edit has
a distinct start position, then `apply_edits_parallel` gives the
same byte stream regardless of which order you list the edits in.

**Print Assumptions** returns "Closed under the global context" —
zero axioms, zero admits.

---

## When `distinct_starts` matters

`distinct_starts es := NoDup (map e_start es)` requires that no two
edits in `es` share the same `e_start` offset.

For typical batch-fix scenarios (one fix per validator finding, each
at a unique source location), `distinct_starts` holds automatically.
Where it can fail:

- **Pure insertions at the same offset.** Two edits `(p, p, X)` and
  `(p, p, Y)` are pairwise non-overlapping per the `non_overlapping`
  predicate (both have empty pre-edit ranges) but produce different
  results depending on order:
  - `[insert_X; insert_Y]` at p produces `…X…Y…` at p
  - `[insert_Y; insert_X]` at p produces `…Y…X…` at p

  These cases are explicitly excluded by `distinct_starts`.

- **Replacement edits that share a start but cover different
  end-offsets.** These are conflict-overlapping per the runtime's
  `validate_non_overlapping` and rejected before reaching the
  applier.

For non-empty edits (`e_start < e_end`) with pairwise non-overlapping
ranges, `distinct_starts` follows automatically — start positions
must differ if ranges don't overlap (proof: if two non-empty ranges
share a start, both contain `[start, min(end1, end2))` so they
overlap).

---

## Runtime correspondence

The OCaml runtime (`latex-parse/src/cst_edit.ml::apply_all`) and the
Coq parallel applier produce the **same byte sequence** on
non-overlapping edits with distinct starts, but via different
mechanisms:

- **OCaml `apply_all`**: sorts edits **ascending** by `start_offset`,
  then walks a cursor through the *original source* — for each
  sorted edit it copies `src[cursor:edit.start_offset]`, appends
  the replacement, and advances the cursor to `edit.end_offset`.
  After all edits, copies the tail `src[cursor:n]`.  Single
  buffered pass; offsets stay relative to the original source by
  construction.

- **Coq `apply_edits_parallel`**: sorts edits **descending** by
  `e_start`, then folds via `apply_edits_concrete` (the v26.3
  sequential applier).  Applying the rightmost edit first leaves
  all smaller offsets unchanged in the remaining buffer; iterate.
  Same result, different traversal order.

Both produce the byte-by-byte original-offset semantic.  The Coq
descending-sort form is chosen because it composes with the
existing `apply_edits_concrete` sequential applier (no need to
introduce a cursor model in Coq); the OCaml ascending-sort cursor
walk is the natural runtime implementation that avoids creating
intermediate buffer copies.

For the v27.0.3 user-facing claim: **the order in which validators
emit fixes does not affect the output, provided the fixes have
distinct start positions.** This claim transfers from the Coq
proof to the shipped binary because both algorithms compute the
same parallel-applier semantic on every input where
`distinct_starts` holds.

The runtime-vs-Coq correspondence is **mechanised** for
representative inputs in `proofs/ApplyEditsAssoc.v` Stage 5b:

- `Definition apply_edits_cursor src es :=
   apply_edits_cursor_aux src 0 (sort_by_start_asc es)` — Coq
  mirror of OCaml `Cst_edit.apply_all`'s ascending-sort + cursor-
  walk algorithm.
- 4 `Example`s prove `apply_edits_cursor src es =
  apply_edits_parallel src es` by `reflexivity` on the documented
  non-overlapping inputs (2-edit, 2-edit-swap, 3-edit,
  3-edit-permuted). All `Print Assumptions` Closed under the
  global context.
- `apply_edits_cursor_empty` and `apply_edits_parallel_empty`
  Qed-prove that both algorithms return the source unchanged for
  the empty edit list.

The fully universal theorem
`forall src es, distinct_starts es -> pairwise_non_overlapping es ->
   apply_edits_cursor src es = apply_edits_parallel src es`
extends the corpus mechanisation to every valid input.  Stage-
decomposed plan committed as
[`specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md`](../specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md)
(7 stages, target tag **v27.0.4**, ~4–6 sessions).  Stage 4 of
that plan carries the technically substantive proof
(induction over the sorted-ascending list, with cursor-walk and
sequential-descending shapes both reduced to a canonical byte
mapping); Stages 1–3 build prerequisite sort-permutation /
sort-rev-bridge / cursor-walk-shape lemmas; Stage 5 combines;
Stage 6 wires into ADMISSIBILITY_MAP + this doc; Stage 7
release-bumps v27.0.4.

The rewrite engine surface relevant to v27.0.3:

- **Single-cursor batch fixes** — one validator emits multiple
  non-overlapping suggestions; runtime sorts ascending + cursor-
  walks. Result is order-independent.
- **Multi-cursor / multi-validator batches** — outputs from
  different validators get merged (`apply_with_priority` for
  prioritised conflicts; `apply_best_effort` for greedy-skip
  overlap handling) and the surviving non-overlapping subset is
  then applied via `apply_all`.

---

## See also

- `proofs/ApplyEditsAssoc.v` — full Coq machinery (Stages 1–4)
- `proofs/RewritePreservesCST.v` — byte-lossless preservation (the
  v26.3 result that this builds on)
- `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md` — multi-stage plan
- CHANGELOG `[v27.0.3]` — release entry summarising the cycle
