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
the sequential applier, the **order matters**.  This is by design at
the runtime level — `Cst_edit.apply_all` does its own sorting before
applying — but the Coq proof against the sequential applier alone
cannot claim order-independence.

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

The OCaml runtime's `Cst_edit.apply_all` already performs descending-
by-start sorting before applying edits.  The Coq parallel applier
mirrors that runtime behaviour, so the Coq guarantee transfers
directly to the shipped binary's behaviour on:

- **Single-cursor batch fixes** — one validator emits multiple
  non-overlapping suggestions; the runtime sorts and applies them.
  Result is order-independent.
- **Multi-cursor / multi-validator batches** — outputs from
  different validators get merged (per
  `apply_edits_concrete_with_priorities` for prioritised conflicts)
  and the surviving set is then applied in parallel-applier order.

For the v27.0.3 user-facing claim: **the order in which validators
emit fixes does not affect the output, provided the fixes have
distinct start positions.**

---

## See also

- `proofs/ApplyEditsAssoc.v` — full Coq machinery (Stages 1–4)
- `proofs/RewritePreservesCST.v` — byte-lossless preservation (the
  v26.3 result that this builds on)
- `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md` — multi-stage plan
- CHANGELOG `[v27.0.3]` — release entry summarising the cycle
