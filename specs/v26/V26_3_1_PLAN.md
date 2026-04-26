# V26.3.1 — First successor cycle for v26.3 deferred work

**Status:** draft, 2026-04-26. Successor to `V26_3_PLAN.md` §5 commitment.
**Scope:** the three multi-week items from `V26_3_PLAN.md` §1.3 that are
narrow enough to land as one tagged release, plus the next rolling
fix-producer batch.
**Cadence:** multi-PR cycle, mixed-effort. Tag target depends on which
subset lands first; the batch plus at least one Coq discharge gates the
tag.

## 0. Pre-conditions (verified 2026-04-26 on `main` `c96e367`)

- v26.3.0 tagged at `81fa8a2`; Release workflow green.
- 17/17 pre-release gates PASS on `main`.
- Differential test 0 diffs across 330 corpus files vs `v26.3.0`.
- `spec-drift` workflow is a required-check on `main`
  (post-PR #276); `messages-validate` runs strict.
- All known silent-failure scope/regex bugs in pre-release gates closed
  (PRs #273, #277, #278); each gate now reports its input count or
  refuses to silent-pass on empty input.

## 1. Inventory of in-scope items

### 1.1 Rolling fix-producer batch (next 10 rules)

The 13 fix producers shipped in v26.2.1 + v26.3.0 cover the highest-
visibility mechanical typos (STRUCT-001/002, TYPO-002/003/018/022/024/
027/033/035/037, ENC-002, SPC-012). The next batch aims at rules with
deterministic single-pass fixes that don't require sentence- or
context-sensitive analysis:

1. **TYPO-005** — Ellipsis `...` → `\dots`.
2. **TYPO-006** — Tab character U+0009 → four spaces (configurable).
3. **TYPO-007** — Trailing spaces at end of line → strip.
4. **TYPO-008** — Multiple consecutive blank lines (> 2) → collapse to 2.
5. **TYPO-013** — ASCII back-tick ` as opening quote → curly U+2018.
6. **TYPO-004** — TeX double back-tick `` ``…'' `` → curly U+201C/U+201D.
7. **SPC-002** — Line containing only whitespace → empty line.
8. **SPC-003** — Hard tab in mixed-indent line → spaces (preserve depth).
9. **TYPO-021** — Capital after ellipsis without space → insert space.
10. **TYPO-009** — `~` at line start (non-breaking space at column 0) → strip.

Each ships with at least one assert in the producer's existing test
file plus, where the fixture corpus benefits, a new `corpora/fixtures/
v26_2_1/` entry. The integration test (`test_rule_fix_integration.ml`)
gains one E2E case per rule.

### 1.2 `CSTRoundTrip.Section_lossless` discharge

Per `proofs/ADMISSIBILITY_MAP.md`, the `Section Structure_lossless`
in `proofs/CSTRoundTrip.v` has two hypotheses (`builder_partitions`,
`parse_serialize_is_id_on_subset`) that must discharge together. The
v26.3.1 target is a concrete instantiation:

- `ast := bytes` (or a `list token` projection — TBD at implementation).
- `parse := identity` for the bridge case, with a richer projection
  added if `parse_serialize_is_id_on_subset` requires it.
- `builder := byte_lossless_singleton` ↔ a single `mk_cst_abs src`
  node (matches the OCaml `CUnparsed` fallback at the abstract level)
  for the byte-lossless half; richer multi-node decomposition added
  for the structure-lossless half once the subset predicate is fixed.
- `in_subset` defined (initial draft: "no `\begin`/`\end` mismatch
  at the byte level").

The discharge produces unconditional theorems mirroring the
in-section ones. `proofs/ADMISSIBILITY_MAP.md` annotation flips from
HYPOTHESIS-PARAMETRIC to "DISCHARGED in v26.3.1
`CSTRoundtripConcrete.v`" (or equivalent file name).

This is multi-week. The plan reserves a separate PR for it; partial
progress lands as commits on the v26.3.1 branch with each commit
preserving `dune build` greenness.

### 1.3 `RewritePreservesSemantics.Semantic_preservation` discharge

Two hypotheses (`tokens_ws_empty`, `tokens_concat`) must discharge
together. `tokens_ws_empty` is mechanical against any tokenizer that
treats whitespace as trivia. `tokens_concat` requires restricting the
hypothesis to non-command whitespace chunks because real `Parser_l2`
has lookahead (e.g. `\[`).

Discharge plan:
- Define a minimal Coq tokenizer model on trivia-only chunks
  (whitespace, line endings).
- Restrict `in_subset` to inputs that contain only trivia (initial
  cut), or to source positions away from command tokens (richer cut).
- Prove both hypotheses against this restricted model.
- Update `proofs/ADMISSIBILITY_MAP.md` accordingly.

Same multi-week character as §1.2; lands as a separate PR.

## 2. Non-goals

- **L3 AST migration** (`docs/L3_ROADMAP.md`) — multi-month, defer to
  v26.4 / v27.
- **Conflict-aware rewrite merging** (`V26_2_PLAN.md` line 631) —
  defer to a `V26_4_PLAN.md` if and when that file opens.
- **T6 / T7 discharge against `PdflatexModel.v`** — v27 WS8.
- **More than 10 fix producers** in §1.1 — disciplined batch size
  to keep the PR reviewable; the next batch becomes v26.3.2 or
  v26.4 PR #1 depending on cadence.

## 3. PR slate

### PR #1 — v26.3.1 plan + fix-producer batch

This commit introduces `V26_3_1_PLAN.md` and lands the 10 fix
producers from §1.1 on a single branch (`v26.3.1/plan-and-fix-batch`).
Each rule is its own commit on the branch for reviewability. Tests
in `validators_l0_typo.ml` / `validators_l0.ml` smoke files plus an
extension to `test_rule_fix_integration.ml`.

### PR #2 — `CSTRoundTrip` discharge

Single-purpose PR for §1.2. Adds `proofs/CSTRoundtripConcrete.v` (or
extends `CSTRoundTrip.v`); updates `ADMISSIBILITY_MAP.md`.

### PR #3 — `RewritePreservesSemantics` discharge

Single-purpose PR for §1.3.

### PR #4 — release-bump for v26.3.1

Once §1.1–§1.3 ship and gates remain 17/17:
`scripts/release.sh 26.3.1` → bump → PR → tag.

## 4. Gates

No new pre-release gates are added by this cycle. The existing
`check_fix_integration_wired` gate covers the new fix producers
implicitly via the `test_rule_fix_integration.ml` extension.

Total at v26.3.1 tag: **17 pre-release gates** (unchanged from v26.3.0).

## 5. Out-of-cycle commitments

The remaining v26.3 deferral residue lands in successor cycles:

- Conflict-aware rewrite merging → `V26_4_PLAN.md` (when opened).
- L3 AST migration → `V26_4_PLAN.md` or v27 entry plan.
- Rolling fix-producer batches beyond §1.1 → ongoing per
  `V26_3_PLAN.md` §1.3 commitment.
- T6/T7 discharge → v27 WS8 entry plan.

## 6. Differential-test budget

`run_differential_test.py` against `v26.3.0` is expected to show:

- **0 diffs** for the corpus files that don't exercise the 10 new
  fix producers. The fix producers themselves are gated by the
  existing `--apply-fixes` / `--apply-fixes-for` flags; default
  output (no `--apply-fixes`) is unchanged.
- The PR description must declare any deviation explicitly with a
  reason.

## 7. First concrete action

This file is created on branch `v26.3.1/plan-and-fix-batch`. The
next commits land the 10 fix producers in order (TYPO-005 first).
Subsequent PRs (#2, #3) open separate branches and reference this
plan.
