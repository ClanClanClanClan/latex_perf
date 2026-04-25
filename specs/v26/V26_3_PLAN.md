# V26.3 — Full deferred-list discharge

**Status:** draft, 2026-04-25. Successor to `V26_2_1_PLAN.md`.
**Scope:** every item in `V26_2_1_PLAN.md` §8 plus the residue from
`V26_2_PLAN.md` §13 that v26.2.1 didn't pick up.
**Cadence:** multi-PR cycle, mixed-effort. Tag target depends on
which subset lands first.

## 0. Pre-conditions (verified 2026-04-25 on main `6474c00`)

- `dune build` green; `dune runtest latex-parse/src` green.
- `pre_release_check.py --skip-build` → 16/16 PASS.
- `run_differential_test.py --baseline-ref v26.2.0 --current-ref HEAD
  --corpus corpora/lint --expected-diff-keys ""` → 0 diffs / 330 files.
- v26.2.1 tag pushed; GitHub Release workflow `in_progress`.

## 1. Inventory of deferred items

### 1.1 Closed before v26.3 began

- `specs/v26/partial_document_semantics.yaml` — already shipped in
  v26.2.0 (88 lines). The §10 `V26_2_PLAN.md` deferral was
  retroactively closed by PR #263. **No work needed.**
- v26.0 §15.1 EDF deadline-bug rename — already done. The current
  `edf_scheduler.task.priority` is correctly typed and labelled NOT
  a wall-clock deadline.

### 1.2 Tractable in this cycle (target: ship in v26.3.0)

| Item | Effort | Source |
|---|---|---|
| **A. BOM-aware STRUCT-001 insertion** | Small (~50 LoC + test) | v26.2.1 PR §6 R3 fixture deferred note |
| **B. `--apply-fixes-for RULE-ID` CLI flag** | Small (~80 LoC + tests) | `V26_2_PLAN.md` §3.2 B3, `V26_2_1_PLAN.md` §8 |
| **C. CST structure-lossless runtime gate** | Small (~120 LoC + new test) | `V26_2_1_PLAN.md` §8, `CHANGELOG.md` v26.2.0 |
| **D. `RewritePreservesCST.apply_total` Section closure** | Small-Medium (concrete `apply_edits` + close section) | `ADMISSIBILITY_MAP.md` |
| **E. Rolling fix producers — first batch (10 rules)** | Medium (~300 LoC + tests) | `V26_2_1_PLAN.md` §8 |
| **F. xelatex `.aux` parser variant** | Medium (~200 LoC + test fixture) | `V26_2_PLAN.md` §10 |
| **G. lualatex `.aux` parser variant** | Medium (similar to F) | `V26_2_PLAN.md` §10 |
| **H. `edf_scheduler.ml` per-class proper rewrite** | Medium-Large (~250 LoC + tests) | memo §11.2 |

### 1.3 Multi-cycle scope (defer to v26.3.1 / v26.4 / v27)

The following items genuinely cannot be completed in a single
session and span multiple weeks each. v26.3.0 ships without them
but commits to delivering each in a numbered successor:

| Item | Estimated scope | Target |
|---|---|---|
| **CSTRoundTrip Section_lossless full discharge** (2 hypotheses, structure-lossless) | Multi-week — needs concrete `cst_abs` partition model + parse/serialize functions + Coq induction over `Cst_of_ast.fill_nodes` | v26.3.1 |
| **RewritePreservesSemantics Semantic_preservation full discharge** (2 hypotheses) | Multi-week — needs minimal Coq tokenizer model on trivia chunks | v26.3.1 |
| **Rolling fix producers — remaining ~647 rules** | Months at ~10 rules/week | v26.4 / ongoing |
| **L3 AST migration** (per `docs/L3_ROADMAP.md`) | Multi-month — new `ast_semantic_state.ml` + label/ref switch + parity gate | v26.4 / v27 |

The boundary between 1.2 and 1.3 is *honest scope* — see
`v26_2_audit_lessons.md` "gates lie if their scope is wrong".
Promising the v26.3 cycle ships items it physically cannot complete
in time would repeat the v26.2.0 stale-governance bug.

## 2. Non-goals

- No new memo §17 v27 work (editorial / collaboration / platform).
- No engine support beyond pdflatex / xelatex / lualatex `.aux`.
- No `--apply-fixes-by-severity` flag (out of v26.3 scope).
- No `result.fix` field changes — the v26.2.1 type is final.

## 3. PR slate (in-cycle)

### PR #1 (this cycle, single branch initially): plan + execution

A bundle of A–H from §1.2 lands on `v26.3/cycle`. Each item is its
own commit on the branch for reviewability. The branch then becomes
the v26.3.0 release-bump PR (analogous to v26.2.1 PR #270).

If the branch grows beyond ~10 commits or any single item proves
larger than its estimate, the cycle splits into stacked PRs.

### Item details

#### A. BOM-aware STRUCT-001 insertion

`require_documentclass` in `validators_l0.ml`: detect leading UTF-8
BOM (`\xEF\xBB\xBF`) and place the inserted `\documentclass` AFTER
the BOM (offset 3) instead of before (offset 0). Update the BOM
fixture's expected output in `corpora/fixtures/v26_2_1/README.md`
and the E2E test assertion in `test_rule_fix_integration.ml`.

#### B. `--apply-fixes-for RULE-ID` CLI flag

`validators_cli.ml` gains a new mode: `--apply-fixes-for ID file.tex`
filters the collected fix list to results where `r.id = ID` before
applying. Same overlap-handling and output as `--apply-fixes`. Tests
in `test_apply_fixes_cli.ml`: applying STRUCT-001 only via
`--apply-fixes-for STRUCT-001` ignores TYPO-002 fixes on a mixed
source.

#### C. CST structure-lossless runtime gate

New script `scripts/tools/check_cst_structure_lossless.py` (gate #17)
that runs the existing `test_cst_roundtrip` on a curated subset
(LP-Core fixtures under 1MB, no unclosed constructs) and asserts
re-parse-after-serialize equality. New runtime test
`test_cst_structure_lossless.ml` exercises the corpus subset.

#### D. `RewritePreservesCST.apply_total` Section closure

Define `apply_edits_concrete : bytes -> list edit -> bytes` in Coq:

```coq
Definition apply_one_edit (src : bytes) (e : edit) : bytes :=
  take e.(e_start) src ++ e.(e_replacement) ++ drop e.(e_end) src.

Fixpoint apply_edits_concrete (src : bytes) (es : list edit) : bytes :=
  match es with
  | [] => src
  | e :: rest => apply_edits_concrete (apply_one_edit src e) rest
  end.
```

Prove `apply_total_concrete : forall src es, exists out,
apply_edits_concrete src es = out` (trivially) and emit unconditional
versions of the Section's two theorems
(`rewrite_preserves_byte_lossless`, `rewrite_empty_preserves`). Update
`ADMISSIBILITY_MAP.md` "DISCHARGED in
`RewritePreservesCST.apply_edits_concrete`" annotation.

#### E. Rolling fix producers — first batch

Pick 10 high-value, mechanically-fixable rules:

1. TYPO-022 (space before closing punctuation) — delete the space.
2. TYPO-027 (multiple `!`) — replace `‼` with single `!` or `‼`.
3. TYPO-033 (`et.al` without space) — replace with `et al.`.
4. TYPO-035 (French NBSP) — insert NBSP before `; : ! ?`.
5. TYPO-037 (space before comma) — delete the space.
6. STRUCT-002 (empty section title) — insert placeholder `{Untitled}`.
7. ENC-002 (BOM in middle) — delete BOM occurrence.
8. SPC-012 (BOM not at file start) — delete interior BOMs.
9. TYPO-018 (multiple consecutive spaces) — replace runs with single
   space.
10. TYPO-024 (dangling dash at line end) — delete the trailing dash.

Each ships with at least one assert in the producer's existing test
file, plus an entry in `corpora/fixtures/v26_2_1/` if useful.

#### F. xelatex `.aux` parser variant

Audit current `aux_state.ml` for pdflatex-specific assumptions.
xelatex's `.aux` format is largely identical (`\newlabel`,
`\bibcite`, etc.) but may use UTF-8 encoded labels and emit
`\@writefile` differently. Ship a `Engine` parameter on the
parser entry point (`Aux_state.of_string ~engine`) and a regression
fixture (`corpora/aux/xelatex_minimal.aux`) confirming round-trip.

#### G. lualatex `.aux` parser variant

Same as F. lualatex `.aux` adds `\luaentry` and possibly
luatex-specific font records. v26.3.0 ships best-effort recognition
with documented limitations.

#### H. `edf_scheduler.ml` per-class proper rewrite

Memo §11.2 mandates per-class scheduling beyond the v26.1
priority-offset wiring. v26.3 lands a proper class-tier queue:
separate priority queues per class A/B/C/D, drained in tier order
(A first, then B, C, D), each tier internally ordered by the
existing priority within class. Tests in `test_edf_scheduler.ml`
confirm class-tier dominance under contended schedules.

### PR #2: release-bump for v26.3.0

Once items A–H ship and gates are 17/17 (gate #17 added by C):
`scripts/release.sh 26.3.0` → bump → PR → tag.

## 4. Gates

**New gates added by this cycle:**
- C: `check_cst_structure_lossless.py` (gate #17).

Total at v26.3.0 tag: **17 pre-release gates**.

## 5. Out-of-cycle commitments

Items in §1.3 each get their own scoped plan files in this repo
(`V26_3_1_PLAN.md`, `V26_4_PLAN.md`) when they begin. Do not start
them speculatively from this cycle's branch.

## 6. First concrete action

This file is created on branch `v26.3/cycle`. The next commit on
that branch is item A (BOM-aware STRUCT-001 insertion). Subsequent
commits land items B–H in order. Each commit verifies build + tests
+ the relevant gate before being committed.
