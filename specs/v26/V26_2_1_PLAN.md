# V26.2.1 — Fix producer track

**Status:** draft, 2026-04-24. Successor to `V26_2_PLAN.md`.
**Scope:** the five fix-producer items CHANGELOG deferred from v26.2.0.
**Cadence:** five PRs, one-per-item, merged sequentially. Target tag: 2026-05-08
(two-week cycle — smaller than v26.1 / v26.2 per `V26_2_PLAN.md` §13).

## 0. Pre-conditions (verified 2026-04-24 on HEAD `830c58b`)

- `dune build` green, `dune runtest latex-parse/src` green.
- `python3 scripts/tools/pre_release_check.py --allow-dirty --skip-build`
  → 14/14 gates PASS (`check_repo_facts`, `check_rule_contracts`,
  `check_regression_gates`, `check_memo_files`, `check_proof_substance`,
  `validate_catalogue`, `check_severity_drift`, `check_mli_doc_coverage`,
  `check_code_quality`, `check_unused_hypotheses`, `check_doc_refs`,
  `check_release_integrity`, `check_gates_meta`, `check_perf_ratchet`).
- `check_memo_files.py` → 115/115 paths resolve.
- No open PRs against main. Four open GitHub issues are historical
  `proof-regression` labels from PR #206/#245 era (April 10–21); not
  v26.2.1 blockers.
- No prior v26.2.1 planning artifacts (no branches, no plan file, no
  issues).

## 1. Verified scope numbers (grep audit)

Prior memory/CHANGELOG claims were stale; re-verified counts used below.

### 1.1 `result` record literal refactor

`grep -c "severity = \(Error\|Warning\|Info\)" latex-parse/src/*.ml`
yields **681 literals across 18 files**. Per-file top (ordered):

| File | Literals |
|---|---|
| `validators_l2.ml` | 204 |
| `validators_l0.ml` | 134 |
| `validators_l1.ml` | 90 |
| `validators_l1_math.ml` | 82 |
| `validators_l0_typo.ml` | 61 |
| `validators_l4_style.ml` | 59 |
| `validators_l3_file.ml` | 19 |
| `validators_l1_expl3.ml` | 12 |
| remainder (10 files) | ≤4 each |

The prior memory claim of "~40" was a 17× under-count. Implication: the
record-literal migration is **not** a manual PR-sized edit; it ships
via a helper-constructor rewrite (§3.1 PR #1 design).

### 1.2 Rule-fix producer scope (target rules verified to exist)

- `STRUCT-001` at `validators_l0.ml:25` (`require_documentclass`),
  gated by `L0_VALIDATORS` pilot mode. Returns `count = 1` on miss.
- `TYPO-002` at `validators_l0_typo.ml:19` (double-hyphen →
  en-dash), dual-mode: token-aware (`L0_TOKEN_AWARE=1`) or
  substring. Returns aggregate `count`, no offsets.
- `TYPO-003` at `validators_l0_typo.ml:62` (triple-hyphen →
  em-dash), same structure as TYPO-002.

**Key finding:** TYPO-002/003 aggregate matches into one `result` with
`count = N`. A fix for N matches needs N edits. Therefore
`result.fix` must be `Cst_edit.t list option`, not `Cst_edit.t option`
as CHANGELOG and memory implied. This plan adopts the `list option`
type; §4 §CHANGELOG deviation notes this.

### 1.3 Rewrite-engine hooks (verified present)

- `Cst_edit.t` private record at `cst_edit.mli:16`.
- `Cst_edit.make / insert / delete / replace` constructors
  (`cst_edit.mli:23-35`).
- `Cst_edit.apply_all : string -> t list -> (string, [\`Overlap of t*t]) result`
  at `cst_edit.mli:61`.
- `Rewrite_engine.apply` + `apply_and_reparse` in `rewrite_engine.mli`.
- `--apply-fixes` / `L0_APPLY_FIXES` NOT present anywhere in
  `latex-parse/src/` or `scripts/` (verified by negative grep).

### 1.4 Section structure of v26.3 Coq targets (out of v26.2.1 scope)

For completeness; these land in v26.3 per `ADMISSIBILITY_MAP.md`:

- `CSTRoundTrip.v` Section `Structure_lossless` (lines 126–168) — 2
  hypotheses, must discharge together.
- `RewritePreservesCST.v` Section `Rewrite_preserves` (lines 54–86) —
  1 hypothesis (`apply_total`); smallest v26.3 unit.
- `RewritePreservesSemantics.v` Section `Semantic_preservation`
  (lines 32–86) — 2 hypotheses, must discharge together.

## 2. Non-goals

- No Coq-level hypothesis discharge. The v26.3 sections above stay
  hypothesis-parametric in v26.2.1.
- No `edf_scheduler.ml` per-class rewrite; v26.1 priority offsets
  remain.
- No xelatex/lualatex `.aux` parser extensions.
- No migration of TYPO-002/003 to one-result-per-match. Aggregate
  `count` stays; the fix producer walks source independently to emit
  per-match edits.
- No rolling fix producers for rules beyond STRUCT-001 / TYPO-002 /
  TYPO-003. The three "exemplars" model the pattern; rest ship in
  v26.3+ per plan §10.

## 3. PR slate

### PR #1 — `result.fix` field via `mk_result` helper

**Branch:** `v26.2.1/a1-result-fix-field`
**Size:** 681-site mechanical rewrite + helper module. Single-review PR.
**Reviewer requirement:** 1 (mechanical), but author cannot self-merge
(standard).

**Changes:**

1. `latex-parse/src/validators_common.ml(i)`:
   - Add `fix : Cst_edit.t list option` field to `type result`.
   - Add helpers:
     ```ocaml
     val mk_result :
       id:string -> severity:severity -> message:string ->
       count:int -> result
     val mk_result_with_fix :
       id:string -> severity:severity -> message:string ->
       count:int -> fix:Cst_edit.t list -> result
     ```
   - `mk_result` sets `fix = None`; `mk_result_with_fix` sets
     `fix = Some <list>`.
2. Mechanical migration of all 681 record literals:
   ```
   Some { id = "X"; severity = S; message = M; count = C }
   → Some (mk_result ~id:"X" ~severity:S ~message:M ~count:C)
   ```
   Script: `scripts/tools/migrate_result_literals.py` (new, one-shot,
   deleted after PR #1 lands). Must be idempotent and refuse to touch
   a file that doesn't parse identically post-rewrite
   (round-trip gate).
3. `latex-parse/src/dune` — no change; `validators_common` already
   depends on `cst_edit` via the rewrite engine wrapped lib.

**Gates added/modified:**

- New gate: `scripts/tools/check_result_helpers.py` — rejects new
  `{ id = ...; severity = ...; message = ...; count = ... }` record
  literals in `validators_*.ml`. Forces future rules to use the
  helper. Wired into `pre_release_check.py` as gate #15.
- `run_differential_test.py` baseline reset to `v26.2.0`; fix-present
  diffs use `--expected-diff-keys fix` (per CHANGELOG line 70).

**Semver:** additive — new field defaults to `None` through the
helpers; no behavior change on consumers. Patch bump (`26.2.0 →
26.2.1`).

**Acceptance:**

- `dune build && dune runtest` green.
- 14+1 gates pass (new `check_result_helpers`).
- `run_differential_test.py --baseline-ref v26.2.0 --current-ref HEAD
  --expected-diff-keys ""` → zero diffs (no fix producers yet).

### PR #2 — STRUCT-001 fix producer

**Branch:** `v26.2.1/a2-struct-001-fix`
**Size:** ~20 lines. Single commit.

**Changes:**

1. `validators_l0.ml::require_documentclass` — when firing, emit:
   ```ocaml
   let fix = [Cst_edit.insert ~at:0 "\\documentclass{article}\n"] in
   mk_result_with_fix ~id:"STRUCT-001" ~severity:Warning
     ~message:"Missing \\documentclass" ~count:1 ~fix
   ```
2. Test: `test_validators_struct.ml` asserts
   `r.fix = Some [edit]` with `edit.start_offset = 0 && edit.end_offset = 0
   && edit.replacement = "\\documentclass{article}\n"`.
3. Doc: extend `docs/v26_2/FIX_STYLE_GUIDE.md` with the STRUCT-001
   example.

**Gates:** differential-test expected-diff-keys includes `fix` for
STRUCT-001-firing corpus files from here on.

### PR #3 — TYPO-002 + TYPO-003 fix producers

**Branch:** `v26.2.1/a3-typo-dashes-fix`
**Size:** ~80 lines (two rules + position scan).

**Design note:** the current rules aggregate `count` without tracking
offsets. The fix producer does a separate second pass over the source
to collect offsets and build N edits. Does NOT change the existing
count logic.

**Changes:**

1. New helper in `validators_l0_typo.ml`:
   ```ocaml
   let find_all_substrings s sub =
     (* returns sorted list of byte offsets where sub occurs in s *)
   ```
2. TYPO-002 fix: for each offset `o` where `--` appears, emit
   `Cst_edit.replace ~start_offset:o ~end_offset:(o+2) "–"`.
3. TYPO-003 fix: same but for `---` → `—`, offsets +3.
4. **Conflict note:** TYPO-002 and TYPO-003 conflict on `---`
   (TYPO-003 matches, TYPO-002's second+third char also match). The
   existing `conflicts_with` edge (PR #241 p1.3: TYPO-003 suppresses
   TYPO-002 on `---`) means only TYPO-003 fires in that case, so the
   fix set is non-overlapping by construction.
5. Tests in `test_typo_fix.ml` (new): firing + fix-content assertions
   on curated fixtures.
6. Doc: FIX_STYLE_GUIDE.md — add the two-pass "scan for offsets"
   pattern.

### PR #4 — `--apply-fixes` CLI + `L0_APPLY_FIXES` env gate

**Branch:** `v26.2.1/a4-apply-fixes-cli`
**Size:** ~100 lines in `validators_cli.ml` + wiring.

**Changes:**

1. `validators_cli.ml`:
   - Add `--apply-fixes` boolean flag (default false). Alternative gate:
     env var `L0_APPLY_FIXES=1|true|on`.
   - When gated on: after `Validators.run_all`, collect every
     `r.fix = Some edits` into a single list, call
     `Rewrite_engine.apply` via `Cst_edit.apply_all`. On overlap:
     emit `E.apply-fixes.overlap` error to stderr, exit non-zero,
     DO NOT modify output.
   - Output: modified source to stdout (existing non-fix mode writes
     per-rule reports to stdout; `--apply-fixes` replaces that output
     unambiguously — semantically distinct mode, no confusion).
2. Decision (pre-filled, override if needed): all-or-nothing
   application only. `--apply-fixes-for RULE-ID` stays deferred to
   v26.3 per `V26_2_PLAN.md` §3.2 B3.
3. Wire into `latex-parse/src/dune` (no change expected — CLI is
   already in the main target).
4. Tests in `test_apply_fixes_cli.ml`:
   - STRUCT-001 apply inserts `\documentclass` at top.
   - TYPO-002 apply converts `a -- b` to `a – b`.
   - Overlapping fixes from contrived corpus → exit code 2, stderr
     `E.apply-fixes.overlap`.

### PR #5 — E2E fix integration test + runtime gate

**Branch:** `v26.2.1/a5-fix-integration-e2e`
**Size:** ~150 lines.

**Changes:**

1. `test_rule_fix_integration.ml` (new):
   - Full pipeline per test: raw source → `Validators.run_all` →
     collect fixes → `Rewrite_engine.apply_and_reparse` → assert no
     firing of the same rule on the output.
   - Cases: STRUCT-001, TYPO-002, TYPO-003, combinations.
2. CI gate: `pre_release_check.py` adds `test_rule_fix_integration`
   to the required-tests list (gate #16).
3. `corpora/fixtures/v26_2_1/` (new): curated inputs for the E2E
   tests. 5 files, small.
4. Documentation:
   - CHANGELOG `[v26.2.1]` entry with the five PRs listed.
   - `docs/MIGRATION_v26.2_to_v26.2.1.md` (new, small): the helper
     constructor is the only consumer-visible change, but third-party
     code constructing `result` literals directly must migrate.
   - Update `docs/v26_2/FIX_STYLE_GUIDE.md` with the three exemplars.

## 4. CHANGELOG deviation from v26.2.0 deferred-list

The v26.2.0 CHANGELOG line described the deferred field as
`result.fix : Cst_edit.t option`. During verification we determined
the correct type is `Cst_edit.t list option` (see §1.2). The v26.2.1
CHANGELOG entry documents the deviation:

> Type deviation from v26.2.0 plan: `result.fix` is
> `Cst_edit.t list option`, not `Cst_edit.t option`. Single-edit was
> incorrect — TYPO-002/003 rules aggregate `count` per document and
> produce one edit per match, requiring a list. The v26.2.0 `option`
> claim was an authoring error; no third-party code depended on it
> (the field didn't exist in v26.2.0).

## 5. Gates and ratchets

**No ratchet bumps expected.** New tests are structural, not
`expect true`. MLI doc coverage: `validators_common.mli` gains two
helpers with docstrings, so coverage goes up, not down. Perf budget:
no hot-path change.

**New gates added across the cycle:**
- PR #1: `check_result_helpers.py` (forbids raw `result` record
  literals in `validators_*.ml`).
- PR #5: `test_rule_fix_integration` in required-tests list.

Final pre-release check count: **14 → 16 gates** by tag.

## 6. Risks + mitigations

| ID | Risk | Likelihood | Impact | Mitigation | Backout |
|---|---|---|---|---|---|
| R1 | Migration script (PR #1) misses a literal | Med | High | Check `check_result_helpers.py` + full `dune runtest` before merge; staged rollout file-by-file | Revert PR, single commit |
| R2 | TYPO-002 and TYPO-003 fix sets overlap in corner cases | Low | Med | Existing `conflicts_with` edge suppresses TYPO-002 when TYPO-003 fires; test on `a---b---c` corpus explicitly | `--apply-fixes` emits overlap error + non-zero exit |
| R3 | STRUCT-001 fix inserts at wrong offset when BOM present | Low | Low | Fix-producer respects byte-0 semantics; test includes UTF-8 BOM fixture | Rule keeps working without fix; fix is optional |
| R4 | `--apply-fixes` output mode confuses existing stdout consumers | Med | Low | Mode is gated on explicit flag/env; existing stdout format preserved in non-fix mode | Ship with `FIX_STYLE_GUIDE.md` warning |
| R5 | v26.2.0 downstream consumers construct `result` records directly | Low | Med | Migration doc + deprecation note on `result` type literal usage | Helper is additive; raw literals still compile (gate is lint-only) |
| R6 | 681-site refactor introduces syntax error in one file | Med | High | Per-file round-trip gate in migration script + per-file `dune build` check | Revert file |

## 7. Release flow

Per `V26_2_PLAN.md` §12 template:

```bash
# After PR #5 merges and the CHANGELOG entry is complete:
git checkout main && git pull
git checkout -b v26.2.1/release-bump
python3 scripts/release.sh 26.2.1  # runs 16 gates + bumps facts
git push -u origin v26.2.1/release-bump
gh pr create --title "chore: bump version to 26.2.1" \
  --body "See CHANGELOG §v26.2.1"
# On merge, tag:
git checkout main && git pull
git tag -a v26.2.1 -m "v26.2.1 fix-producer track"
git push origin v26.2.1
```

## 8. Out-of-v26.2.1 (confirmed)

These stay in v26.3 per §10 of V26_2_PLAN and §1.4 above:

- Three Section-level Coq discharges (`CSTRoundTrip.Structure_lossless`,
  `RewritePreservesCST.Rewrite_preserves`,
  `RewritePreservesSemantics.Semantic_preservation`).
- Rolling fix producers for the remaining ~657 rules.
- `--apply-fixes-for RULE-ID` granularity flag.
- `edf_scheduler.ml` per-class rewrite.
- CST structure-lossless runtime gate.
- xelatex / lualatex `.aux` parser variants.
- L3 AST migration (docs/L3_ROADMAP.md).

## 9. First concrete action

Open **PR #1 (result.fix field + mk_result helpers)**:

```bash
git checkout main && git pull
git checkout -b v26.2.1/a1-result-fix-field
# 1. Edit validators_common.ml(i) with field + helpers
# 2. Write scripts/tools/migrate_result_literals.py
# 3. Run it — verify `dune build` after every file
# 4. Write scripts/tools/check_result_helpers.py
# 5. Wire new gate into pre_release_check.py
python3 scripts/tools/pre_release_check.py --allow-dirty --skip-build
git commit -m "feat(v26.2.1): PR #1 — result.fix field + mk_result helper"
git push -u origin v26.2.1/a1-result-fix-field
gh pr create --title "feat(v26.2.1): PR #1 — result.fix field via mk_result helper" \
  --body "See specs/v26/V26_2_1_PLAN.md §3 PR #1"
```

Estimated time: 1–2 days for PR #1, 1 day each for PRs #2–#4, 2 days
for PR #5. Total: ~8 days of work over a 2-week calendar cycle.
