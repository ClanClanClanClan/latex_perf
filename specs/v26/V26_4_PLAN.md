# V26.4 — Conflict-aware rewrites + apply_edits semantics + rolling fix batch

**Status:** draft, 2026-04-26. Successor to `V26_3_1_PLAN.md` §5
commitment + `V26_2_PLAN.md` §13 ("Rewrite conflict-aware merge")
explicit deferral.
**Scope:** the next concrete chunk of v26 substrate work past v26.3.1.
**Cadence:** bundled cycle PR (matches v26.3.0 PR #271 + v26.3.1
PR #279 patterns), followed by a small release-bump PR.

## 0. Pre-conditions (verified 2026-04-26 on `main` `39eebde`)

- `v26.3.1` tagged on the PR #280 merge commit; Release workflow
  green; tag pushed; GitHub Release auto-published.
- 17/17 pre-release gates PASS.
- 1,281 theorems / 161 .v files / 0 admits / 0 axioms.
- Differential test 0 diffs across 330 corpus files vs `v26.3.0`.
- 9 required-checks on `main` (incl. `spec-drift`); messages-validate
  is strict.
- ADMISSIBILITY_MAP: only T6 + T7 remain `HYPOTHESIS-PARAMETRIC`
  (owned by v27 WS8 via `proofs/PdflatexModel.v`); CSTRoundTrip,
  RewritePreservesCST, and RewritePreservesSemantics Sections all
  unconditionally discharged.

## 1. Inventory of in-scope items

### 1.1 Conflict-aware rewrite merging (PRIMARY ITEM)

`V26_2_PLAN.md` line 631 + line 565 mandated automatic conflict-
aware rewrite merging. v26.3 shipped strict overlap rejection
(`Cst_edit.apply_all → Error (Overlap (a, b))`). v26.4 adds:

- **`Cst_edit.apply_best_effort : string -> t list -> result`**.
  Returns `(output, applied, skipped)`. Walks the input edit list
  in input order; an edit is appended to `applied` iff it doesn't
  conflict with any edit already in `applied`, otherwise it lands
  in `skipped`. The output equals `apply_all src applied` (which
  cannot fail by construction). Pure insertions at the same offset
  remain compatible per the existing `conflicts` semantics.
- **`Cst_edit.apply_with_priority : string -> (t -> int) -> t list ->
  result`**. Sorts by descending priority (higher = applied first),
  then dispatches to `apply_best_effort`. Useful when the caller
  has a deterministic priority signal (e.g., severity-driven).
- **CLI plumbing** in `validators_cli.ml`: `--apply-fixes-best-effort`
  flag selects `apply_best_effort` over the strict `apply_all`.
  Default (no flag) preserves the existing strict behaviour
  (back-compat).
- **Tests** (`test_cst_edit.ml` extension): no-conflict input ≡
  apply_all; two conflicting edits → first wins; deduplicated
  insertions preserved; apply_with_priority orders correctly;
  output equals apply_all on the applied subset.

This is the v26.4 cycle's primary deliverable. Estimated ~150 LoC
OCaml + 50 LoC test, single session.

### 1.2 Stronger `apply_edits` semantics (Coq, optional stretch)

`proofs/RewritePreservesCST.v`'s `apply_edits_concrete` was shipped
in v26.3 (item D). Beyond byte-losslessness, two additional theorems
strengthen the runtime guarantee:

- **`apply_one_edit_byte_count`**: `length (apply_one_edit src e) =
  length src + delta e` where `delta e := length e.replacement -
  (e.e_end - e.e_start)`. Mechanical (induction on `take`/`drop`).
- **`apply_edits_concrete_associative_subset`**: the result of
  `apply_edits_concrete` over a NON-OVERLAPPING list is invariant
  under any reordering of the input (folded application commutes
  in the absence of conflicts). This requires a `non_overlapping`
  predicate on the edit list (similar to OCaml's `validate_non_
  overlapping`); restricted to that subset, fold-order doesn't matter.

Optional within v26.4 if §1.1 lands cleanly. If §1.2 turns out
non-trivial, defer to v26.4.1 / v26.5.

### 1.3 Rolling fix-producer batch (PRIMARY ITEM)

Continuation of `V26_3_1_PLAN.md` §1.1's rolling work. Original
budget: 10 rules. **Actual ship: 5 rules** (TYPO-014, TYPO-021,
TYPO-025, SPC-009, SPC-010). Honest revision — the remaining 5
candidates the batch was draft-scoped for either need careful
boundary-tracking (TYPO-016 must avoid escaped `\cite`-like
patterns inside verbatim, SPC-008 needs paragraph-boundary
detection, SPC-011 needs `$$…$$` boundary tracking) or duplicate
existing fixes (STRUCT-003 is covered by TYPO-006's tab → spaces
fix). These five roll into v26.5 if mechanical extensions emerge,
or stay as count-only flags otherwise.

Total fix-producing rules after v26.4: **28** (was 23 at v26.3.1).
~632 rules remain, ongoing rolling work into v26.5+.

## 2. Non-goals

- **L3 AST migration** (`docs/L3_ROADMAP.md`) — multi-month, defer
  to v26.5 / v27.
- **T6/T7 discharge against `PdflatexModel.v`** — v27 WS8.
- **More than 10 fix producers** in §1.3 — batch-size discipline.
- **Removing strict `apply_all`** — back-compat: callers that want
  the old strict semantics keep them.
- **Full edit-list reorderable proof** — only the bounded subset
  in §1.2 if it lands.

## 3. PR slate (post-execution revision)

The cycle ended up as three PRs rather than the originally-planned
two. The §1.2 stretch landed as a separate PR after the §1.1+§1.3
cycle PR was merged — cleaner-than-mid-PR amendment, and §1.2 was
explicitly "OPTIONAL stretch" in the §1.2 description.

### PR #1 — cycle PR (`v26.4/cycle`, merged as #281)

Plan + conflict-aware merging + 5 fix producers + format-job CI fix.
Logical commits:

1. `V26_4_PLAN.md` — this plan file.
2. Conflict-aware merging (§1.1): `cst_edit.{ml,mli}` adds
   `apply_best_effort` + `apply_with_priority`; CLI plumbing for
   `--apply-fixes-best-effort{,-for}`; 7 new tests.
3. ocamlformat polish.
4. 5 fix producers (§1.3 partial): TYPO-014, TYPO-021, TYPO-025,
   SPC-009, SPC-010 + 7 tests.
5. CI hygiene: format job opam-packages list + timeout-minutes
   adjustments (re-trying around upstream package mirror flakes).

### PR #2 — Coq stretch (`v26.4/coq-stretch`, merged as #282)

§1.2: 10 new theorems in `proofs/RewritePreservesCST.v`
(byte-count + structural lemmas). Did NOT discharge the
associative-reorder claim — that requires modelling parallel
application against original-source offsets, multi-week scope,
deferred to v26.5+ with an honest note in the commit message.

### PR #3 — release-bump for v26.4.0

Mirrors v26.3.1 PR #280: small chore PR bumps version metadata,
regenerates governance, lands new CHANGELOG entry. Tag created
on `main` after merge.

## 4. Gates

No new pre-release gate is added in v26.4. The 17 existing gates
cover the new code paths via the §1.1 tests being wired into
`dune runtest` and the §1.3 fix producers being absorbed by
`test_typo_fix.ml` / `test_rule_fix_integration.ml`.

Total at v26.4.0 tag: **17 pre-release gates** (unchanged).

## 5. Out-of-cycle commitments

Items deferred from §2 each open their own scoped plan files:
- `V26_5_PLAN.md` if rolling fix-producer cadence continues.
- `V27_WS8_PLAN.md` when v27 WS8 begins (T6/T7 discharge against
  `proofs/PdflatexModel.v`).
- `docs/L3_ROADMAP.md` is the existing plan for L3 AST migration.

## 6. Differential-test budget

`run_differential_test.py` against `v26.3.1` is expected to show:

- **0 diffs** on the default invocation (no `--apply-fixes`).
- The `apply_best_effort` mode is opt-in via
  `--apply-fixes-best-effort`. The strict `--apply-fixes` mode
  preserves existing behaviour, so corpus-driven differential
  output is unchanged.
- The 5 new fix producers contribute additional fix edits in
  `result.fix` for inputs that trigger them, but the default
  emission stream is unchanged.

**Verified 2026-04-27 post-PR #282:** 0 diffs / 330 files vs `v26.3.1`.

## 7. First concrete action

This file is created on branch `v26.4/cycle`. The next commit on
that branch is `Cst_edit.apply_best_effort` (§1.1). Subsequent
commits land §1.3 (fix producers); §1.2 lands only if completed
in-session, otherwise reserved for a follow-up cycle.
