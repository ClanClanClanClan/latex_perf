# v26.2.1 E2E fix-integration fixtures

Small curated inputs for `latex-parse/src/test_rule_fix_integration.ml`
(v26.2.1 PR #5). Each file is the source the E2E test feeds to
`Validators.run_all` → collect-fixes → `Cst_edit.apply_all` → re-validate.

| File | Trigger | Expected fix |
|---|---|---|
| `struct_001_missing_docclass.tex` | STRUCT-001 (no `\documentclass`) | 1 insert edit at offset 0 |
| `struct_001_with_bom.tex` | STRUCT-001 + UTF-8 BOM at byte 0 (plan §6 R3) | 1 insert edit at offset 0; the BOM stays at its byte position and ends up after the inserted `\documentclass{article}\n`. Fix-producer respects byte-0 semantics; BOM-aware insertion is v26.3 scope. |
| `typo_002_multi_dashes.tex` | TYPO-002 (`--`) ×2 | 2 replace edits → en-dashes |
| `typo_003_multi_dashes.tex` | TYPO-003 (`---`) ×2 | 2 replace edits → em-dashes |
| `typo_002_collect_all.tex` | TYPO-002 ×2 (disjoint locations) | 2 edits, collected via `run_all` |
| `clean_docclass.tex` | (none — negative control) | 0 edits; applying yields source unchanged |

Expected env:

- STRUCT-001 fixtures: `L0_VALIDATORS` unset (rule lives in `rules_basic`).
- TYPO fixtures: `L0_VALIDATORS=pilot` (rules live in `rules_pilot`).

Add new fixtures to this directory + update the test + update this table
when extending v26.2.1 fix producers.
