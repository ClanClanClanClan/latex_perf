# Changelog

All notable changes to LaTeX Perfectionist v25 are documented here.

## [Unreleased]

### Added
- 80 VPD validators with formal Coq soundness proofs (PR #146)
- RegexFamily proof tactics: `qed_text_sound` tactic, `vpd_catalogue_coverage` lemma
- Conflict test suite: 22 cases for deterministic ordering, severity, and cross-family fire
- Shared `test_helpers.ml` module eliminating ~759 lines of boilerplate across 30 test files
- `contains_substring` helper replacing 30 ad-hoc `Str.search_forward` patterns
- Deferred NLP stubs documentation block for TYPO-019/-020/-030/-031
- Naming convention and `Validators_context` contract documentation

### Changed
- Hoisted 17 `Str.regexp` compilations from inside `let run` closures to rule-level (compiled once at module load)
- Replaced `List.exists` with `Hashtbl.mem` for `is_math_env` lookups (O(n) to O(1))
- Narrowed all 44 bare `with _ ->` exception handlers to specific exception types across 21 files
- Removed `-w -27-26` warning suppressions from `core/l1_expander/dune`; fixed underlying unused variable warnings
- Fixed 3 unsafe `List.hd` calls with pattern matching

### Fixed
- TYPO-050 count mismatch (81 vs 80) between Coq proof list and VPD patterns JSON

## [W25] - L3 Text-Scannable Approximations (PR #141)

### Added
- 22 new validators: BIB (12), PKG (2), FONT (1), LAY (3), REF (1), META (1), PDF (1), TIKZ (1)
- Helpers: `split_bib_entries`, `count_matches`
- 94 unit tests, 22 corpus files, 22 golden entries

## [W24] - expl3, TIKZ, LANG Rules (PR #140)

### Added
- 25 new validators: L3-expl3 (9), TIKZ (6), LANG (4), COL/LAY/META/RTL (6)
- 111 unit tests, 25 golden corpus files

## [W23] - L2 Batch 4: Final Text-Scannable (PR #139)

### Added
- 27 new validators: PKG (9), TAB (7), FIG (7), MATH (2), CMD (1), DOC (1)
- Helpers: `extract_usepackages_with_opts`, `extract_caption_content`
- 77 unit tests, 27 corpus files

## [W22] - Audit Remediation (PR #138)

### Fixed
- MATH-063 `String.split_on_char` bug
- CMD-005, PKG-007/023, TIKZ-007, FIG-010, DOC-001/002/003 logic fixes
- 43 regression tests

## [W21] - L2 Batch 3 (PR #137)

### Added
- 22 new validators: CMD, DOC, TAB, PKG, LANG, TIKZ, FIG rules
- 91 unit tests, 22 golden entries

## [W20] - L2 Batch 2 (PR #136)

### Added
- 11 new validators: FONT, MATH, REF cross-reference rules
- Helpers: `extract_labels_with_prefix`, `extract_refs_with_prefix`
- 85 unit tests

## [W19] - L2 Batch 1 (PR #135)

### Added
- 14 new validators: FIG, TAB, PKG, CJK structural scanning rules
- Helpers: `extract_env_blocks_with_opts`, `extract_preamble`, `extract_usepackages`
- 53 unit tests

## [W18] - Locale + Straggler Batch (PRs #133-134)

### Added
- 16 locale rules covering FR/PT/RU/PL/CS/EL/RO/AR/HE/ZH/JA/KO/HI
- 17 straggler rules (CY, DE, NL, PL, PT, RU, TR, ZH, VERB, MATH, L3, REF, TYPO)
- L0/L1 coverage: 100% of actionable rules (333/345; 12 Reserved)

## [W17] - L1 Batch Completion (PRs #120-132)

### Added
- DELIM (11), SCRIPT (22), MATH-A (14), MATH-B (23), MATH-C (34) L1 batches
- REF batch (8 rules), CHEM batch (9 rules), L3 batch (9 rules)
- ~1,300+ validator tests total
