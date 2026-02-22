# Changelog

All notable changes to LaTeX Perfectionist v25 are documented here.

## [Unreleased]

### Added (Phases 4-8, PRs #150-#159)
- Sub-split L0 and L1 validator modules (PR #150)
- Table-driven layer lookup (PR #151)
- CI workflow consolidation with setup-ocaml-env (PR #152)
- Test file consolidation by domain (PR #156)
- REST API decomposition into 3 modules (PR #157)
- Multi-arg macro support + 17 argsafe macros (PR #158)
- CI hardening: timeouts on all 30 workflows, Rust fmt+clippy (PR #159)

### Changed
- Macro catalogue expanded: 441 symbols + 79 argsafe = 520 total (was 383 + 28)
- CI consolidated from 35 to 30 workflows
- All CI jobs now have explicit timeout-minutes
- Rust proxy enforces cargo fmt --check + cargo clippy -D warnings
- Removed redundant opam constraint (dune >= 3.10 dedup)
- Deleted dead .github/actions/setup-ocaml/ composite action

### Fixed
- Dropbox-corrupted git refs (Phase 8: 21 conflict files in .git/)
- cargo fmt pre-existing formatting issue in rust proxy
- Stale remote branches cleaned (6 deleted)
- Stale local branches cleaned (16 deleted)
- Documentation audit: corrected inflated rule counts (482 → 452 spec-matched)


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
