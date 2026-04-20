# Changelog

All notable changes to LaTeX Perfectionist are documented here.

## [v26.1.0] — 2026-04-20

Memo-mandated v26 substrate (`specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md`). Closes memo §4, §6, §10, §11, §12, §15 items that slipped past v26.0.0.

**Added (PRs #235-#240):**
- **Language contract** (memo §4): `specs/v26/language_contract.{md,yaml}` defines LP-Core / LP-Extended / LP-Foreign tiers; `latex-parse/src/language_profile.{ml,mli}` + `unsupported_feature.{ml,mli}` implement the classifier; CLI `--profile` flag; REST `L0_PROFILE_OVERRIDE` env var. `proofs/LanguageContract.v` (6 QED).
- **Real validator DAG** (memo §10, §15.4): `specs/rules/rule_contracts.yaml` + `.json` (645 entries × 11 fields) + `latex-parse/src/rule_contract_loader.{ml,mli}` replace `Validator_dag.default_meta` in `validators.ml`. `scripts/tools/generate_rule_contracts.py` + `check_rule_contracts.py` drift gate. `proofs/ValidatorGraphProofs.v` +4 QED.
- **Execution-class proofs** (memo §11): `proofs/ExecutionClasses.v` (6 QED) formalises Class A hot-path isolation, Class C build-profile requirement, Class D advisory-only, and hot-path-excludes-CD.
- **Machine-readable support matrix** (memo §12): `specs/v26/support_matrix.yaml` is the source of truth; `docs/SUPPORT_MATRIX.md` rewritten as human-readable wrapper; drift-gated.
- **Editing-semantics proofs** (memo §6): `proofs/RepairMonotonicity.v` (E2, 4 QED) + `proofs/StableNodeIds.v` (E3, 6 QED). `Error_recovery.is_repaired_with_deps` adds dependency-boundary-aware repair predicate.
- **Expanded compile-log pack** (PR #235): LAY-025/026/027 rules (rerun warning / citation undefined / font substitution); `proofs/BuildLog.v` conditional soundness (3 QED).
- **Spec catch-up**: LAY-025/026/027 added to `specs/rules/rules_v3.yaml` (642→645 entries); `scripts/validate_catalogue.py` L0-only early return removed so non-L0 runtime rules are now catalogue-checked.

**Governance regenerated:**
- `governance/project_facts.yaml`: version v26.1.0; 645 specified / 629 shipped; `by_proof_class` now includes `formal_conditional: 3`; `by_execution_class` populated (A=172, B=407, C=17, D=49); release_date 2026-04-20.
- `governance/project_facts.contract.yaml`: adds `formal_conditional_count` to required proof fields; consumers list now includes `specs/v26/support_matrix.yaml`.

**Documentation refresh:**
- `README.md`, `docs/index.md`, `docs/PROOF_CLASSES.md`, `docs/SUPPORT_MATRIX.md`, `docs/ARCH.md`, `docs/PROOFS.md`, `docs/PROOF_GUIDE.md`, `ARCHITECTURE.md`, `ml/ARCHITECTURE.md`, `ml/RESULTS.md`, `specs/README.md`, `specs/rules/README.md`, `docs/README.md`: v26.1.0 framing; refreshed counts (645 / 629 / 622 / 20 / 3 / 1,130); ML v2 no longer marked "blocked" (trained on A100, F1=0.9799, proved).
- `docs/archive/`: moved obsolete v25-era docs (`PROJECT_STORY_GENERAL.md`, `RULES_IMPLEMENTATION_PLAN.md`, `WEEKLY_STATUS.md`).

**Fixed:**
- Hollow validator DAG: every rule used to call `Validator_dag.default_meta r.id` with empty provides/requires/conflicts (memo §15.4 defect). Now populated from `rule_contracts.yaml`.
- Runtime-vs-spec divergence: LAY-025/026/027 existed in runtime since v26.1 compile-log work but not in `rules_v3.yaml`. Fixed in PR #237.
- `scripts/validate_catalogue.py` L0-only gap: non-L0 runtime rules now covered.

## [v26.0.0] — 2026-04-18

### Added (PRs #223-#233)

**WS0: Truth-surface freeze**
- Canonical `governance/project_facts.yaml` with `generate_project_facts.py` and `check_repo_facts.py`
- Spec-drift CI gate (`.github/workflows/spec-drift.yml`)
- `docs/SUPPORT_MATRIX.md`, `docs/PROOF_CLASSES.md`, `docs/COMPILATION_GUARANTEE_STACK.md`

**WS1: Compile-log integration**
- Class C execution path: 14 log-dependent rules isolated from keystroke-critical `run_all`
- `build_profile.ml`: auto-detect `.log` sibling, engine detection, staleness check
- `execution_class.ml` / `execution_policy.ml`: A/B/C/D taxonomy
- CLI `--log` flag, auto-detect, `[build]` tagged output
- `docs/BUILD_LOG_CONTRACT.md`

**WS2: Bounded user macro registry**
- `user_macro_registry.ml`: parse `\newcommand`/`\renewcommand`/`\providecommand`, 29-primitive blocklist
- Def-use dependency edges, DFS cycle detection
- `merge_user_macros` in `macro_catalogue.ml`: user macros expand via existing pipeline
- CMD-015 (unsupported construct), CMD-016 (cycle), CMD-017 (shadowing)

**WS3: Project graph foundation**
- `include_resolver.ml`: parse `\input`/`\include`/`\includeonly`, no-brace form support
- `project_graph.ml`: directed inclusion graph, DFS cycle detection, `\includeonly` respect
- `project_state.ml`: per-file semantic analysis, cross-file label/ref projection
- PRJ-001 (cycle), PRJ-002 (unresolved), PRJ-003 (cross-file undef ref), PRJ-004 (dup label)
- CLI `--project` mode

**WS4: Hybrid invalidation**
- `semantic_edges.ml`: label-ref and macro def-use edges per chunk
- `dependency_graph.ml`: BFS transitive affected set propagation
- `invalidation.ml`: replaces whole-source fallback with semantic-aware invalidation
- Wired into `run_all_incremental` and `run_all_scheduled`

**WS5: Partial document semantics**
- `partial_cst.ml`: classify documents into trust zones (Complete/Partial/Broken)
- `error_recovery.ml`: recovery point detection, monotonic repair predicate
- PRT-001 (parse errors with confidence-based severity), PRT-002 (trust zone boundary)
- Wired into `run_all` via `Parser_l2.parse_located`

**WS6: Testing hardening**
- `test_mutation_baseline.ml`: 92.4% rule coverage (532/576)
- `test_fuzz_parser.ml`: grammar-aware parser fuzzing (5000 trials)
- `test_fuzz_binary.ml`: PNG/JPEG/font reader fuzzing (1000 trials/format)
- `test_long_stress.ml`: 10K iterations + GC tracking
- `.github/workflows/mutation.yml`, `.github/workflows/fuzz-nightly.yml`

**Coq proofs (6 new files, 22 QED, 0 admits)**
- `BuildLog.v`, `UserExpand.v`, `IncludeGraphSound.v`
- `InvalidationSound.v`, `PartialParseLocality.v`, `DamageContainment.v`

### Fixed
- EDF scheduler: renamed `deadline` to `priority` (was compared against wall-clock time)
- Removed dead `DeadlineMissed` event from event_bus
- TIKZ-002 moved from `rules_l3_file` to `rules_class_c` (Class C isolation)
- `expand_once` arity-0 argsafe fix (user macros with no args never expanded)
- REST handler: `User_macro_context` set/cleared per request

### Changed
- `project_facts.yaml`: `multi_file: planned` → `multi_file: alpha`
- 18 new OCaml modules, 15 new test files, ~3,846 new lines

## [v25.0.0] — 2026-04-14

### Added (PRs #200-#219)
- 19 L3 file-based validators: PNG/JPEG/PDF/font binary readers (PRs #214-#215)
- 12 expl3/draft rules: CHAR-004, MATH-006, L3-001..011 (PR #215)
- 19 MOD/EXP rules added to spec with VPD entries (PR #215)
- SIMD 6x benchmark: simd_vs_scalar_bench.ml, 12.67x measured (PR #214)
- ML v2 ByteClassifier trained on A100: F1=0.9799 (PR #215)
- SpanExtractorSound.v: v2_span_extractor_sound theorem QED (PR #215)
- Chunk store: paragraph-level splitting, xxh64 hashing, per-chunk caching (PR #216)
- EDF scheduler: deadline-ordered task execution, event bus integration (PR #216)
- ML confidence integration: pre-computed map suppresses zero-TP rules (PR #216)
- run_all_incremental: only re-validates dirty chunks (PR #216)
- run_all_scheduled: EDF-ordered incremental validation (PR #216)
- Proof maturity: multi_substring_all, substring_pair, terminated_command,
  paragraph_terminated_command_pair Coq families (PRs #218-#219)
- Integration test suite: 36 paranoid end-to-end assertions (PR #219)
- docs/ARCH.md: architecture handbook (PR #217)
- docs/PROOF_GUIDE.md: proof-writers guide (PR #217)
- .pre-commit-config.yaml: zero-admits, zero-axioms, no-Str, format hooks (PR #217)
- Re_compat module: thread-safe Str replacement via Re library (PR #217)
- Colab notebook: v2_byte_classifier_training.ipynb, disconnection-safe (PR #215)
- data/ml_confidence_map.json: per-rule ML precision weights (PR #216)
- Dockerfile: multi-stage OCaml service image
- scripts/release.sh: release automation
- .github/workflows/release.yml: GitHub Release + Cosign signing
- .github/workflows/docker-push.yml: Docker image to GHCR

### Changed (PRs #200-#219)
- Str→Re migration: 1,057 call sites across 16 files, zero Str references (PR #217)
- Proof count: 606 faithful (was 587), 20 conservative (was 37)
- Theorem count: 1,067 (was ~600)
- Severity mismatches: 10 fixed in VPD patterns (PR #219)
- validators_cli.ml: now uses run_all_scored with ML confidence (PR #217)
- ML confidence map: opt-in via LP_ML_CONFIDENCE_MAP env var (PR #217)
- Performance gates: aligned to spec (25ms full-doc, 1ms edit-window) (PR #217)
- v25_master_R1.md §9: 6→7 language packs (Arabic added) (PR #217)
- L_roadmap.md: W102-140 marked Done

### Fixed (PRs #200-#219)
- gen_coq_proofs.py: L3/L4 grouping bug (was defaulting to L0) (PR #214)
- build_candidate_dataset.py: yaml.safe_load→json.load for control chars (PR #215)
- train_byte_classifier.py: BCELoss outside autocast for AMP safety (PR #215)
- chunk_store: catcode vector in hash per spec I-3 (PR #216)
- chunk_store: diff_snapshots handles deletion (PR #216)
- edf_scheduler: removed dead Lockfree_queue field (PR #216)
- 25 weak test assertions eliminated across 5 files (PR #219)
- All font reader tests: match/expect-true→direct equality (PR #219)

## [Unreleased — Phases 9-12]

### Added (Phases 9-12, PRs #161-#179)
- Comprehensive project audit: docs, .mli, _CoqProject fixes (PR #172)
- Regex hoisting: 44 Str.regexp compilations moved out of run closures (PRs #172, #173)
- contains_substring: replaced Str.regexp_string with pure OCaml (PR #174)
- ML CPU baselines: logistic regression + gradient boosting pipeline (PR #175)
- External corpus infrastructure: corpora.lock + fetch_corpora.sh (PR #176)
- Risk register: governance/risk-register.md with 33 risks (PR #177)
- Parallel validators: run_all_parallel with OCaml 5.x domains (PR #178)
- Documentation site: mkdocs.yml + landing page (PR #179)

### Removed
- run_all_parallel: unsafe with Str global state, removed pending Re migration (PR #180)

### Added (PRs #161-#171)
- ML v2 parser-state diagnostic + architecture docs (PR #161)
- v2 candidate classification pipeline: extractor, dataset, byte classifier (PR #165)
- 429 soundness theorems via auto-generation + CI parallelism (PR #166)
- Language detection: babel/polyglossia/CJK heuristic, 65-lang mapping (PR #167)
- 84 new validators: 49 STYLE, 10 locale (CE/TH/IB/LANG), 25 L3-approx (PR #168)
- Post-merge audit fixes: regex bugs, severity mismatches, 55 test cases (PR #169)
- 93 golden corpus tests + 7 i18n QA documents across 12 YAML suites (PR #170)
- 607 soundness theorems (was 429), 26 test hardening cases, perf verified (PR #171)

### Changed (Phases 9-12)
- Rule count: 452 → 568 unique IDs (91.2% of 623 spec)
- Proof count: 429 → 607 per-rule soundness theorems (26 faithful, 581 conservative)
- Golden corpus: 236 → 329 cases across 12 suites
- Test suites: 53 → 57, ~7,320 test cases total
- gen_coq_proofs.py extended to L3/L4 layers

### Infrastructure (Phases 9-12)
- Project health cleanup: gitignore, CI consolidation, action bumps (PR #162)
- Docs/proofs audit: README sync, macro sync, Coq proof refactor (PR #163)
- Folder cleanup: archive stale docs, remove orphans (PR #164)

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
