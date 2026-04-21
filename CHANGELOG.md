# Changelog

All notable changes to LaTeX Perfectionist are documented here.

## [v26.1.0] — 2026-04-21

### Post-merge audit rounds (PRs #241, #242, and #243)

Six audit passes after the initial P1 merge unearthed progressively deeper issues that earlier rounds missed. Each was closed with substantive changes and a CI gate to prevent regression.

- **Conflict resolution wiring** (PR #241 p1.3). `conflicts_with` is now consumed by `run_all`: severity DESC, count ASC, id_lex ASC picks the winner; TYPO-003 suppresses TYPO-002 on `---`. Five concrete conflict edges populated.
- **BuildLog LAY-025/026/027 tautologies** (PR #241 p1.4). Replaced `P -> P` with `build_ctx`-parameterised firing predicates and persistence theorems using `has_event_preserved`. 12 QED, zero `Proof. auto. Qed.`.
- **Five uncatalogued utility rules** (PR #241 p1.4). `no_tabs` / `unmatched_braces` / `require_documentclass` / `missing_section_title` / `DOC-STRUCT` renamed to `STRUCT-001..005`, added to `rules_v3.yaml` + contracts. `default_meta` has zero live callsites.
- **Family-level DAG edges** (PR #241 p1.4). LAB/REF/BIB/CITE/CMD/ENV/MATH/FIG/TAB/VERB/STYLE/STRUCT families get default consumes/provides. Empty-consumes 93% → 56%.
- **Three more load-bearing proof tautologies** (PR #242 p1.5). `PartialParseLocality.v` / `RepairMonotonicity.v::repair_restores_trust_outside_boundaries` / `ValidatorGraphProofs.v::cycle_detection_sound` + `dependency_respects_topo_order` — all rewritten with substantive bodies (`lia`, `andb_false_iff`, two-step transitivity).
- **Anti-tautology CI gate** (PR #242 p1.5). `proof.yml` rejects `Proof. auto. Qed.` / `Proof. trivial. Qed.` in the ten memo-load-bearing proof files. Escape hatch via `(* ANTI-TAUT-OK: reason *)`.
- **Memo §11.2 per-class scheduling** (PR #243 p1.6). `evidence_scoring.ml` caps Class D confidence at Low and Class C at Medium without a live build profile. `edf_scheduler.ml` gains a `execution_class` field with priority offsets (A=0, B=1e6, C=2e6, D=3e6) so hot-path rules dominate scheduling regardless of layer/chunk proximity. Tests in `test_edf_scheduler.ml` verify class dominance.
- **Runtime-type bindings for E2 + DAG proofs** (PR #243 p1.6). `RepairMonotonicity.v` adds `partial_cst_trust_zone` Coq record mirror of `Partial_cst.trust_zone` with `forget_confidence` projection; `partial_cst_zone_trusted_under_bounded_repair` transports the E2 theorem to runtime-shaped records. `ValidatorGraphProofs.v` adds `validator_meta_v26` with string IDs (via list nat) + `find_by_id_unique`.
- **Three regression gates** (PR #243 p1.6). `check_regression_gates.py` enforces (1) `_CoqProject` lists every non-archive `.v`, (2) every rule_id matches `FAMILY-NNN`, (3) mutation-uncovered count ≤ 35 (P1.4 baseline). Wired into `spec-drift.yml`.

## [v26.1.0-draft] — 2026-04-20

Memo-mandated v26 substrate delivery (`specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md`). Closes memo §4, §6, §10, §11, §12, §15 items that slipped past v26.0.0. After two internal audit rounds the scope was split into three honest buckets below.

### Shipped and runtime-enforced

These changes are real behaviour changes in the runtime or proof tree; tests pin the behaviour.

- **Language contract + tier gating** (memo §4). `specs/v26/language_contract.{md,yaml}` defines LP-Core / LP-Extended / LP-Foreign tiers. `latex-parse/src/language_profile.{ml,mli}` + `unsupported_feature.{ml,mli}` implement the classifier. CLI `--profile` flag; REST `L0_PROFILE_OVERRIDE` env var. **PR #241 (p1.2)** wires tier gating into `Validators.run_all`: when the active profile is `LP_Foreign`, rules whose contract declares `project_scope: lp_core_or_extended` are skipped; only `Any_tier` rules (the Class C build-coupled set) fire. Proven with `test_tier_gating.ml` (4 cases). `proofs/LanguageContract.v` — 6 QED.

- **Rule contracts drive the validator metadata** (memo §10, §15.4). `specs/rules/rule_contracts.yaml` + `.json` (654 entries × 11 fields) + `latex-parse/src/rule_contract_loader.{ml,mli}` replace `Validator_dag.default_meta` in `validators.ml` for every catalogued rule. Missing contracts are a fatal startup error (`Rule_contracts_missing` exception). Internal-utility rules (`no_tabs`, `unmatched_braces`, `DOC-STRUCT`) still use `default_meta`; `Validator_dag.default_meta` is `[@@deprecated]`. `scripts/tools/generate_rule_contracts.py` + `check_rule_contracts.py` drift gate enforces contract ↔ runtime parity. `proofs/ValidatorGraphProofs.v` +4 QED (7 total).

- **Execution-class runtime classification** (memo §11). `execution_class.classify` now reads the real A/B/C/D from `rule_contracts.yaml` instead of returning A-or-C. Class D (STYLE family) is routed out of `run_all` and reached through `run_with_policy Execution_policy.with_advisory` or the CLI `--advisory` flag. CI drift gate verifies every runtime Class C id in `execution_class.ml` has `execution_class: C` in the contract — this turns the abstract `ExecutionClasses.v` theorems into a runtime-enforced invariant. `proofs/ExecutionClasses.v` — 6 QED.

- **Editing-semantics proofs** (memo §6). `proofs/RepairMonotonicity.v` E2 strengthened with `repair_restores_trust_outside_boundaries` — the dependency-boundary hypothesis is genuinely consumed, not decorative (5 QED). `proofs/StableNodeIds.v` E3 binds to real AST via `parser_located_node` mirror + `Node_id.of_located` OCaml constructor, now called from `Partial_cst.zone_id` so every trust zone carries a stable ID across edits (8 QED). `latex-parse/src/error_recovery.is_repaired_with_deps` + `dependency_boundary` type.

- **Expanded compile-log pack** (memo §16.2). PR #235 added LAY-025/026/027 (rerun, citation undefined, font substitution) as Class C rules; `proofs/BuildLog.v` proves their conditional soundness (6 QED after the 3 new ones).

- **Spec catch-up**. `specs/rules/rules_v3.yaml`: added LAY-025/026/027 (PR #237) plus CMD-015/016/017 (user macro), PRJ-001..004 (project graph), PRT-001/002 (partial document trust) that existed in the runtime since v26.0 but never made it into the spec (PR #241 p1.1-#4). Totals: **654 specified / 638 shipped**. `scripts/validate_catalogue.py` L0-only early return removed.

- **UserMacro proof wrappers with real content** (memo §16.1). `proofs/UserMacroTermination.v` — `empty_catalog_acyclic`, `singleton_acyclic`, `add_entry_acyclic`, `count_refs_monotone` (4 non-trivial QEDs); `proofs/UserMacroRegistrySound.v` — `user_macro_registry_merge_sound` via `merge_acyclic`, disjoint-names specialisation, acyclicity-under-reverse-merge (3 QEDs). The tautological `input = input` placeholders from the first P1.1 draft were replaced after the second audit.

- **Machine-readable support matrix at memo path** (memo §12). `docs/SUPPORT_MATRIX.md` + `docs/SUPPORT_MATRIX.yaml` (moved to the memo §12.1 path, from `specs/v26/support_matrix.yaml`). YAML is source-of-truth; spec-drift workflow validates schema.

- **Governance regeneration**. `governance/project_facts.yaml` — version v26.1.0, 654/638 counts, `by_proof_class` includes `formal_conditional: 3`, `by_execution_class` populated (A=172, B=416, C=17, D=49). `generated/project_facts.json` mirror emitted by generator (memo §16.1 asked for JSON). `governance/project_facts.contract.yaml` updated.

### Shipped as metadata; enforcement partial or deferred

These are real artefacts but the runtime does not yet fully consume them; callers still need to reach them explicitly.

- **Per-class scheduling** (memo §11.2). `rule_contracts.yaml` tags every rule with A/B/C/D, and `execution_class.classify` returns the real class. But `evidence_scoring.ml` and `edf_scheduler.ml` do NOT yet weight results or priority by class — Class D confidence is not capped, Class C does not get a dedicated EDF budget. The taxonomy is enforced at registration/classification time; per-class scheduling is v26.2 work and pairs with the compile-guarantee stack.

- **Rule DAG edges** (memo §10.3). 44 of 654 contracts have non-empty `consumes` (Class C: compile-log; L3 file rules: image/pdf/font metadata; ML-gated: ml_confidence_map). `depends_on` and `conflicts_with` are empty for every rule today. `Validator_dag.build_dag` produces a correct but largely edgeless DAG — this is the honest state for pattern-match leaf rules. VPD-overlap-derived conflict edges are a v26.2 follow-up.

- **Node_id constructor**. `Node_id.of_located` is wired from `Partial_cst.zone_id` and the type is consumed by a new public `val zone_id` — giving the E3 theorem a concrete binding. Validators and incremental callers do NOT yet track zones by node_id across edits; that consumer arrives with the v26.2 lossless-CST substrate.

- **ExecutionClasses.v abstract model**. The theorem compartments (`Hot_path_state`, `Build_log_state`, `External_binary_state`, `Ml_confidence_state`) are a Coq-level abstraction. The runtime binding comes from the CI drift gate (step 3b in `check_rule_contracts.py`) verifying every runtime Class C rule has `execution_class: C` in the contract. A deeper binding — mapping Coq compartments to the real `Log_parser` / `File_context` / `Evidence_scoring` modules — is v26.2 work.

### Deferred to v26.2 / v27 (memo §16.3 release plan, not v26.1 regressions)

- Lossless CST stack (memo §7): `cst.ml`, `cst_builder.ml`, `rewrite_engine.ml`, `stable_spans.ml`, `CSTRoundTrip.v`, `RewritePreservesCST.v`. v26.2.
- Compile-guarantee theorem stack T0–T7 (memo §5) and `specs/v26/compilation_profiles.yaml`. v26.2 / v27.2.
- Three-plane hybrid invalidation with full semantic dep edges (memo §9). Current `dependency_graph.ml` / `invalidation.ml` / `semantic_edges.ml` ship as the v26 foundation; three-plane routing is v26.2.
- Full project/build model: `aux_state.ml`, `bibliography_state.ml`, `artifact_graph.ml`, `ProjectSemantics.v`, `ArtifactGraphSound.v` (memo §8). v26.2.
- Editorial policy layer (memo §13). v27.0.
- Collaboration platform (memo §14). v27.1.

### Documentation refresh

- `README.md`, `docs/index.md`, `docs/PROOF_CLASSES.md`, `docs/SUPPORT_MATRIX.md`, `docs/ARCH.md`, `docs/PROOFS.md`, `docs/PROOF_GUIDE.md`, `ARCHITECTURE.md`, `ml/ARCHITECTURE.md`, `ml/RESULTS.md`, `specs/README.md`, `specs/rules/README.md`, `docs/README.md`: v26.1.0 framing; refreshed counts (654 / 638 / 631 / 20 / 3 / 1,137); ML v2 no longer marked "blocked" (trained on A100, F1=0.9799, proved).
- `docs/L3_ROADMAP.md`: new. Honest acknowledgement of regex-derived L3 (memo §15.5) with migration plan to AST-derived extraction.
- `docs/ARCH.md` L3 section now leads with the regex-caveat.
- `docs/archive/`: moved obsolete v25-era docs (`PROJECT_STORY_GENERAL.md`, `RULES_IMPLEMENTATION_PLAN.md`, `WEEKLY_STATUS.md`).

### Fixed (memo §15)

- §15.2 governance drift: `governance/project_facts.yaml` regenerated and drift-gated end-to-end.
- §15.3 release-state coherence: CHANGELOG entry structure split across shipped / metadata / deferred.
- §15.4 DAG metadata hollowness: `default_meta` fallback removed for catalogued rules.
- §15.5 L3 over-source honesty: `docs/L3_ROADMAP.md` + `docs/ARCH.md` caveat.
- §15.1 EDF deadline bug: verified already fixed in v26.0 (field is `priority`, comment explicit).

### Verification

- `dune build` green (full tree including proofs)
- `dune runtest --force latex-parse/src` → 94+ suites PASS, 0 failures
- `proof-ci` zero admits, zero axioms across 144 Coq files
- `scripts/tools/check_repo_facts.py` → Project facts check passed
- `scripts/tools/check_rule_contracts.py` → PASS with Class C runtime-vs-contract binding check
- `scripts/validate_catalogue.py` → PASS (all layers)

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
