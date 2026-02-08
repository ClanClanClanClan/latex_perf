Weekly Status (Weeks 0–10)
==========================

Week 0 — Bootstrap
- Minimal repo layout (latex-parse/, core/, proofs/, scripts/, specs/) and dune build green
- REST façade scaffolded; basic endpoints and smoke harness

Week 1 — Baseline + Zero‑Admit
- `dune build` green for latex-parse/
- Proofs: 0 admits for core stubs
- Performance baseline measured and recorded

Week 2–3 — Runtime Reconciliation & Catcode
- Catcode classifier restored and aligned with Data.Types.Catcode
- Benches runnable; perf_smoke numbers refreshed
- Docs updated with baseline results

Week 4 — Proofs (Foundations)
- L0 small‑step and segmented control models ported; window lemmas established
- Coq imports normalized for stable CI loadpath

Week 5 — Performance α Gate
- perf_smoke and edit‑window benches wired; gate scripts present
- Nightly perf job activated (gating on p95 < 20 ms, median-of-100); badge published to gh-pages

Week 6 — Validators (Pilot)
- Pilot L0 rules enabled behind `L0_VALIDATORS=pilot`
- CLI and REST smokes for pilot rules
- Message alignment added for core pilot IDs

Week 7 — Unicode + L1 + CI Gates
- Unicode token‑aware heuristics made paragraph‑aware; positive/negative goldens
- Dune unicode path flipped to uutf; fallback removed
- L1 expander summary (post_commands + spans) exposed under `L0_DEBUG_L1`
- L1 rules added: EXP‑001 (incomplete expansion), MOD‑001/2/3/4 (modernization)
- Goldens and corpora added; smokes enforce exact IDs + messages
- Proof progress in `LexerIncremental.v`: outside‑edits + window corollaries
- CI: proof-ci (Coq) added; Unicode/L1/pilot smokes enforce messages; branch-protection workflow provided

Next (Week 8)
- Expand proofs for incremental determinism and locality with a faithful L0 relation
- Activate nightly perf gates; monitor regressions (full-doc p95, edit-window p95, first-token p95)
- Gradually broaden message checks to remaining rules as wording stabilizes

Week 8 — Proof β Gate (CI wiring)
- Proof CI enforces zero admits and zero axioms across `proofs/`
- Proof regression alert workflow opens GitHub issues on failures

Week 9 — Performance β Gate (CI wiring)
- Performance Gate CI added as required check (quick gates on PRs)
- Nightly perf gates run full suite and open issues on regression
- Badges and rolling history published on gh-pages

Week 10 — Proof β Gate (enforced)
- Branch protection can enforce required checks (proof/perf/smokes)
- Proof β Gate now effective via required Proof CI (Coq)

Week 10 — Code Health Audit & Fixes
- Fixed CI YAML indentation across 23 workflows (ocaml-compiler was sibling of with: instead of child)
- Fixed opam version constraint (>= 5.1.1 in latex-parse/dune-project package stanza)
- Fixed 15 corpora/l1/sample_*.tex files (encoding: double backslash to single)
- Fixed simple_expander_test expected output for fixpoint expansion
- Fixed l1_integration_test corpus access (deps + chdir for dune sandbox)
- Replaced 15 duplicated .ml files in core/l0_lexer/ with symlinks to latex-parse/src/
- Removed 5 orphaned .ml files from core/l1_expander/
- Removed hardcoded absolute path from latex-parse/src/dune
- Applied dune fmt across codebase
- All 13 tests pass; dune build, runtest, fmt all green

Week 11 — VPD Compiler Batch 1
- VPD compiler skeleton: vpd_types.ml, vpd_parse.ml, vpd_emit.ml, vpd_compile.ml (313 lines)
- 10 pattern families: count_char, count_substring, count_substring_strip_math, multi_substring, multi_substring_strip_math, char_range, regex, line_pred, custom
- Generated 9 new TYPO validators (034, 037, 042, 048, 051, 052, 053, 055, 061) via VPD batch
- Wired into validators.ml via rules_vpd_gen list
- 9 corpus files + 9 golden entries in pilot_v1_golden.yaml
- All smoke tests green

Week 11 — CI Infrastructure Hardening
- Fixed timerfd blocking hang: added TFD_NONBLOCK to hedge_timer_stubs.c
- Added proper service warmup to rest-smoke, rest-schema, rust-proxy-smoke workflows
- Added opam install retry (3 attempts with 15s backoff) to all 25 CI workflows
- Fixed expander-smoke jq selector (was broken since Sept 2025)
- All 35 CI checks green on main

Week 12 — VPD Grammar Front-End + Code Debt
- VPD Grammar tool: generator/vpd_grammar.ml — YAML-to-VPD-JSON bridge
  - Reads rules_v3.yaml (623 rules) + vpd_patterns.json (pattern annotations)
  - Minimal YAML-subset parser (no new opam dependency)
  - Produces VPD manifest JSON for vpd_compile
  - Supports --filter (subset generation) and --validate (consistency check)
- New VPD pattern family: Count_char_strip_math (strip math then count char)
- E2E pipeline verified: rules_v3.yaml → vpd_grammar → vpd_compile → OCaml (TYPO-001 match)
- vpd_patterns.json: initial 6 entries (TYPO-001, 004, 005, 006, 023, 030)
- E2E test script: scripts/test_vpd_e2e.sh
- Code debt cleanup:
  - Deleted core/l0_lexer/dune.disabled (dead file with hardcoded absolute path)
  - Converted test_simd_attestation from executable to test stanza with exit code assertions
  - Added fault-test Makefile target for test_fault_injection
- CI: 25 workflows with opam retry, all green
- Tests: 13 dune tests pass (including new test_simd_attestation)

Week 13 — VPD Batch 2 + Q1 Wrap-Up
- VPD Batch 2: 8 new validators via VPD pipeline (TYPO-035, 036, 038, 041, 043, 054, 057, 063)
  - 4 regex-family rules (shouting detection, email detection, en-dash spacing, degree symbol)
  - 3 multi_substring rules (French punctuation, ldots spacing, smart quotes)
  - 1 count_substring rule (non-breaking hyphen)
- VPD-generated section now contains 17 rules (up from 9 in batch 1)
- vpd_patterns.json expanded to 23 entries (covering all VPD-generated + hand-coded VPD-able rules)
- typo_batch2.json: standalone batch 2 manifest for provenance tracking
- E2E test updated: verifies all 23 rules in full manifest + batch 2 regex rules
- All pilot golden tests pass (39/39), zero regressions
- Q1 exit criteria met:
  - dune build, dune runtest --force, dune fmt: all exit 0
  - TYPO-001 E2E pipeline verified via VPD grammar
  - Code debt resolved (no dead files, no hardcoded paths, no TODOs)

Week 14 — Phase 2 Kickoff: L1 Expansion Proofs + Coq Build Infrastructure
- Created proofs/dune with (coq.theory) stanza: all 13 proof files now compile via dune
  - Previously proofs/ had no dune file — CI was textually checking but not compiling
  - Theory name: LaTeXPerfectionist (matches existing Require Import statements)
- New proof file: proofs/Expand.v — L1 expansion model with fuel-bounded recursion
  - Defines: token model, macro catalog, expand_one (single step), expand_star (fixpoint)
  - Defines: well-formedness (wf_catalog), acyclicity (acyclic_catalog)
  - Proven (QED): expand_no_teof — expansion preserves EOF-free invariant
  - Proven (QED): expand_deterministic — same input → same output
  - Proven (QED): expand_one_unchanged — unchanged flag means identity
  - Proven (QED): expand_star_fixpoint — at fixpoint, extra fuel is no-op
  - Helper lemmas (QED): has_eof_cons, has_eof_app, catalog_lookup_wf, expand_one_no_eof
  - Deferred: expand_one_decreases_ctrls, expand_terminates_acyclic, expand_fuel_insensitive
  - Zero admits, zero axioms (CI gate compliant)
- All 13 proof files compile clean with Coq 8.18.0 via dune build proofs
- Proofs: 13 files (up from 12), 0 admits, 0 axioms

Week 15 — Expansion Termination + Fuel Confluence Proofs
- Completed all 3 deferred expansion theorems (all QED, zero admits):
  - expand_one_decreases_ctrls: acyclic single-step strictly decreases control count
  - expand_terminates_acyclic: acyclic well-formed catalog → expansion reaches fixpoint
  - expand_fuel_insensitive: sufficient fuel → result independent of fuel amount (confluence)
- New helper lemmas (all QED):
  - filter_app, count_ctrls_app, count_ctrls_nil, count_ctrls_zero_filter, count_ctrls_cons
  - is_catalog_ctrl_lookup, is_catalog_ctrl_non_ctrl, is_catalog_ctrl_none
  - catalog_lookup_in, acyclic_lookup_zero
  - expand_one_ctrls_unchanged: unchanged step preserves control count
  - expand_star_reaches_fixpoint: fuel ≥ count → fixpoint reached
  - expand_star_succ_at_fixpoint, expand_star_fuel_excess
- Expand.v: 11 theorems/lemmas QED total (up from 8 in W14)
- W14-17 exit criteria fully met ahead of schedule
- CI fix: removed legacy coq_makefile step from ci.yml (conflicted with proofs/dune)
- CI fix: restricted latex-perfectionist.yml trigger paths (package not on PyPI yet)
- Golden corpus: 8 new corpus files for VPD batch 2 validators (47 golden cases total)

Current State (Post Week 15 / Phase 2 Active)
- Validators: 75 rules (33 TYPO hand + 17 VPD-gen + 14 MOD + 2 CMD + 1 EXP + 4 basic + 4 legacy)
- VPD Pipeline: rules_v3.yaml → vpd_grammar → vpd_compile → OCaml (23 rules in vpd_patterns.json)
- Proofs: 13 files, 0 admits, 0 axioms — all expansion theorems QED
- Performance: p95 ≈ 2.96 ms full-doc (target < 25 ms), edit-window p95 ≈ 0.017 ms
- CI: 31 workflows covering build, format, tests, proofs, perf, REST, validators, Rust proxy
- Gates passed: Bootstrap (W1), Perf α (W5), Proof β (W10)
- Next gate: L0-L1 QED (W26) — expansion proofs complete; remaining is L1 integration + audit
