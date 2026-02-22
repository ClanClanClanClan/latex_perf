# LaTeX Perfectionist v25 - Project Index

**Status**: Week 30 of 156 — Post-Phase 8, entering Q3
**Last Updated**: 2026-02-22 (verified by full audit)
**Project Type**: 3-Year Solo-Developer Project (156 weeks total)

## Current Status Summary

- 452 spec-matched validators implemented out of 623 spec rules (72.6%)
  - L0: 183/187 (97.9%), L1: 141/158 (89.2%), L2: 94/96 (97.9%)
  - L3: 24/112 (21.4%), L4: 10/70 (14.3%)
  - 22 orphan rules in code not in spec (MOD, EXP, UTF/LATIN utilities)
  - 474 unique rule IDs in code total; 51 layer misplacements (functional, file vs spec layer)
  - Remaining gaps: L3 needs semantic/AST infrastructure, L4 needs NLP pipeline
- Macro catalogue: 520 macros (441 symbols + 79 argsafe) in production
- 15 Coq proof files (+ 7 archive), 316 theorems/lemmas, 0 admits, 0 axioms
- Performance: A+B p95 = 3.25 ms (target ≤ 20 ms), first-token p95 = 27 µs (target ≤ 350 µs)
- 30 CI workflows, all with timeout-minutes on every job
- ~7,086 test cases across 53 test files, 236 golden corpus tests, 100K IPC roundtrips
- 6 gates passed: Bootstrap (W1), Perf α (W5), Proof β (W10), Q1 (W13), L0-L1 QED (W26), VPD-80 (W39)
- Y1 target of 180 validators exceeded by 2.5× (ahead of schedule)
- Next per timeline: W27-30 generic proof tactics (RegexFamily) — W40-52 L2 parser + proofs

## 📁 Project Structure

### Active Runtime & Benchmarks
```
latex-parse/
├── src/                        # SIMD service runtime (current production target)
│   ├── main_service.ml        # Service entry point
│   ├── broker.ml / worker.ml  # Hedge + worker orchestration
│   ├── real_processor.ml      # SIMD tokenization bridge
│   └── service_payload.ml     # Typed 13-byte status payload decoder for façades
└── bench/                      # Latency harnesses (@perf gates)
    └── ab_microbench.ml
```

### VPD Generator Pipeline
```
generator/
├── vpd_grammar.ml          # YAML + patterns JSON → VPD manifest JSON bridge
├── vpd_compile.ml          # VPD manifest JSON → OCaml validator code
├── vpd_types.ml            # Core VPD type definitions (11 pattern families)
├── vpd_parse.ml            # JSON manifest parser
├── vpd_emit.ml             # OCaml code emitter
├── typo_batch1.json        # Batch 1 manifest (9 rules)
└── typo_batch2.json        # Batch 2 manifest (8 rules)

specs/rules/
├── rules_v3.yaml           # Authoritative rule catalogue (623 rules)
├── vpd_patterns.json       # Pattern annotations for VPD-able rules
├── pilot_v1_golden.yaml    # Golden test cases (55 entries)
├── l1_golden.yaml          # L1 golden test cases
├── locale_golden.yaml      # Locale golden test cases
├── stragglers2_golden.yaml # Stragglers batch 2 golden
├── l2_approx_golden.yaml   # L2-approx batch 1-2 golden
├── l2_batch3_golden.yaml   # L2-approx batch 3 golden
├── l2_batch4_golden.yaml   # L2-approx batch 4 golden
├── l5_expl3_tikz_golden.yaml  # expl3/TIKZ/LANG golden
├── l3_text_approx_golden.yaml # L3 text-approx golden
└── unicode_golden.yaml     # Unicode golden test cases
```

### Archived / Gated Prototypes
```
core/                           # Legacy L0-L4 experiments (may be disabled)

proofs/archive/                 # Historical proof drafts kept for reference
```

Note on reuse: `core/l0_lexer` reuses the production runtime via symlinks to
`latex-parse/src` (e.g., arena, broker, service components). This keeps
prototypes and benches aligned with the active runtime without duplication.
When editing runtime modules, prefer touching files under `latex-parse/src/` —
the symlinks in `core/l0_lexer/` will reflect those changes automatically.

### Formal Proofs
```
proofs/
├── dune                        # Coq theory stanza (coq.theory, added W14)
├── CoreProofs.v                # Live zero-admit baseline (L0 core)
├── Catcode.v                   # Category code proofs
├── Arena_safe.v                # Arena safety proofs
├── LexerSoA.v                  # SoA window equivalence
├── LexerFaithfulStep.v         # Step determinism & progress
├── Expand.v                    # L1 fuel-bounded expansion model (added W14)
└── archive/                    # Historical proof drafts
```

### Shared Assets
```
data/                           # Shared OCaml data structures
corpora/                        # Test data (perf_smoke, etc.)
specs/                          # Authoritative plans & rule catalogues
```

## 📊 Performance Status

### Current Baseline
| Area | Target | Repository State | Notes |
|------|--------|------------------|-------|
| Build | `dune build` green | ✅ | Active for `latex-parse/` modules |
| Proof admits | 0 | ✅ | 15 proof files (+ 7 archive), 316 theorems, 0 admits |
| Proof locality | Window equivalence | ✅ | `proofs/LexerSoA.v` (kinds/codes/offs/issues) |
| Performance snapshot | record p95 | A+B p95 = 3.25 ms (measured 2026-02-22) | `ab_microbench` on `perf_smoke_big` |
| Performance gate | p95 ≤ 20 ms (Tier A) | ✅ | 6.2× headroom |
| First-token p95 | ≤ 350 µs | ✅ | p95 = 27 µs (13× headroom) |
| Edit-window p95 | < 1ms | ✅ | p95 = 0.012 ms (250× headroom) |
| Validators | 623 total | 452 spec-matched (72.6%) | L0: 97.9%, L1: 89.2%, L2: 97.9%, L3: 21.4%, L4: 14.3% |

### Long-term Targets (Week 156 GA)
| Metric | Target | Current | Progress |
|--------|--------|---------|----------|
| Validators | 623 | 452 spec-matched | 72.6% |
| Languages | 21 | 6 live + 15 stubbed | 29% |
| Edit-window p95 | < 1ms | ✅ | p95 = 0.012 ms (250× headroom) |
| False-positive rate | < 0.1% | pending | - |

## 🛠️ Quick Commands Reference

### Build Commands
```bash
# Complete build (service + benches)
OPAMSWITCH=l0-testing opam exec -- dune build
```

### Testing Commands
```bash
# Quick validation (1K iterations)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 1000 --csv /tmp/ab_microbench.csv

# Extended validation (10K iterations)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 10000 --csv /tmp/ab_microbench.csv
```

## 📖 Documentation Guide

### Primary References (v25_R1)
1. **specs/v25_R1/v25_master_R1.md** - Single source of truth
2. **specs/v25_R1/PLANNER_v25_R1.yaml** - Complete 156-week timeline
3. **specs/v25_R1/L0_LEXER_SPEC_v25_R1.md** - L0 layer specification

### Project Documentation
1. **README.md** - Project overview and Week 1 status
2. **docs/BUILD_SYSTEM_GUIDE.md** - Build instructions
3. **docs/NEXT_STEPS_PLAN.md** - Immediate priorities (Weeks 2-5)
4. **docs/PROOFS.md** - Summary of formal model and lemmas
5. **docs/REST_API.md** - REST façade endpoints and JSON schema
6. **docs/VALIDATORS_RUNTIME.md** - Runtime validators, feature flag, results shapes
7. **docs/RULES_IMPLEMENTATION_PLAN.md** - Rules rollout plan and gates
8. **docs/RULES_PILOT_TODO.md** - Pilot TODOs and checklist
9. **docs/UNIT_TESTS.md** - Unit/property tests and how to add more

## 🧪 CI Checks
- CI (build): builds @all, runs tests.
- Format check: enforces `dune fmt --check` and uploads a patch if violations are found.
- REST Smoke Test: builds the service and REST façade and exercises `POST /tokenize`.
- Validators Pilot Smokes:
  - `.github/workflows/validators-pilot-smoke.yml` (REST on `/expand`)
  - `.github/workflows/validators-pilot-smoke-cli.yml` (CLI fallback, no TCP bind)
- Catalogue Compliance: `.github/workflows/catalogue-compliance.yml` (IDs, severities, preconditions)
- Catalogue Deep Validation: `.github/workflows/catalogue-deep.yml` (normalized rules index JSON)
- REST Schema Validation: `.github/workflows/rest-schema.yml` (unified `.validators` shape)
- Latency Nightly: `.github/workflows/latency-nightly.yml` (runs `/expand` smoke, uploads latencies, publishes badge to `gh-pages`)

### Badges

- Expand latency p95 badge (nightly) is published to `gh-pages/public-badges/expand_latency.json` and embedded in README within the `LAT_BADGE_START/END` block.

## 🎯 Upcoming Milestones

### Phase 2 Immediate (Weeks 14-17) — EXIT CRITERIA MET
- **Week 14** ✅: Phase 2 kickoff — Expand.v, proofs/dune, fuel-bounded model
- **Week 15** ✅: All expansion proofs QED (decreases_ctrls, terminates_acyclic, fuel_insensitive)
- **Week 17** ✅: expand_no_teof QED exit criterion (met ahead of schedule at W15)

### Q1 Gates (Weeks 1-13) — ALL PASSED
- **Week 1** ✅: Bootstrap complete
- **Week 5** ✅: Performance α gate (p95 < 20ms)
- **Week 10** ✅: Proof β gate (admits = 0)

### Q2 Gates (Weeks 14-26) — ALL PASSED
- **Week 26** ✅: L0-L1 formal checkpoint (100% actionable rules, 0 admits)

### Validator Sprint (Weeks 17-25) — COMPLETE
- **Week 17**: L1 batch completion (DELIM, SCRIPT, MATH-A/B/C, REF, CHEM, L3)
- **Week 18**: Locale rules + stragglers
- **Weeks 19-23**: L2-approximable batches 1-4 (FIG, TAB, PKG, CJK, FONT, MATH, REF, CMD, DOC, LANG, TIKZ)
- **Weeks 24-25**: Text-scannable Draft rules (expl3, TIKZ, LANG, BIB, LAY, META, PDF)
- **Result**: 452/623 spec-matched rules (72.6%) — all text-scannable rules exhausted

### Major Milestones (Upcoming)
- **Weeks 27-30**: Generic proof tactics (RegexFamily) — auto-proof < 50 ms/validator
- **Weeks 31-35**: ML span extractor training — F1 ≥ 0.94
- **Week 39**: Scalar optimization complete
- **Week 52**: L2 delivered (p95 < 1.2 ms end-to-end)
- **Week 78**: Style α gate (430 validators)
- **Week 156**: v25 General Availability

## 🗂️ File Navigation

**Essential Files**:
- `specs/v25_R1/v25_master_R1.md` - Master specification
- `README.md` - Current status
- `Makefile` - Build commands
- `latex-parse/bench/ab_microbench.exe` - Performance testing
- `corpora/perf/perf_smoke_big.tex` - 1.1MB test dataset

---

**Week 30 Status**: 452/623 spec-matched validators (72.6%). L0-L2 layers nearly complete (97.9%/89.2%/97.9%). L3/L4 gaps need semantic/NLP infrastructure. Next per timeline: W40-52 L2 parser + proofs.
