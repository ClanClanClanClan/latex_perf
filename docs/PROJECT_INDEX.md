# LaTeX Perfectionist v25 - Project Index

**Status**: Week 1 of 156 - Bootstrap Phase Complete
**Last Updated**: September 13, 2025
**Project Type**: 3-Year Solo-Developer Project (156 weeks total)

## 📋 Week 1 Status Summary

Week 1 clean-up outcomes:
- ✅ Repository and build hygiene: legacy OCaml/Coq drafts moved to `core/**` and `proofs/archive/`; modern build unblocks `latex-parse/`
- ✅ Coq baseline restored with `proofs/CoreProofs.v` (0 admits, 0 axioms)
- ✅ Performance harness retained (`latex-parse/bench`, `scripts/perf_gate.sh`)
- 🔄 Rebuild L0 lexer + validator implementations on top of the refreshed runtime before re-running gates

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

### Archived / Gated Prototypes
```
core/                           # Legacy L0-L4 experiments (disabled by default)
  ↳ Reactivate by temporarily renaming `dune.disabled` → `dune`

proofs/archive/                 # Historical proof drafts kept for reference
```

Note on reuse: `core/l0_lexer` reuses the production runtime via symlinks to
`latex-parse/src` (e.g., arena, broker, service components). This keeps
prototypes and benches aligned with the active runtime without duplication.
When editing runtime modules, prefer touching files under `latex-parse/src/` —
the symlinks in `core/l0_lexer/` will reflect those changes automatically.

### Shared Assets
```
proofs/CoreProofs.v             # Live zero-admit baseline
data/                           # Shared OCaml data structures
corpora/                        # Test data (perf_smoke, etc.)
specs/                          # Authoritative plans & rule catalogues
```

## 📊 Performance Status

### Week 1 Baseline (post-clean-up)
| Area | Target | Repository State | Notes |
|------|--------|------------------|-------|
| Build | `dune build` green | ✅ | Active for `latex-parse/` modules |
| Proof admits | 0 | ✅ | `proofs/CoreProofs.v`, `proofs/Catcode.v`, `proofs/Arena_safe.v` |
| Proof locality | Window equivalence | ✅ | `proofs/LexerSoA.v` (kinds/codes/offs/issues) |
| Performance snapshot | record p95 | p95 ≈ 2.73 ms (200 k iters), ≈ 2.96 ms (1 M iters) | `ab_microbench` on `perf_smoke_big` (see `core/l0_lexer/current_baseline_performance.json`) |
| Performance gate | p95 < 20 ms (Tier A) | ✅ | `scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 100` |
| Edit-window p95 | < 1ms | ✅ | `scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000` (p95 ≈ 0.017 ms) |
| Validators | 623 total | TODO | Implementation tracked in specs |

### Long-term Targets (Week 156 GA)
| Metric | Target | Current | Progress |
|--------|--------|---------|----------|
| Validators | 623 | specs-only | 0% in repo |
| Languages | 21 | specs-only | 0% in repo |
| Edit-window p95 | < 1ms | pending | - |
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

### Immediate (Weeks 2-5)
- **Week 2-3**: Catcode module + proofs
- **Week 4**: Chunk infra, xxHash scalar
- **Week 5** 🎯: Performance α gate (p95 < 20ms mandatory)

### Q1 Gates (Weeks 1-13)
- **Week 1** ✅: Bootstrap complete
- **Week 5** 🎯: Performance α gate
- **Week 10** 🎯: Proof β gate (admits ≤ 10)

### Major Milestones
- **Week 26**: L0-L1 formal checkpoint
- **Week 39**: Scalar optimization complete
- **Week 48**: SIMD optional gate
- **Week 52**: L2 delivered
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

**Week 1 Status**: ✅ Build + proof baselines restored; performance and validator work resume after the lexer/runtime rebuild.
