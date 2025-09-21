# LaTeX Perfectionist v25

![Nightly Perf](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/badges/perf.json)
<!-- LAT_BADGE_START -->
![Expand Latency p95](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/${REPO:-${GITHUB_REPOSITORY}}/gh-pages/public-badges/expand_latency.json)
<!-- LAT_BADGE_END -->
<!-- LAT_L1_BADGE_START -->
![L1 Expand Latency p95](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/${REPO:-${GITHUB_REPOSITORY}}/gh-pages/public-badges/expand_latency_l1.json)
<!-- LAT_L1_BADGE_END -->
<!-- UNIT_TESTS_BADGE_START -->
![Unit Tests](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/${REPO:-${GITHUB_REPOSITORY}}/gh-pages/public-badges/unit_tests.json)
<!-- UNIT_TESTS_BADGE_END -->
![Perf Sparkline](https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/badges/perf_spark.svg)

**3-Year Project - Week 1 of 156** - Comprehensive LaTeX document analysis and style validation system.

LaTeX Perfectionist v25 is a 3-year solo-developer project to build a formally-verified, high-performance LaTeX validation system with 623 rules across 21 languages.

## Current Status (Week 1 - September 2025)

Baseline after the Week‑1 audit clean-up:
- **Build**: `dune build` compiles the SIMD service and benches under `latex-parse/`. Legacy prototypes in `core/` are archived (`dune.disabled`) until they are rebuilt against the new runtime.
- **Proofs**: The zero-admit baseline is preserved via `proofs/CoreProofs.v`, `proofs/Catcode.v`, and `proofs/Arena_safe.v`. Earlier drafts remain in `proofs/archive/` and do not participate in the build.
  Recent additions: `proofs/LexerSoA.v` (SoA small-step + big-step with window locality and stability), `proofs/LexerFaithfulStep.v`, `proofs/LexerDeterminism.v`, `proofs/LexerTotality.v` — all admit-free.
- **Validators & Languages**: Implementation of the 623-rule catalog is still tracked in `specs/`; no production validators ship in this repository yet.
- **Performance**: Harnesses (`latex-parse/bench`, `scripts/perf_gate.sh`, `scripts/edit_window_gate.sh`) are in place. Latest runs on `perf_smoke_big` show p95 ≈ 2.73 ms (200 k iters) and ≈ 2.96 ms (1 M iters), with p99.9 ≈ 8.69 ms; the 4 KB edit-window bench lands at p95 ≈ 0.017 ms. See `core/l0_lexer/current_baseline_performance.json` and re-run after major changes.

### Week 1 Deliverables
- ✅ Repository and build hygiene pass: legacy OCaml/Coq drafts archived, modern build unblocked
- ✅ Coq baseline restored (CoreProofs.v / Catcode.v / Arena_safe.v, 0 admits, 0 axioms)
- ✅ Performance harness wired up (bench + gate scripts)
- 🔄 Rebuild L0 lexer/validator implementations on top of the refreshed runtime

## Quick Start

```bash
# Build the SIMD service and benches
OPAMSWITCH=l0-testing opam exec -- dune build

# Run the micro-benchmark once the service is built
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 1000 --csv /tmp/ab_microbench.csv

# Start/stop the unix-socket service
make service-run
make service-stop
 
# Expose Prometheus metrics (http://127.0.0.1:9109/metrics)
L0_PROM=1 make service-run

# Optional REST façade (requires service on /tmp/l0_lex_svc.sock)
make rest-run   # starts REST on http://127.0.0.1:8080
make rest-stop
```

### Metrics

- `L0_PROM=1` enables the built-in Prometheus exporter.
- `L0_PROM_ADDR=HOST:PORT` controls TCP bind (default `127.0.0.1:9109`).
- `L0_PROM_UDS=/tmp/l0_prom.sock` serves metrics over a Unix socket (useful if TCP bind is restricted).
- Metrics include total requests, errors, hedge fires/wins, worker rotations, and latency histogram buckets.
- Curl examples:
  - `curl http://127.0.0.1:9109/metrics`
  - `curl --unix-socket /tmp/l0_prom.sock http://localhost/metrics`
  - Leave `L0_PROM` unset for zero-overhead runs.

### Nightly Trends

- Dashboard: https://ClanClanClanClan.github.io/latex_perf
- Badge above reflects full-doc p95 (median-of-100).

### Edit-window Benchmark

```bash
# Measure 4 KB edit-window performance
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/edit_window_bench.exe \
  corpora/perf/edit_window_4kb.tex 5000 --csv /tmp/edit_window_bench.csv

# Fast compliance gate (p95 ≤ 1.2 ms)
OPAMSWITCH=l0-testing opam exec -- \
  bash scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000
```

### Edit Replay (incremental)

```bash
# Simulate 2K incremental edits (inserts/deletes) with a 4 KB window
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/edit_replay_bench.exe \
  corpora/perf/edit_window_4kb.tex 2000 --window 4096 --csv /tmp/edit_replay_2k.csv
```

### A/B Compare (direct vs service)

```bash
OPAMSWITCH=l0-testing opam exec -- bash scripts/ab_compare.sh corpora/perf/perf_smoke_big.tex 10000
```

### Expander + Validators (CLI smoke)

```bash
# Build and run the simple expander smoke (strips \textbf/\emph/\section braces)
OPAMSWITCH=l0-testing opam exec -- dune build core/l1_expander/expander_smoke.exe
./_build/default/core/l1_expander/expander_smoke.exe | jq .
# Example JSON keys: .expanded, .validators (id,severity,message,count)
```

### REST Validators (end-to-end)

```bash
make service-run
make rest-run
curl -s -X POST http://127.0.0.1:8080/tokenize \
  -H 'Content-Type: application/json' \
  -d '{"latex":"\\section{Title} Text with\t tab."}' | jq .validators
# Returns validators summary (applied/errors/results array)
```

Note: to enable the pilot L0 rules aligned with `rules_v3.yaml` (e.g., TYPO-001…010), set `L0_VALIDATORS=pilot` (or `1`/`true`) in the environment before starting the REST server (see also `docs/VALIDATORS_RUNTIME.md`):

```bash
L0_VALIDATORS=pilot make rest-run
# or
export L0_VALIDATORS=1 && make rest-run
```

#### Pilot Smoke

Once REST is running with `L0_VALIDATORS=pilot`, you can smoke-test the first 10 L0 rules via the `/expand` endpoint (does not require the SIMD service):

```bash
# Each case expects a specific TYPO-00x to appear
bash scripts/smoke_rules_pilot.sh  # default http://127.0.0.1:8080/expand

# Optional: latency smoke on /expand (N requests) + gate summary
bash scripts/latency_smoke_expand.sh 200
```

### Token Debugging & Layer Gating

- Token snapshots: see `docs/VALIDATORS_RUNTIME.md` → Token Debugging. Enable `L0_DEBUG_TOKENS=1` and POST `/tokens`.
- Layer gating: add `?layer=l1` to `/expand` to run L1-only rules.

## Project Timeline Overview

### Q1 (Weeks 1-13) - Current Quarter
- **Week 1** ✅: Bootstrap skeleton, repo restructure, _CoqProject
- **Week 2-3**: Catcode module + proofs
- **Week 4**: Chunk infra, xxHash scalar
- **Week 5** 🎯: Performance α gate (Tier A p95 < 20ms)
- **Week 6-8**: Incremental Lexer proof
- **Week 9**: SIMD xxHash
- **Week 10** 🎯: Proof β gate (admits ≤ 10)

### Q2-Q4 (Weeks 14-52)
- L1 macro expander + proofs
- SIMD tokenizer implementation (Weeks 40-48)
- Validator DSL v1
- L2 parser delivery

### Years 2-3 (Weeks 53-156)
- Complete 623 validators
- 21 language support
- ML-assisted pattern generation
- Performance target: <1ms edit-window latency
- **Week 156**: v25 General Availability

## Performance Targets

Per v25_R1 L0_LEXER_SPEC:

| Metric | Tier A (Scalar) | Tier B (SIMD) | Repository Baseline |
|--------|-----------------|---------------|---------------------|
| Full-doc p95 (1.1MB) | ≤ 20ms | ≤ 8ms | p95 ≈ 2.96 ms (1 M) |
| Edit-window p95 (4 KB) | ≤ 3ms | ≤ 1.2ms | p95 ≈ 0.017 ms (5 K) |
| First-token latency | ≤ 350μs | ≤ 200μs | planned |

## Architecture

Per v25_R1 specification:
- **Implementation Baseline**: OCaml-first L0 runtime with optional performance lanes
- **Five-Layer Architecture**: L0 (Lexer) → L1 (Expander) → L2 (Parser) → L3 (Semantics) → L4 (Style)
- **Current Focus**: L0 Lexer implementation and optimization
- **Proof Strategy**: Zero admits maintained, Coq formal verification

### SIMD Implementation

The R1 baseline is the OCaml L0 runtime. SIMD acceleration is available via:
- **Rust SIMD lane**: AVX-512/AVX2/NEON intrinsics with runtime feature detection
- **C-extension lane**: Currently enabled on Apple Silicon (NEON) and auto-disabled if slower
- **Performance policy**: Feature-flagged, auto-disabled if slower than baseline per R1 specifications

## Documentation

### v25_R1 Specifications
- **specs/v25_R1/v25_master_R1.md**: Master plan (single source of truth)
- **specs/v25_R1/L0_LEXER_SPEC_v25_R1.md**: L0 Lexer specification
- **specs/v25_R1/PLANNER_v25_R1.yaml**: Complete 156-week timeline

### Project Documentation
- **docs/PROJECT_INDEX.md**: Project structure and navigation
- **docs/UNIT_TESTS.md**: Unit/property tests overview and how to add more
- **docs/BUILD_SYSTEM_GUIDE.md**: Build and deployment instructions
- **docs/NEXT_STEPS_PLAN.md**: Immediate development priorities

## Key Success Metrics (v25 GA - Week 156)

- 623 validators implemented
- 21 languages supported
- <1ms p99 edit-window latency
- 0 proof admits
- <0.1% false-positive rate

---

**Status**: Build and proof baselines restored; rebuilding the L0 lexer + validator implementation is the next milestone before re-running the Week‑5 performance gate.
### First‑Token Latency (Tier A target ≤ 350 µs)

```bash
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/first_token_latency.exe \
  corpora/perf/edit_window_4kb.tex 2000 --window 4096 --csv /tmp/first_token_latency.csv
```

### Hash Throughput (Week‑9 scaffolding)

```bash
make hash-bench
# or
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/hash_throughput.exe \
  corpora/perf/perf_smoke_big.tex 50 --csv /tmp/hash_throughput.csv

# Optional C lane (feature-flagged; falls back to scalar if not available)
L0_USE_SIMD_XXH=1 OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/hash_throughput.exe \
  corpora/perf/perf_smoke_big.tex 50
```

### L1 Expander A/B (enabled for experimentation)

```bash
OPAMSWITCH=l0-testing opam exec -- dune build core/l1_expander
./_build/default/core/l1_expander/l1_ab_test.exe corpora/perf/edit_window_4kb.tex --csv /tmp/l1_ab.csv
```
