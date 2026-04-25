# LaTeX Perfectionist v26.3.0

![Nightly Perf](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/badges/perf.json)
<!-- LAT_BADGE_START -->
![Expand Latency p95](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/public-badges/expand_latency.json)
<!-- LAT_BADGE_END -->
<!-- LAT_L1_BADGE_START -->
![L1 Expand Latency p95](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/public-badges/expand_latency_l1.json)
<!-- LAT_L1_BADGE_END -->
<!-- UNIT_TESTS_BADGE_START -->
![Unit Tests](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/public-badges/unit_tests.json)
<!-- UNIT_TESTS_BADGE_END -->
![Perf Sparkline](https://raw.githubusercontent.com/ClanClanClanClan/latex_perf/gh-pages/badges/perf_spark.svg)

LaTeX Perfectionist is a formally-verified, high-performance LaTeX validation system with 660 rules across 21 languages. See [specs/v26/](specs/v26/) for the v26 language contract, support matrix, and workstream roadmap; [specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md](specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md) for the architecture memo.

## Installation

### From Source (opam + dune)

```bash
# Prerequisites: opam 2.1+, OCaml 5.1.1+
opam switch create latex-perf 5.1.1
eval $(opam env)
opam install coq.8.18.0 coq-core.8.18.0 re yojson uutf
dune build @all
```

### Docker

```bash
docker pull ghcr.io/clanclanclanclan/latex_perf:latest
docker run --rm -v $(pwd):/data ghcr.io/clanclanclanclan/latex_perf:latest /data/paper.tex
```

## CLI Reference

```bash
# Validate a LaTeX file (all layers)
dune exec latex-parse/src/validators_cli.exe -- paper.tex

# Validate with a specific layer only
dune exec latex-parse/src/validators_cli.exe -- --layer l0 paper.tex
dune exec latex-parse/src/validators_cli.exe -- --layer l2 paper.tex
```

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `L0_VALIDATORS` | unset | Set to `pilot` to enable pilot L0 TYPO rules |
| `LP_ML_CONFIDENCE_MAP` | unset | Path to ML confidence map JSON (suppresses zero-TP rules) |
| `LP_SCORING_CONFIG` | unset | Path to evidence scoring config JSON |
| `L0_PROM` | unset | Set to `1` to enable Prometheus metrics exporter |
| `L0_PROM_ADDR` | `127.0.0.1:9109` | Prometheus TCP bind address |
| `L0_USE_SIMD_XXH` | unset | Set to `1` for SIMD xxHash acceleration |

## Current Status — v26.1 (April 2026)

All layers (L0-L4) implemented. L3 file-based validators (PNG/JPEG/PDF/font). ML v2 byte classifier trained (F1=0.9799) and formally verified:
- **Build**: `dune build` compiles the SIMD service, benches, and the Coq proof tree (33 core + 108 generated + 1 ML) via `(coq.theory)` stanzas.
- **Proofs**: 142 Coq files, 1,133 theorems/lemmas. 644 per-rule soundness (637 faithful, 20 conservative, 3 conditional). 0 admits, 0 axioms. ML: `v2_span_extractor_sound` QED.
- **Validators**: 638 rule IDs / 654 spec. 329 golden corpus tests, ~7,800 test cases across 89 suites. 19 L3 file-based + 12 expl3 rules.
- **Macros**: 520 production macros (441 symbols + 79 argsafe) with multi-arg support.
- **ML Pipeline**: v2 ByteClassifier (CNN+BiLSTM, 538K params) trained on A100. F1=0.9799, precision=0.975, recall=0.985. Proved in `proofs/ML/SpanExtractorSound.v`.
- **Performance**: Harnesses (`latex-parse/bench`, `scripts/perf_gate.sh`, `scripts/edit_window_gate.sh`) are in place. Latest runs on `perf_smoke_big` show p95 ≈ 2.73 ms (200 k iters) and ≈ 2.96 ms (1 M iters), with p99.9 ≈ 8.69 ms; the 4 KB edit-window bench lands at p95 ≈ 0.017 ms. See `core/l0_lexer/current_baseline_performance.json` and re-run after major changes.

### Milestones
- ✅ v25.0.0 (2026-04-14): rule coverage + ML v2 + SIMD + chunk store
- ✅ v26.0.0 (2026-04-18): WS0-WS6 — truth-surface freeze, compile-log Class C, bounded macro registry, project graph, hybrid invalidation, partial-document semantics, testing hardening
- ✅ v26.1.0 (2026-04-20): formal language contract + real validator DAG + ExecutionClasses proof + support_matrix.yaml + E2/E3 editing proofs + expanded compile-log (LAY-025/026/027) + governance regen
- ✅ v26.2.0 (2026-04-23): compile-guarantee stack T0–T7 (runtime `Compile_contract` + ProjectClosure/BuildProfileSound/CompileProgress/CompileWellFormed + T0/T1/T4/T5 wrappers) + byte-lossless CST (`Cst`, `Cst_of_ast`, `Stable_spans`; 345/345 corpora round-trip) + rewrite engine v1 (`Cst_edit`, `Rewrite_engine`) + preservation proofs (CSTRoundTrip, RewritePreservesCST, RewritePreservesSemantics)

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

## Performance Targets

| Metric | Target | Repository Baseline |
|--------|--------|---------------------|
| Full-doc p95 (1.1MB) | ≤ 20ms | p95 ≈ 2.96 ms (1 M iters) |
| Edit-window p95 (4 KB) | ≤ 1.2ms | p95 ≈ 0.017 ms (5 K iters) |
| First-token latency | ≤ 350μs (scalar) / ≤ 200μs (SIMD) | |

## Architecture

- **Five-layer pipeline**: L0 (Lexer) → L1 (Expander) → L2 (Parser) → L3 (Semantics) → L4 (Style).
- **Language contract** (v26): LP-Core / LP-Extended / LP-Foreign tiers. See [specs/v26/language_contract.md](specs/v26/language_contract.md).
- **Rule contracts** (v26.1): per-rule execution/proof/project metadata in [specs/rules/rule_contracts.yaml](specs/rules/rule_contracts.yaml); drives the validator DAG.
- **Execution classes**: A (keystroke-critical) / B (debounce) / C (build-coupled) / D (advisory). Formalised in [proofs/ExecutionClasses.v](proofs/ExecutionClasses.v).
- **Proof strategy**: 0 admits, 0 axioms; 142 Coq files, 1,130 theorems/lemmas.

### SIMD Implementation

- **Rust SIMD lane**: AVX-512/AVX2/NEON intrinsics with runtime feature detection.
- **C-extension lane**: enabled on Apple Silicon (NEON); auto-disabled if slower than scalar.
- Feature-flagged with auto-fallback.

## Documentation

- **[specs/v26/V26_REPO_EXACT_MASTER_SPEC.md](specs/v26/V26_REPO_EXACT_MASTER_SPEC.md)** — current release master spec
- **[specs/v26/language_contract.md](specs/v26/language_contract.md)** — LP-Core / LP-Extended / LP-Foreign tiers
- **[docs/SUPPORT_MATRIX.yaml](docs/SUPPORT_MATRIX.yaml)** — machine-readable support contract
- **[specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md](specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md)** — architecture memo (v26/v27 plan)
- **[docs/ARCH.md](docs/ARCH.md)** — architecture handbook
- **[docs/PROOFS.md](docs/PROOFS.md)** / **[docs/PROOF_GUIDE.md](docs/PROOF_GUIDE.md)** / **[docs/PROOF_CLASSES.md](docs/PROOF_CLASSES.md)**
- **[docs/SUPPORT_MATRIX.md](docs/SUPPORT_MATRIX.md)** — engine/package/interface support
- **[docs/BUILD_LOG_CONTRACT.md](docs/BUILD_LOG_CONTRACT.md)** — Class C compile-log contract
- **[docs/UNIT_TESTS.md](docs/UNIT_TESTS.md)**, **[docs/BUILD_SYSTEM_GUIDE.md](docs/BUILD_SYSTEM_GUIDE.md)**, **[docs/REST_API.md](docs/REST_API.md)**

## Success Metrics (v26.1)

- 660 rules specified / 643 shipped
- 631 formal faithful + 20 conservative + 3 conditional proofs
- 0 admits, 0 axioms
- 21-language target (7 live + 14 stubbed)
- p95 edit-window ≈ 0.017 ms (target ≤ 1.2 ms)

---

**Status**: v26.3.0 released. 644 validators implemented, 1,261 theorems across 159 Coq files (0 admits, 0 axioms), ML v2 byte classifier trained (F1=0.9799, proved). Compile-guarantee contract + byte-lossless CST + rewrite engine + per-rule fix producers live.

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
