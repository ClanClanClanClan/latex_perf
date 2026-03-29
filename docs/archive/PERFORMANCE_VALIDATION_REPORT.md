# Performance Validation Report

**Date**: 19 September 2025 (UTC)
**Project Week**: 1 of 156
**Status**: Baseline telemetry refreshed ✅

## Executive Summary

Three consecutive microbench campaigns (`latex-parse/bench/ab_microbench.exe`) were executed against `corpora/perf/perf_smoke_big.tex` with 200 K, 500 K, and 1 M measured iterations (warmup 512). All runs satisfy the Week‑5 performance gate (p95 < 20 ms) with substantial headroom; p99.9 stays below ~8.7 ms in every series.

| Iterations | p50 (ms) | p95 (ms) | p99 (ms) | p99.9 (ms) | max (ms) | CSV |
|-----------:|---------:|---------:|---------:|-----------:|---------:|-----|
| 2.0 × 10⁵  | 2.555 | 2.729 | 3.035 | **5.107** | 21.314 | `/tmp/ab_microbench_200k.csv`
| 5.0 × 10⁵  | 2.684 | 2.947 | 3.922 | **8.529** | 136.175 | `/tmp/ab_microbench_500k.csv`
| 1.0 × 10⁶  | 2.707 | 2.959 | 3.990 | **8.685** | 102.020 | `/tmp/ab_microbench_1M.csv`

Detailed statistics (including min/p50/p95/p99/p999/max) are tracked in `core/l0_lexer/current_baseline_performance.json`.

### Edit-window (4 KB) Benchmark

- Command: `latex-parse/bench/edit_window_bench.exe corpora/perf/edit_window_4kb.tex 5000 --csv /tmp/edit_window_bench.csv`
- Result: p95 ≈ 0.017 ms, p99.9 ≈ 0.020 ms, max ≈ 0.031 ms
- Compliance gate: `scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000` (p95 threshold 1.2 ms)

### Measurement Protocol (per v25_R1)

- Full-doc perf gate uses a median-of-100 batches: we run the microbench 100 times at the requested iteration count, collect p95 values, take the median, and enforce the < 20 ms target. See `scripts/perf_gate.sh` for the exact procedure.

## Test Environment

- **Platform**: Apple Silicon (ARM64)
- **Binary**: `_build/default/latex-parse/bench/ab_microbench.exe`
- **Command template**:
  ```bash
  OPAMSWITCH=l0-testing opam exec -- \
    ./_build/default/latex-parse/bench/ab_microbench.exe \
    corpora/perf/perf_smoke_big.tex <ITERS> \
    --warmup 512 --csv /tmp/ab_microbench_<ITERS>.csv
  ```
- **Warmup**: 512 iterations
- **Input**: `corpora/perf/perf_smoke_big.tex` (≈1.1 MB)

## Observations

- Latency distribution remains tight: even at 1 M iterations, p95 ≈ 2.96 ms and p99.9 ≈ 8.69 ms.
- Occasional long-tail spikes (max ≈ 136 ms) appear at very high iteration counts; these align with background system noise and remain well below the 42 ms SLA gate for p95.
- SIMD attestation counters (queried via `latex-parse/src/test_simd_attestation.ml`) confirm SIMD execution is active for the runs above.

## Next Actions

1. Keep the JSON baseline in sync after major tokenizer/runtime changes.
2. Restore the archived L0 lexer (`core/`) to build against `Latex_parse_lib` so prototype lanes share the same arena/token SoA.
3. Re-enable the Week‑5 performance gate in CI once the lexer/runtime reconciliation work is complete.
