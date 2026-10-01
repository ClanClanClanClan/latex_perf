# LaTeX Perfectionist

A LaTeX linter (660 rules specified) with a heuristic compile-readiness check. The Coq development proves properties of an abstract document model, not of the shipped rules, and **no document gets a proven compile verdict today**. The measured position lives in [v27/PROJECT_STATE.md](v27/PROJECT_STATE.md), which wins wherever this page disagrees; [COMPILATION_GUARANTEE.md](COMPILATION_GUARANTEE.md) says what the compile verdict means.

## Quick Links

- [Architecture Overview](ARCH.md) — Five-layer pipeline, Elder runtime
- [Proof Guide](PROOF_GUIDE.md) — Proof conventions and taxonomy
- [Support Matrix](SUPPORT_MATRIX.md) — Engines, packages, proof classes
- [Risk Register](../governance/risk-register.md) — 33 tracked risks

## Current Status

| Metric | Value |
|--------|-------|
| Rules specified | 660 (17 reserved) |
| Rules shipped | 643 / 660 |
| Fix-producing rules | 164, of which the default `--apply-fixes` applies 1 (MATH-106; allow-list, OPEN-112). The rest are opt-in. |
| Proof-class labels | 637 faithful, 20 conservative, 3 conditional (= 660). These are labels, not measurements: "faithful" is the generator's default. The "643 per-rule" once shown here was the non-reserved rule headcount. |
| Total theorems/lemmas | 1,591 across 192 Coq files. 803 of them are generated per-rule theorems sharing one proof body (`qed_text_sound`); the other 788 are everything else. |
| Rules stage per keystroke (300 KB) | 203.3 ms against a 30 ms budget, 6.8× over (perf-ci run 36683234282, `84b8f6ef`, 2026-09-30) |
| L0 tokenizer only, 1.1 MB file | p95 ≈ 2.8 ms (`core/l0_lexer/current_baseline_performance.json`, 2026-02-08; tokenizer alone, not a keystroke latency) |
| Admits / Axioms | 0 / 0 |
| Languages | Rules for several languages. The old "7 live + 14 stubbed = 21" row was three hard-coded integers, not a measurement. |

## Getting Started

```bash
# Build everything
opam exec -- dune build @all

# Run all tests
opam exec -- dune runtest

# Start the service
make service-run

# Run performance gate
bash scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 50
```
