# LaTeX Perfectionist v26.2.0

Comprehensive LaTeX document analysis and style validation system with 660 rules across 21 languages, backed by formal Coq proofs.

## Quick Links

- [Architecture Overview](ARCH.md) — Five-layer pipeline, Elder runtime
- [Proof Guide](PROOF_GUIDE.md) — Proof conventions and taxonomy
- [Support Matrix](SUPPORT_MATRIX.md) — Engines, packages, proof classes
- [Risk Register](../governance/risk-register.md) — 33 tracked risks

## Current Status

| Metric | Value |
|--------|-------|
| Rules specified | 654 (16 reserved) |
| Rules shipped | 638 / 654 |
| Soundness theorems | 644 per-rule (637 faithful, 20 conservative, 3 conditional) |
| Total theorems/lemmas | 1,133 |
| Test suites | 97 |
| Test cases | 3,254 |
| Performance p95 | 2.78 ms (gate: 25 ms) |
| Admits / Axioms | 0 / 0 |
| Languages | 7 live + 14 stubbed = 21 target |

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
