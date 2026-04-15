# LaTeX Perfectionist v25.0.0

**3-Year Project — Week 80 of 156**

Comprehensive LaTeX document analysis and style validation system with 642 rules across 21 languages, backed by formal Coq proofs.

## Quick Links

- [Architecture Overview](ARCH.md) — Five-layer pipeline, Elder runtime
- [Proof Guide](PROOF_GUIDE.md) — Proof conventions and taxonomy
- [Support Matrix](SUPPORT_MATRIX.md) — Engines, packages, proof classes
- [Risk Register](../governance/risk-register.md) — 33 tracked risks

## Current Status

| Metric | Value |
|--------|-------|
| Rules specified | 642 (16 reserved) |
| Rules shipped | 626 / 642 |
| Soundness theorems | 626 per-rule (606 faithful, 20 conservative) |
| Total theorems/lemmas | 1,067 |
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
