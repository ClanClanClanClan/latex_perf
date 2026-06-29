# LaTeX Perfectionist v27.0.72

Comprehensive LaTeX document analysis and style validation system with 660 rules across 21 languages, backed by formal Coq proofs.

## Quick Links

- [Architecture Overview](ARCH.md) — Five-layer pipeline, Elder runtime
- [Proof Guide](PROOF_GUIDE.md) — Proof conventions and taxonomy
- [Support Matrix](SUPPORT_MATRIX.md) — Engines, packages, proof classes
- [Risk Register](../governance/risk-register.md) — 33 tracked risks

## Current Status

| Metric | Value |
|--------|-------|
| Rules specified | 660 (16 reserved) |
| Rules shipped | 644 / 660 |
| Fix-producing rules | 115 (Bucket A rolling cadence, see [V27_FIX_PRODUCER_CADENCE.md](../specs/v27/V27_FIX_PRODUCER_CADENCE.md)) |
| Soundness theorems | 644 per-rule (637 faithful, 20 conservative, 3 conditional) |
| Total theorems/lemmas | 1,400 across 170 Coq files |
| Performance p95 (L1 expand) | ≈ 2.8 ms (gate: 20 ms, Tier A) |
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
