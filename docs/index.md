# LaTeX Perfectionist v25

**3-Year Project — Week 80 of 156**

Comprehensive LaTeX document analysis and style validation system with 623 rules across 21 languages, backed by formal Coq proofs.

## Quick Links

- [Architecture Overview](ARCHITECTURE.md) — Two-project structure, layer model
- [Build System Guide](docs/BUILD_SYSTEM_GUIDE.md) — How to build and test
- [Rule Implementation](docs/RULES_IMPLEMENTATION_PLAN.md) — 568 / 623 rules implemented
- [Proof Infrastructure](docs/PROOFS.md) — 607 soundness theorems, 0 admits
- [ML Pipeline](ml/ARCHITECTURE.md) — Span extractor v2 design
- [Risk Register](governance/risk-register.md) — 31 tracked risks

## Current Status

| Metric | Value |
|--------|-------|
| Rules implemented | 568 / 623 (91.2%) |
| Soundness theorems | 607 (26 faithful, 581 conservative) |
| Golden corpus tests | 329 across 12 suites |
| Test suites | 56 |
| Performance p95 | 2.8 ms (gate: 20 ms) |
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
