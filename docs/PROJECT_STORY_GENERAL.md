# LaTeX Perfectionist v25 — What We Are Building

LaTeX Perfectionist v25 sets out to become the reliability layer for scientific and technical writing. Authors love LaTeX for the precision it gives them, yet even seasoned teams struggle to keep manuscripts free of subtle syntax slips, style drifts, and formatting inconsistencies. This project aims to deliver an automated reviewer that catches those issues instantly and with guarantees about correctness.

## Why This Project Matters
- **Error prevention at scale:** Misplaced braces, mismatched math delimiters, and stray ASCII quotes routinely break document builds or delay publication. A dependable checker removes that friction.
- **Trustworthy results:** Every rule in the 623-item catalog is slated for formal verification in Coq, so the system can prove it is not inventing errors or overlooking real ones.
- **Inclusive by design:** Targeting 21 languages and culturally-aware templates means international research teams can apply the same quality bar everywhere.
- **Productivity boost:** Tight feedback loops let authors fix issues while they write, instead of after long CI runs or editorial reviews.

## How We Are Approaching It
1. **High-speed foundation:** The current focus is the L0 lexer — a service that tokenizes large LaTeX documents or 4 KB edit windows in just a few milliseconds. Benchmarks (`core/l0_lexer/current_baseline_performance.json`) show p95 latencies under 3 ms for 1.1 MB files and 0.017 ms for edit windows.
2. **Layered architecture:** The lexer feeds into future layers for macro expansion (L1), parsing (L2), semantics (L3), and style guidance (L4). Each layer adds richer understanding while keeping earlier guarantees intact.
3. **Formal verification:** Zero-admit Coq proofs already cover the SoA lexer model (`proofs/LexerSoA.v`) and supporting components (`proofs/CoreProofs.v`, `proofs/Catcode.v`, `proofs/Arena_safe.v`). New rules will ship alongside proofs to maintain that standard.
4. **Operational readiness:** The runtime runs as a Unix-socket service with optional REST (`docs/REST_API.md`) and Rust/Tokio (`rust/`) façades. Prometheus metrics, performance gates, and soak scripts ensure regressions are caught early.

## Where We Stand Today
- **Week 1 baseline restored:** Build, proof, and performance scaffolding are clean after the audit (`README.md`, `docs/PROJECT_INDEX.md`).
- **Pilot validators:** Foundational typo checks (e.g., curly quotes enforcement) are in place under a feature flag while the broader catalog is staged (`latex-parse/src/validators.ml`).
- **Tooling in place:** Benchmarks, acceptance gates, and CI workflows guard latency targets and proof hygiene (`Makefile`, `scripts/perf_gate.sh`, `.github/workflows/*`).

## The Road Ahead
- Reconcile archived prototypes in `core/` with the active SIMD runtime, then widen validator coverage layer by layer.
- Maintain the <20 ms full-document and <1 ms edit-window goals as new features land.
- Roll out the 623-rule catalog in disciplined batches, each with proofs, golden corpora, and telemetry.
- Expand multi-language support, guided by the master specification (`specs/v25_R1/v25_master_R1.md`) and the rules implementation plan (`docs/RULES_IMPLEMENTATION_PLAN.md`).

## What Success Looks Like
By Week 156, LaTeX Perfectionist v25 aims to give authors, editors, and publishers a shared, provably correct safety net. Documents stay consistent and publication-ready, teams receive instant feedback without sacrificing accuracy, and the tooling integrates smoothly with existing workflows. In short: polished LaTeX, verified at every step.
