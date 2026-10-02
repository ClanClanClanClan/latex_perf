# Documentation Index

## Current (actively maintained)

**Start here:** [v27/PROJECT_STATE.md](v27/PROJECT_STATE.md) is the single source of truth for
the measured position (generated block, OPEN ledger, corrections log), and
[COMPILATION_GUARANTEE.md](COMPILATION_GUARANTEE.md) states what the compile verdict does and does
not guarantee. Where any file below disagrees with them, they win.

| File | Purpose |
|------|---------|
| [v27/PROJECT_STATE.md](v27/PROJECT_STATE.md) | Measured position, OPEN ledger, corrections log (source of truth) |
| [COMPILATION_GUARANTEE.md](COMPILATION_GUARANTEE.md) | What `--compile-check` guarantees: three tiers, measured false-READY rate, what is proved |
| [v27/adr/](v27/adr/) | Current architecture decisions (ADR-010 … ADR-015) |
| [ARCH.md](ARCH.md) | Architecture handbook — 5-layer pipeline, Elder runtime |
| [PROOFS.md](PROOFS.md) | Coq proof infrastructure overview |
| [PROOF_GUIDE.md](PROOF_GUIDE.md) | Proof-writers guide |
| [PROOF_CLASSES.md](PROOF_CLASSES.md) | Proof taxonomy (faithful / conservative / conditional / statistical) |
| [SUPPORT_MATRIX.md](SUPPORT_MATRIX.md) | Engine/package/interface support (wrapper over `docs/SUPPORT_MATRIX.yaml`) |
| [COMPILATION_GUARANTEE_STACK.md](COMPILATION_GUARANTEE_STACK.md) | v27 compile-guarantee theorem stack (T0-T7); predates ADR-012 — the stack is proved over an abstract model, see COMPILATION_GUARANTEE.md for what it means for a real document |
| [BUILD_LOG_CONTRACT.md](BUILD_LOG_CONTRACT.md) | Class C compile-log contract (LAY-001..027) |
| [REST_API.md](REST_API.md) | REST endpoint reference (`/expand`, `/tokens`, profile env) |
| [VALIDATORS_RUNTIME.md](VALIDATORS_RUNTIME.md) | L0-L2 validator runtime, layer gating, token debugging |
| [BUILD_SYSTEM_GUIDE.md](BUILD_SYSTEM_GUIDE.md) | Build commands, environment setup |
| [UNIT_TESTS.md](UNIT_TESTS.md) | Test infrastructure |
| [TOKEN_AWARE_VALIDATORS.md](TOKEN_AWARE_VALIDATORS.md) | Token-aware validation design |
| [CI_STATUS_CHECKS.md](CI_STATUS_CHECKS.md) | Required CI checks and branch protection config |
| [NOTIFICATIONS.md](NOTIFICATIONS.md) | CI notification setup |
| [TEST_COVERAGE_MATRIX.md](TEST_COVERAGE_MATRIX.md) | Per-rule test coverage tracking |

## Subdirectories

| Directory | Contents |
|-----------|----------|
| `archive/` | Historical reports, audits, and obsolete v25-era planning docs (incl. the SIMD-v2-era handoff/debug docs and v26.x migration guides) |
| `appendices/` | Glossary, layer interfaces, validator DSL, proof template catalogue |

## See also

- Project overview: [../README.md](../README.md)
- Root architecture: [../ARCHITECTURE.md](../ARCHITECTURE.md)
- Specs: [../specs/](../specs/) (v26 master, language contract, rule contracts, support matrix)
- Architecture memo: [../specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md](../specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md)
- ML subsystem: [../ml/ARCHITECTURE.md](../ml/ARCHITECTURE.md)
