# Documentation Index

## Current (actively maintained)

| File | Purpose |
|------|---------|
| [ARCH.md](ARCH.md) | Architecture handbook — 5-layer pipeline, Elder runtime |
| [PROOFS.md](PROOFS.md) | Coq proof infrastructure overview |
| [PROOF_GUIDE.md](PROOF_GUIDE.md) | Proof-writers guide |
| [PROOF_CLASSES.md](PROOF_CLASSES.md) | Proof taxonomy (faithful / conservative / conditional / statistical) |
| [SUPPORT_MATRIX.md](SUPPORT_MATRIX.md) | Engine/package/interface support (wrapper over `specs/v26/support_matrix.yaml`) |
| [COMPILATION_GUARANTEE_STACK.md](COMPILATION_GUARANTEE_STACK.md) | v27 compile-guarantee theorem stack (T0-T7) |
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
| `archive/` | Historical reports, audits, and obsolete v25-era planning docs |
| `expert/` | Technical handoff knowledge for Coq proofs |
| `handoff/` | Project continuity and context transfer docs |
| `appendices/` | Glossary, layer interfaces, validator DSL, proof template catalogue |

## See also

- Project overview: [../README.md](../README.md)
- Root architecture: [../ARCHITECTURE.md](../ARCHITECTURE.md)
- Specs: [../specs/](../specs/) (v26 master, language contract, rule contracts, support matrix)
- Architecture memo: [../specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md](../specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md)
- ML subsystem: [../ml/ARCHITECTURE.md](../ml/ARCHITECTURE.md)
