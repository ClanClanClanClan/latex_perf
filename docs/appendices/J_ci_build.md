# Appendix J — Continuous Integration & Build Infrastructure

Per v25 master plan §15, Table J (14 pages).

## Build System

| Component | Technology | Config File |
|-----------|-----------|-------------|
| OCaml build | Dune 3.10 | `dune-project`, `latex-parse/src/dune` |
| Coq proofs | Dune coq.theory | `proofs/dune`, `proofs/generated/dune` |
| Rust proxy | Cargo | `rust/Cargo.toml` |
| Python ML | pip/venv | `ml/requirements.txt` |
| Documentation | MkDocs | `mkdocs.yml` |

### Quick Commands

```bash
# Build everything (OCaml + Coq)
opam exec -- dune build @all

# Build OCaml only (fast, no Coq)
opam exec -- dune build

# Run all tests
opam exec -- dune runtest

# Format code
opam exec -- dune fmt --auto-promote

# Build proofs only
opam exec -- dune build proofs
```

## CI Workflows (30 total)

### Required Status Checks (branch protection)

| Check | Workflow | What it verifies |
|-------|---------|-----------------|
| `proof-ci` | proof.yml | Zero admits, zero axioms, all .vo compile |
| `unicode-smoke` | unicode-smoke.yml | Unicode handling correctness |
| `l1-smoke` | l1-smoke.yml | L1 macro expansion smoke test |
| `smoke-cli` | validators-pilot-smoke-cli.yml | CLI validator smoke test |
| `rest-smoke` | rest-smoke.yml | REST API smoke test |
| `perf-ci` | perf-ci.yml | p95 < 20ms full-doc, p95 < 1.2ms edit-window |
| `xxh-selfcheck` | xxh-selfcheck.yml | xxHash implementation correctness |
| `unit-tests` | unit-tests.yml | All dune test suites pass |

### Performance Gates

| Gate | Threshold | Workflow |
|------|-----------|---------|
| Full-doc p95 | < 20 ms (1.1 MB corpus) | perf-ci.yml |
| Edit-window p95 | < 1.2 ms (4 KB) | perf-ci.yml |
| First-token p95 | < 350 µs | perf-ci.yml |
| SIMD (Tier B) | < 8 ms (informational) | perf-ci.yml |

### Proof CI

- Parallel compilation with `-j 4`
- Zero-admit policy enforced via grep
- Zero-axiom policy enforced via grep
- Timing instrumentation per .v file
- Failure → opens GitHub issue with `proof-regression` label
- Notification via Slack webhook (if configured)

## Toolchain Pins

| Tool | Version | Pin Type |
|------|---------|----------|
| OCaml | >= 5.1.1 | `dune-project` depends |
| Coq | = 8.18.0 | Pinned exact |
| coq-core | = 8.18.0 | Pinned exact |
| Dune | >= 3.10 | Minimum |
| yojson | >= 2.1 | Minimum |
| uutf | >= 1.0.3 | Minimum |

## Test Infrastructure

- 58+ test suites in `latex-parse/src/dune`
- Test helpers: `test_helpers.ml` (fires, does_not_fire, fires_with_count, expect)
- Golden corpus: 329 cases across 12 YAML suites
- Property-based: tokenizer, parser (1000 trials each, seed=12345)
- IPC roundtrip: 100K checks (seed=42)
