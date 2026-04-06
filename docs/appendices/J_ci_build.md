# Appendix J — Continuous Integration & Build Infrastructure

Per v25 master plan §15, Table J (14 pages).

---

## J-0 Policy Gate

Block merge unless all:
1. OCaml + Rust compile warnings-as-errors
2. Coq proofs 0 admits, 0 axioms (`coqchk`)
3. Unit, property, and golden-file tests green
4. Performance regression delta < +5% vs baseline
5. Format check passes (`dune fmt`)

---

## J-1 Build System

| Component | Technology | Config File |
|-----------|-----------|-------------|
| OCaml build | Dune 3.10 | `dune-project`, `latex-parse/src/dune` |
| Coq proofs | Dune coq.theory | `proofs/dune`, `proofs/generated/dune` |
| Rust proxy | Cargo (workspace) | `rust/Cargo.toml` |
| Python ML | pip/venv | `ml/requirements.txt` |
| Documentation | MkDocs | `mkdocs.yml` |
| Top-level | Make (193 lines) | `Makefile` |

### Build Recipes

```bash
# Full build (OCaml + Coq)
opam exec -- dune build @all

# OCaml only (fast, no Coq)
opam exec -- dune build

# Run all tests
opam exec -- dune runtest

# Format check
opam exec -- dune fmt

# Build proofs only
opam exec -- dune build proofs

# Rust proxy
cd rust-proxy && cargo build --release

# Performance gates
make gates-all
```

### Makefile Targets

| Target | Purpose |
|--------|---------|
| `build` | `dune build` with parallelism |
| `verify` | Self-tests, IPC propcheck, A+B microbench |
| `ci` | 100K keepalive run with performance gates |
| `soak` | 1-hour stress test |
| `proxy` | Cargo build for `elderd_rust_proxy` |
| `rest-run` / `rest-stop` | REST API server on port 8080 |
| `fault-test` | Fault injection testing |
| `gates-all` | Run all performance gates |
| `hash-bench` / `hash-bench-avx2` / `hash-bench-neon` | Hash throughput measurement |

---

## J-2 Complete Workflow Inventory (29 workflows)

| # | Workflow File | Name | Trigger | Purpose |
|---|--------------|------|---------|---------|
| 1 | `ci.yml` | CI | push, PR | Format checks, OCaml compilation, unit tests |
| 2 | `proof.yml` | Proof CI (Coq) | push, PR | Parallel Coq compilation, zero-admit audit |
| 3 | `unit-tests.yml` | Unit Tests | push, PR | All `dune runtest` suites |
| 4 | `unit-tests-badge.yml` | Unit Tests Badge | push main | Badge generation for README |
| 5 | `perf-ci.yml` | Performance Gate CI | push, PR | p95 latency gates (full-doc, edit-window) |
| 6 | `perf-nightly.yml` | Nightly Performance | schedule | Median-of-100 benchmark with baseline comparison |
| 7 | `performance-gate.yml` | Performance Gate - Week 5 | push, PR | p95 < 20ms Tier A gate |
| 8 | `latency-nightly.yml` | Latency Smoke Nightly | schedule | `/expand` endpoint latency |
| 9 | `l1-smoke.yml` | L1 Rules Smoke | push, PR | L1 macro expansion smoke test |
| 10 | `l1-ab.yml` | L1 Expander A/B | manual | A/B comparison of expander variants |
| 11 | `l1-nightly.yml` | L1 Nightly Smoke | schedule | Extended L1 test suite |
| 12 | `unicode-smoke.yml` | Unicode Rules Smoke | push, PR | Unicode handling correctness |
| 13 | `rest-smoke.yml` | REST Smoke Test | push, PR | REST API endpoint validation |
| 14 | `rest-schema.yml` | REST Schema Validation | push, PR | OpenAPI schema compliance |
| 15 | `rust-proxy-smoke.yml` | Rust Proxy Smoke | push, PR | Rust proxy build + smoke test |
| 16 | `rust-proxy-verify.yml` | Rust Proxy Verify | push, PR | Extended Rust proxy evidence tests |
| 17 | `xxh-selfcheck.yml` | XXH64 SIMD Selfcheck | push, PR | OCaml/Rust xxHash parity check |
| 18 | `xxh-throughput-gate.yml` | XXH64 Throughput Gate | push, PR | SIMD hash throughput gate |
| 19 | `xxh-throughput-scheduled.yml` | SIMD Throughput Gate | schedule | Scheduled SIMD benchmark |
| 20 | `validators-pilot-smoke.yml` | Validators Pilot Smoke | push, PR | Pilot validator set smoke test |
| 21 | `validators-pilot-smoke-cli.yml` | Validators Pilot Smoke (CLI) | push, PR | CLI-mode validator smoke test |
| 22 | `catalogue-compliance.yml` | Catalogue Compliance | push, PR | Macro catalogue schema validation |
| 23 | `catalogue-deep.yml` | Catalogue Deep Validation | push, PR | Deep catalogue consistency checks |
| 24 | `expander-smoke.yml` | Expander Smoke | push, PR | Basic expander functionality |
| 25 | `messages-validate.yml` | Messages Validation | push, PR | Diagnostic message format validation |
| 26 | `prometheus-smoke.yml` | Prometheus Smoke Test | push, PR | Prometheus metrics endpoint check |
| 27 | `branch-protection.yml` | Configure Branch Protection | manual | GitHub API branch protection setup |
| 28 | `latex-perfectionist.yml` | LaTeX Perfectionist | push, PR | Python 3.9-3.12 matrix testing |
| 29 | `week1-validation.yml` | Week 1 Validation Pipeline | push main | Bootstrap validation checks |

### Required Status Checks (branch protection)

These 8 checks must pass before merge to main:

| Check ID | Workflow | What it verifies |
|----------|---------|-----------------|
| `proof-ci` | proof.yml | Zero admits, zero axioms, all `.vo` compile |
| `unicode-smoke` | unicode-smoke.yml | Unicode handling correctness |
| `l1-smoke` | l1-smoke.yml | L1 macro expansion smoke test |
| `smoke-cli` | validators-pilot-smoke-cli.yml | CLI validator smoke test |
| `rest-smoke` | rest-smoke.yml | REST API smoke test |
| `perf-ci` | perf-ci.yml | p95 < 20ms full-doc, p95 < 1.2ms edit-window |
| `xxh-selfcheck` | xxh-selfcheck.yml | xxHash OCaml/Rust parity |
| `unit-tests` | unit-tests.yml | All `dune runtest` suites pass |

---

## J-3 Build System Layers

| Layer | Alias | Contents | Use |
|-------|-------|----------|-----|
| `@unit` | OCaml/Rust unit tests | Inner development loop |
| `@coq` | All `.v` + extracted `.ml` glue | Proof gate |
| `@perf` | Bench harness + CSV | Perf tuning |
| `@all` | Union (default in CI) | Release build |

---

## J-4 Performance Gates

| Gate | Threshold | Workflow | Measured (2026-04-05) |
|------|-----------|---------|----------------------|
| Full-doc p95 | < 20 ms (1.1 MB corpus) | perf-ci.yml | 3.25 ms |
| Edit-window p95 | < 1.2 ms (4 KB) | perf-ci.yml | 0.075 ms |
| First-token p95 | < 350 µs | perf-ci.yml | 27 µs |
| SIMD Tier B | < 8 ms (informational) | perf-ci.yml | N/A (scalar only) |

Performance regression delta > +5% vs baseline → fails the gate.

Nightly `perf-nightly.yml` records median-of-100 runs and compares against
stored baseline. On 3 consecutive nights of > 5% improvement, baseline
auto-refreshes.

---

## J-5 Proof CI Details

```yaml
# .github/workflows/proof.yml (key configuration)
- name: Compile Coq proofs
  run: dune build proofs
  timeout-minutes: 30

- name: Admit audit
  run: |
    ! grep -rn "Admitted\|admit" proofs/ --include="*.v" | grep -v ".disabled"

- name: Axiom audit
  run: |
    ! grep -rn "^Axiom\|^Parameter" proofs/ --include="*.v" | grep -v "archive"
```

- Parallel compilation with `-j 4`
- Timing instrumentation per `.v` file
- 30-minute timeout per job
- Zero-admit policy: hard gate on main
- Zero-axiom policy: hard gate on main

---

## J-6 Caches and Artefacts

| Cache Key | Contents | Scope |
|-----------|----------|-------|
| `sha256(dune.lock)` | opam switch, OCaml compiler | Per-OS |
| `sha256(proofs/**/*.v)` | Coq `.vo` object files | Per-branch |
| `sha256(rules_v3.yaml)` | Generated proof stubs | Per-branch |

Proof deltas uploaded as `proof-delta-$SHA.zip` artefacts.

---

## J-7 Security and SBOM

- **Vulnerability scanning:** Trivy on OS + libs; fail if High with available fix
- **Release signing:** cosign with GitHub OIDC; pushed to `ghcr.io/latex-perf/...`
- **SBOM:** CycloneDX JSON generated by `syft`; attached to Releases
- **Sandboxing:** seccomp profile at `scripts/sandbox/seccomp.json`

---

## J-8 Developer Experience

- **Pre-commit:** ocamlformat, `dune build @unit --profile=dev`, quick-proof
  subset (`scripts/pre_commit_proof_subset.sh` ≤ 60 s)
- **VS Code:** `.vscode/settings.json` configures coq-lsp and OCaml-LSP
- **dune watch:** Auto-rebuild on file changes

---

## J-9 Reproducible Release (`scripts/release.sh`)

```bash
1. git clean -xfd
2. dune build -p latex_perfectionist --profile=release
3. coqchk -silent $(find _build/default/proofs -name '*.vo')
4. ./scripts/bench.py --assert-budget 42ms
5. syft packages dir:. -o spdx-json > sbom.json
6. cosign sign --key env://COSIGN_KEY release.tar.gz
7. Create Release draft with artefacts
```

---

## J-10 Toolchain Pins

| Tool | Version | Pin Type | Source |
|------|---------|----------|--------|
| OCaml | >= 5.1.1 | `dune-project` depends | opam |
| Coq | = 8.18.0 | Pinned exact | opam |
| coq-core | = 8.18.0 | Pinned exact | opam |
| Dune | >= 3.10 | Minimum | opam |
| yojson | >= 2.1 | Minimum | opam |
| uutf | >= 1.0.3 | Minimum | opam |
| Rust | stable (1.75+) | `rust-toolchain` file | rustup |
| ocamlformat | 0.26.2 | `.ocamlformat` | opam |

---

## J-11 Test Infrastructure

| Category | Count | Framework |
|----------|-------|-----------|
| Unit test suites | 58+ | Hand-rolled exit-code based |
| Golden corpus cases | 329 | YAML format (expect/forbid/expect_msgs) |
| Property-based trials | 4 × 1000 | Seed=12345 |
| IPC roundtrip checks | 100K | Seed=42 |
| Parser corpus files | 306 | Success rate measurement |

Test helpers (`test_helpers.ml`): `fires`, `does_not_fire`, `fires_with_count`,
`expect`, `run`, `finalise`.

---

## J-12 Future CI Roadmap

| Feature | Target | Note |
|---------|--------|------|
| Self-hosted ARM64 runners | v26 | Parity with Apple Silicon |
| Coq 8.20 hierarchical proofs | When stable | ~25% faster proof jobs |
| Incremental rule sharding | v26 | Skip untouched proofs |
| Remote proof cache | v26 | Shared `.vo` objects across PRs |
