# Appendix K — Reproducibility Cookbook & Tool-chain Pins

Per v25 master plan §15, Table K (7 pages). Bit-for-bit determinism across
opam (primary), Nix (hermetic CI, future), and Docker; complete
chain-of-custody for compilers, libraries, and containers.

---

## K-1 Pin Table (Single Source of Truth)

| Layer | Package / Binary | Exact Version | Pin Type | Verification |
|-------|-----------------|---------------|----------|-------------|
| Compiler | `ocaml-base-compiler` | 5.1.1 | opam pin | `ocaml -version` |
| Compiler | `coq` | 8.18.0 | opam pin | `coqc --version` |
| Compiler | `coq-core` | 8.18.0 | transitive | — |
| Build tools | `dune` | >= 3.10 | opam | `dune --version` |
| Build tools | `dune-coq` | 0.8 | `(using coq 0.8)` | `dune-project` |
| OCaml libs | `yojson` | >= 2.1 | opam | — |
| OCaml libs | `uutf` | >= 1.0.3 | opam | — |
| OCaml libs | `str` | stdlib | built-in | — |
| Formatter | `ocamlformat` | 0.26.2 | `.ocamlformat` | `ocamlformat --version` |
| Rust | `rust-toolchain` | stable (>= 1.75) | `rust-toolchain` file | `rustc --version` |
| Docker | build env image | tag 2025-07-31 | OCI | `docker inspect` |
| Nix | nixpkgs | (future) | flake input | — |

**Update workflow:** PR adjusts a single row → `make pin-update` regenerates
lock-files → CI checks rebuild determinism → PR auto-labels `pin-bump`.

---

## K-2 Canonical Build Recipes

### Opam (macOS >= 12; Linux x86-64/arm64)

```bash
git clone https://github.com/ClanClanClanClan/latex_perf.git
cd latex_perf
opam switch create . 5.1.1
eval $(opam env)
opam install coq.8.18.0 coq-core.8.18.0 yojson uutf
dune build                          # OCaml only, < 30 s
dune build proofs                   # Coq proofs, ~ 9 min (M2 Pro)
dune runtest                        # all tests
```

### Docker

```bash
# Build from repo root
docker build -t latex-perf-v25 .
docker run --rm -v "$PWD":/work -w /work latex-perf-v25 \
  bash -lc "dune build && dune runtest"
```

### Nix (Future — Planned W151-155)

```bash
# Not yet available; opam provides sufficient reproducibility for v25 development
nix build .#ci --no-write-lock-file
```

A `flake.nix` for fully reproducible builds is planned for the release
engineering phase.

---

## K-3 Build Verification

```bash
# Full build (OCaml + Coq proofs)
dune build @all

# Verify zero admits
grep -rn "Admitted\.\|admit\." proofs/ proofs/generated/ --include="*.v"
# Expected: no output

# Verify zero axioms
grep -rn "^Axiom\|^Parameter" proofs/ --include="*.v" | grep -v archive
# Expected: no output

# Run all tests
dune runtest --force

# Performance gate
bash scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 50
```

---

## K-4 Checksum Manifest

`checksums/artefact_manifest.tsv` (regenerated per release):

```
<sha256>\t<bytes>\t<path>
```

Mandatory artefacts:
- CLI binary
- All `proofs/**/*.vo` files (23 core + 74 generated)
- `docs/v25_master.pdf` (if generated)
- `bench/latest/latency.csv`

CI step `Art-Hash` recomputes and fails on drift without version bump +
changelog entry.

---

## K-5 Version Checksum Table

| Artefact | Version | Verification Command |
|----------|---------|---------------------|
| OCaml compiler | 5.1.1 | `ocaml -version` |
| Coq | 8.18.0 | `coqc --version` |
| dune | >= 3.10 | `dune --version` |
| rules_v3.yaml | 623 rules | `grep "^- id:" specs/rules/rules_v3.yaml \| wc -l` |
| macro_catalogue (symbols) | 441 entries | `python3 -c "import json; ..."` |
| macro_catalogue (argsafe) | 79 entries | `python3 -c "import json; ..."` |
| Proof theorems | 429+ | `grep -r "Theorem\|Lemma" proofs/ \| wc -l` |

---

## K-6 Corpus Reproducibility

External corpora managed via `corpora.lock`:

```bash
make fetch-corpora       # download + verify SHA256
make fetch-corpora-dry   # show what would be downloaded
```

Lock file format:
```yaml
- name: "arxiv-sample-2024"
  url: "https://..."
  sha256: "abc123..."
  size_bytes: 52428800
  format: "tar.gz"
  target_dir: "external_corpora/arxiv"
```

---

## K-7 CI Reproducibility

All GitHub Actions use pinned versions:
- `actions/checkout@v4`
- `actions/cache@v4`
- `actions/upload-artifact@v4`
- `dawidd6/action-send-mail@v4`
- `peaceiris/actions-gh-pages@v4`

Hardware baseline recorded in `core/l0_lexer/current_baseline_performance.json`.

Concurrency control prevents stale results:
```yaml
concurrency:
  group: ci-${{ github.head_ref || github.run_id }}
  cancel-in-progress: true
```

---

## K-8 Offline / Network-Free Builds

**Status:** Planned for GA release. Currently requires network for opam
package resolution.

When available:
1. Download offline bundle from release assets
2. Extract: contains repo checkout + opam download cache
3. Run `./offline_build.sh` (sets `OPAMROOT=./_offline_opam`, forces `--offline`)
4. Hashes must match `checksums/artefact_manifest.tsv`

---

## K-9 FAQ

| Question | Answer |
|----------|--------|
| Minor version bumps? | Only via PR editing K-1 + regenerated locks |
| ARM vs x86 digests? | `.vo` and `.cmx` are arch-independent; binaries differ |
| Pin a fork? | Use `opam pin add pkg git+https://...#commit=...` |
| Why SHA-256? | Sufficient strength and broad tooling support |
| Bypass locally? | `export LP_ALLOW_HASH_DRIFT=1` (never in CI) |
| Why not Nix yet? | opam switch + dune provides sufficient determinism for v25 dev |

---

## K-10 Change-log

- 2026-04-06 — Expanded with pin table, build recipes, checksum manifest,
  offline builds, FAQ (PR #194)
- 2026-04-05 — Initial revision with environment setup and verification
