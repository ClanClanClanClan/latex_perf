# Appendix K — Reproducibility Cookbook & Tool-chain Pins

Per v25 master plan §15, Table K (7 pages).

## Environment Setup

### Prerequisites

```bash
# OCaml via opam
opam switch create l0-testing 5.1.1
eval $(opam env --switch=l0-testing)

# Coq
opam install coq.8.18.0 coq-core.8.18.0

# OCaml deps
opam install yojson uutf str unix threads

# Rust (for proxy)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### Build Verification

```bash
# Full build (OCaml + Coq proofs)
OPAMSWITCH=l0-testing opam exec -- dune build @all

# Verify zero admits
grep -rE 'Admitted\.|admit\.' proofs/ proofs/generated/
# Expected: no output

# Run all tests
OPAMSWITCH=l0-testing opam exec -- dune runtest --force

# Performance gate
OPAMSWITCH=l0-testing opam exec -- bash scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 50
```

## Version Checksum Table

| Artifact | Version | SHA256 (first 16 chars) |
|----------|---------|------------------------|
| OCaml compiler | 5.1.1 | Verify via `ocaml -version` |
| Coq | 8.18.0 | Verify via `coqc --version` |
| dune | >= 3.10 | Verify via `dune --version` |
| rules_v3.yaml | 623 rules | Verify via `wc -l specs/rules/rules_v3.yaml` |
| macro_catalogue.v25r2.json | 441 entries | Verify via `python3 -c "import json; print(len(json.load(open('...'))))"` |

## Corpus Reproducibility

External corpora managed via `corpora.lock`:
```bash
make fetch-corpora       # download + verify SHA256
make fetch-corpora-dry   # show what would be downloaded
```

## CI Reproducibility

All GitHub Actions use pinned versions (v4+):
- `actions/checkout@v4`
- `actions/cache@v4`
- `actions/upload-artifact@v4`

Hardware baseline recorded in `core/l0_lexer/current_baseline_performance.json`.

## Nix Flake (Future)

A `flake.nix` for fully reproducible builds is planned for the release engineering phase (W151-155). Currently, opam switch + dune provides sufficient reproducibility for development.
