#!/usr/bin/env bash
set -euo pipefail

echo "[env] Creating and syncing opam switch l0-testing (OCaml 5.1.1)"
opam switch list --short | grep -qx "l0-testing" || opam switch create l0-testing 5.1.1
opam repo add coq-released https://coq.inria.fr/opam/released || true
opam update -y

echo "[env] Installing toolchain and deps (Coq 8.18.0, dune 3.10, libs)"
opam install -y coq.8.18.0 coq-core.8.18.0 dune.3.10 yojson angstrom ppx_deriving uutf

eval "$(opam env --switch=l0-testing)"
echo "[env] Active switch: $(opam switch show)"
echo "[env] ocamlc: $(ocamlc -version) | dune: $(dune --version)"

echo "[env] Rebuilding project"
opam exec -- dune build @all
opam exec -- dune build @coq
opam exec -- dune runtest || true

echo "[env] If you encounter 'yojson.cmi … older OCaml', you can run:"
echo "       opam reinstall -y yojson dune"
echo "       # Or pin deps from lock: opam install -y . --deps-only"

