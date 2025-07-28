#!/bin/bash
# Simple build script for OCaml validator without Coq

set -e

echo "Building LaTeX Validator v24 OCaml components..."

cd src/ocaml/lib

# Compile core modules
echo "Compiling vsna_core..."
ocamlopt -I +unix -c vsna_core.ml

# Skip phase1_dfa for now - it has extraction issues
# echo "Compiling phase1_dfa..."
# ocamlopt -I +unix -c phase1_dfa.ml

echo "Compiling latex_validator..."
ocamlopt -I +unix -c latex_validator.ml

# Build main executable
echo "Building latex_validator executable..."
ocamlopt -I +unix unix.cmxa vsna_core.cmx latex_validator.cmx -o ../../../build/latex_validator_new

echo "Build finished! Executable at build/latex_validator_new"