#!/usr/bin/env bash
set -euo pipefail

# Run both performance gates (full-doc median-of-100 and edit-window 4KB)
# and print a concise summary. Assumes project built.

FULL=${1:-corpora/perf/perf_smoke_big.tex}
EDIT=${2:-corpora/perf/edit_window_4kb.tex}
ITERS=${3:-100}

echo "[gates] full-doc median-of-100 @ ITERS=$ITERS on $FULL"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  bash scripts/perf_gate.sh "$FULL" "$ITERS"

echo "[gates] edit-window 4KB on $EDIT"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  bash scripts/edit_window_gate.sh "$EDIT" 2000

echo "[gates] complete"

