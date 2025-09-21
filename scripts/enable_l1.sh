#!/usr/bin/env bash
set -euo pipefail

# Helper to enable L1 expander build locally by swapping dune.disabled → dune
DIR="core/l1_expander"

if [[ -f "$DIR/dune" ]]; then
  echo "[l1] Already enabled: $DIR/dune present"
  exit 0
fi

if [[ -f "$DIR/dune.disabled" ]]; then
  cp "$DIR/dune.disabled" "$DIR/dune"
  echo "[l1] Enabled L1 dune in $DIR. Run: opam exec -- dune build $DIR"
else
  echo "[l1] No dune.disabled found; nothing to enable"
fi

