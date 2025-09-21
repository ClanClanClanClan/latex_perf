#!/usr/bin/env bash
set -euo pipefail

echo "[l1] Expander A/B compare helper"

if [[ ! -f core/l1_expander/dune ]]; then
  echo "[l1] L1 expander not enabled. Enable it locally with:"
  echo "      OPAMSWITCH=l0-testing opam exec -- bash scripts/enable_l1.sh"
  exit 2
fi

echo "[l1] Building L1 expander library..."
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build core/l1_expander

echo "[l1] Built L1 library. No standalone L1 executable is defined in dune."
echo "[l1] To A/B compare, plug the L1 library into a small test driver or use an existing pipeline test."
echo "[l1] (Intentionally non-invasive to keep mainline gates intact.)"

