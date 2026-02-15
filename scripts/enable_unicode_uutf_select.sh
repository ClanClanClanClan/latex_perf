#!/usr/bin/env bash
set -euo pipefail

# No-op: Unicode support now defaults to Uutf with a single
# unicode.ml implementation (no fallback). This script is kept
# for backward compatibility and will simply print a notice.

echo "[unicode-select] uutf-based unicode.ml is now default; no action needed."
echo "[unicode-select] Build as usual: opam exec -- dune build"
