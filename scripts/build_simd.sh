#!/usr/bin/env bash
set -euo pipefail

# Auto-detect CPU and build with the appropriate SIMD profile.
# - x86_64 → simd-avx2
# - arm64/aarch64 → simd-neon
# Fallback to default profile if unrecognized.

arch=$(uname -m | tr '[:upper:]' '[:lower:]')
profile=""
case "$arch" in
  x86_64|amd64)
    profile="simd-avx2" ;;
  arm64|aarch64)
    profile="simd-neon" ;;
esac

if [[ -n "$profile" ]]; then
  echo "[simd] Detected $arch → --profile=$profile"
  OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build --profile=$profile @all
else
  echo "[simd] Unknown arch ($arch); building default profile"
  OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build @all
fi

