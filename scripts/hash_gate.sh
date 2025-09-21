#!/usr/bin/env bash
set -euo pipefail

# Optional hash throughput gate. Defaults to INFO mode.
# Set ENABLE_HASH_GATE=1 to enforce a minimum MB/s threshold.

FILE=${1:-"corpora/perf/perf_smoke_big.tex"}
ITERS=${2:-50}
CSV=${3:-/tmp/hash_throughput.csv}
THRESH_MBPS=${THRESH_MBPS:-500.0}

echo "[hash-gate] measuring hash throughput on $FILE (iters=$ITERS)"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  ./_build/default/latex-parse/bench/hash_throughput.exe "$FILE" "$ITERS" --csv "$CSV"

MBPS=$(awk -F, 'NR==2{print $2}' "$CSV" 2>/dev/null || echo "0")
echo "[hash-gate] fnv64 throughput = ${MBPS} MB/s"

if [[ "${ENABLE_HASH_GATE:-0}" == "1" ]]; then
  awk -v v="$MBPS" -v t="$THRESH_MBPS" 'BEGIN{ if (v+0 < t+0) exit 1; else exit 0 }' || {
    echo "[hash-gate] FAIL: throughput ${MBPS} < ${THRESH_MBPS} MB/s"; exit 1; }
  echo "[hash-gate] PASS: throughput ${MBPS} ≥ ${THRESH_MBPS} MB/s"
else
  echo "[hash-gate] INFO: not enforcing threshold (set ENABLE_HASH_GATE=1 to enforce)"
fi

# Optional SIMD xxh64 gate
if grep -q '^xxh64,' "$CSV" 2>/dev/null; then
  MBPS_XXH=$(awk -F, '$1=="xxh64"{print $2}' "$CSV" | tail -1)
  echo "[hash-gate] xxh64 throughput = ${MBPS_XXH} MB/s (L0_USE_SIMD_XXH may enable SIMD)"
  if [[ "${ENABLE_HASH_GATE_XXH:-0}" == "1" ]]; then
    THRESH_MBPS_XXH=${THRESH_MBPS_XXH:-1000.0}
    awk -v v="$MBPS_XXH" -v t="$THRESH_MBPS_XXH" 'BEGIN{ if (v+0 < t+0) exit 1; else exit 0 }' || {
      echo "[hash-gate] FAIL: xxh64 throughput ${MBPS_XXH} < ${THRESH_MBPS_XXH} MB/s"; exit 1; }
    echo "[hash-gate] PASS: xxh64 throughput ${MBPS_XXH} ≥ ${THRESH_MBPS_XXH} MB/s"
  fi
fi
