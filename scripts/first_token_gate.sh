#!/usr/bin/env bash
set -euo pipefail

FILE=${1:-"corpora/perf/edit_window_4kb.tex"}
ITERS=${2:-2000}
WIN=${3:-4096}
BIN="_build/default/latex-parse/bench/first_token_latency.exe"

echo "[ft-gate] running first-token latency: $ITERS iters, window=$WIN on $FILE"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  $BIN "$FILE" "$ITERS" --window "$WIN" --csv /tmp/first_token_latency.csv

# CSV columns: label,min_us,p50_us,p95_us,p99_us,p999_us,max_us
P95=$(awk -F, 'NR==2{print $4}' /tmp/first_token_latency.csv)
awk -v p95="$P95" 'BEGIN{ if (p95 <= 350.0) exit 0; else exit 1 }' || {
  echo "[ft-gate] FAIL: p95=${P95} us > 350 us"; exit 1; }

echo "[ft-gate] PASS: p95=${P95} us ≤ 350 us"

