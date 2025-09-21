#!/usr/bin/env bash
set -euo pipefail

# Produce a local perf summary CSV by running ab_microbench (10K) and
# edit_window_bench (5K) and merging results.

FILE=${1:-corpora/perf/perf_smoke_big.tex}
AB_CSV=/tmp/ab_microbench_10k.csv
EDIT_CSV=/tmp/edit_window_bench_5k.csv
OUT=${2:-/tmp/perf_summary.csv}

echo "[perf-summary] running ab_microbench 10k on $FILE"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  "$FILE" 10000 --csv "$AB_CSV"

echo "[perf-summary] running edit_window_bench 5k"
OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- \
  ./_build/default/latex-parse/bench/edit_window_bench.exe \
  corpora/perf/edit_window_4kb.tex 5000 --csv "$EDIT_CSV" --window 4096

bash scripts/merge_perf_csv.sh "$OUT" \
  ab10k "$AB_CSV" \
  edit4k5k "$EDIT_CSV"

echo "[perf-summary] wrote $OUT"

