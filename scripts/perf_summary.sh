#!/usr/bin/env bash
set -euo pipefail

# Produce a local perf summary CSV by running ab_microbench (10K) and
# edit_window_bench (5K) and merging results.
#
# OPAMSWITCH handling: respect the caller's OPAMSWITCH if explicitly set
# (e.g. local development with a `l0-testing` switch), otherwise fall
# through to the ambient opam switch (CI runners use a switch named
# after the OCaml version, NOT `l0-testing`).  Hardcoding `l0-testing`
# as a default broke perf-nightly on GitHub Actions because that switch
# does not exist there — see commit message for context.

FILE=${1:-corpora/perf/perf_smoke_big.tex}
AB_CSV=/tmp/ab_microbench_10k.csv
EDIT_CSV=/tmp/edit_window_bench_5k.csv
OUT=${2:-/tmp/perf_summary.csv}

echo "[perf-summary] running ab_microbench 10k on $FILE"
opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  "$FILE" 10000 --csv "$AB_CSV"

echo "[perf-summary] running edit_window_bench 5k"
opam exec -- \
  ./_build/default/latex-parse/bench/edit_window_bench.exe \
  corpora/perf/edit_window_4kb.tex 5000 --csv "$EDIT_CSV" --window 4096

bash scripts/merge_perf_csv.sh "$OUT" \
  ab10k "$AB_CSV" \
  edit4k5k "$EDIT_CSV"

echo "[perf-summary] wrote $OUT"

