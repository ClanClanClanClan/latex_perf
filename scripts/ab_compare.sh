#!/usr/bin/env bash
set -euo pipefail

FILE=${1:-"corpora/perf/perf_smoke_big.tex"}
ITERS=${2:-10000}

# Direct microbench
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  "$FILE" "$ITERS" --csv /tmp/ab_direct.csv

# Service microbench (keepalive path)
OPAMSWITCH=l0-testing opam exec -- make service-run
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/run_service_bench_keepalive.exe \
  "$FILE" 10000 4 --out /tmp/latencies_ms.txt || true
OPAMSWITCH=l0-testing opam exec -- make service-stop

# Summarize
echo "=== A/B Compare Summary ==="
echo "[A] Direct ab_microbench CSV: /tmp/ab_direct.csv"
if [[ -f /tmp/latencies_ms.txt ]]; then
  echo "[B] Service keepalive percentiles:"
  ./verify_percentiles /tmp/latencies_ms.txt | sed -n '1,12p'
else
  echo "[B] Service run not available; see logs above"
fi
