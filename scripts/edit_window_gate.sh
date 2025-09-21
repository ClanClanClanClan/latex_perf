#!/usr/bin/env bash
set -euo pipefail

FILE=${1:-"corpora/perf/edit_window_4kb.tex"}
ITERS=${2:-2000}
BIN="_build/default/latex-parse/bench/edit_window_bench.exe"

echo "[edit-gate] running ${ITERS} iterations on ${FILE}"
$BIN "$FILE" "$ITERS" --warmup 256 --csv /tmp/edit_window_bench.csv --window 4096

# CSV: label,min_ms,p50_ms,p95_ms,p99_ms,p999_ms,max_ms
P95=$(awk -F, 'NR==2 {print $4}' /tmp/edit_window_bench.csv)
if [[ -z "$P95" ]]; then
  echo "[edit-gate] ERROR: unable to read p95 from CSV"
  exit 1
fi

awk -v p95="$P95" 'BEGIN{ if (p95 <= 1.2) exit 0; else exit 1 }' || {
  echo "[edit-gate] FAIL: p95=${P95} ms > 1.2 ms target"
  exit 1
}

echo "[edit-gate] PASS: p95=${P95} ms ≤ 1.2 ms"
