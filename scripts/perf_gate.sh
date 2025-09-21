#!/usr/bin/env bash
set -euo pipefail

FILE=${1:-"corpora/perf/perf_smoke_big.tex"}
ITERS=${2:-100}
SAMPLES=${SAMPLES:-100}
BIN="_build/default/latex-parse/bench/ab_microbench.exe"

# Median-of-100 batches per R1 plan: collect 100 p95s then take median.
TMPDIR=${TMPDIR:-/tmp}
OUTLIST="$TMPDIR/ab_gate_p95_list.txt"
rm -f "$OUTLIST"

for i in $(seq 1 "$SAMPLES"); do
  CSV="$TMPDIR/ab_microbench_$i.csv"
  $BIN "$FILE" "$ITERS" --csv "$CSV" >/dev/null
  P95=$(awk -F, 'NR==2{print $4}' "$CSV" 2>/dev/null || true)
  if [[ -z "$P95" ]]; then
    echo "[gate] WARN: run $i produced no CSV p95; retrying once"
    $BIN "$FILE" "$ITERS" --csv "$CSV" >/dev/null
    P95=$(awk -F, 'NR==2{print $4}' "$CSV" 2>/dev/null || true)
  fi
  if [[ -n "$P95" ]]; then echo "$P95" >> "$OUTLIST"; fi
done

COUNT=$(wc -l < "$OUTLIST" | tr -d ' ')
if [[ "$COUNT" -lt 80 ]]; then
  echo "[gate] ERROR: insufficient successful samples for median-of-100 ($COUNT)"
  exit 1
fi

MEDIAN=$(sort -n "$OUTLIST" | awk 'NF{a[NR]=$1} END{ if (NR%2){print a[(NR+1)/2]} else {print (a[NR/2]+a[NR/2+1])/2} }')
echo "[gate] median-of-100 p95 = ${MEDIAN} ms"

# Gate: Tier A scalar p95 < 20 ms (SLA 42 ms separate dashboard threshold).
awk -v p95="$MEDIAN" 'BEGIN{if (p95 < 20.0) exit 0; else exit 1}'
