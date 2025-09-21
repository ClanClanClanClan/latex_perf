#!/usr/bin/env bash
set -euo pipefail

# Merge multiple single-row CSVs with a label into a combined CSV.
# Usage: merge_perf_csv.sh OUT.csv LABEL1 FILE1.csv [LABEL2 FILE2.csv ...]

OUT=${1:?OUT csv}
shift

echo "label,min_ms,p50_ms,p95_ms,p99_ms,p999_ms,max_ms" > "$OUT"
while (( "$#" )); do
  LABEL=${1:?label}
  FILE=${2:?file}
  shift 2
  if [[ -f "$FILE" ]]; then
    LINE=$(awk -F, 'NR==2{printf "%s,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f\n", l,$2,$3,$4,$5,$6,$7}' l="$LABEL" "$FILE" || true)
    if [[ -n "$LINE" ]]; then echo "$LINE" >> "$OUT"; fi
  else
    echo "[merge] WARN: missing $FILE" >&2
  fi
done

echo "[merge] wrote $OUT" >&2

