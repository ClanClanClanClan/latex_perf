#!/usr/bin/env bash
set -euo pipefail

LAT=${1:-/tmp/latencies_ms.txt}
OUT=${2:-/tmp/latency_badge.json}
if [[ ! -f "$LAT" ]]; then echo "missing $LAT" >&2; exit 2; fi

readarray -t arr < <(sort -n "$LAT")
N=${#arr[@]}
idx() { awk -v n=$N -v p=$1 'BEGIN{printf "%d", int(n*p)}'; }
p50=${arr[$(idx 0.50)]}
p95=${arr[$(idx 0.95)]}
p99=${arr[$(idx 0.99)]}
p999=${arr[$(idx 0.999)]}

cat > "$OUT" <<JSON
{
  "schemaVersion": 1,
  "label": "expand latency p95",
  "message": "$(printf "%.2f ms" "$p95")",
  "color": "blue"
}
JSON
echo "[badge] Wrote $OUT"

