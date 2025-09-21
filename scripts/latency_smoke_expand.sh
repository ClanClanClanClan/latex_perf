#!/usr/bin/env bash
set -euo pipefail

# Measure /expand latencies and run acceptance_gate.sh on the results.
# Usage: L0_VALIDATORS=pilot bash scripts/latency_smoke_expand.sh N [REST_URL]

N=${1:-100}
REST_URL=${2:-http://127.0.0.1:8080/expand}
LAT=/tmp/latencies_ms.txt
TMP=/tmp/expand_payload.json

if ! command -v jq >/dev/null 2>&1; then
  echo "[latency] ERROR: jq required" >&2
  exit 1
fi

if [[ -z "${L0_VALIDATORS:-}" ]]; then
  export L0_VALIDATORS=pilot
fi

echo "[latency] Writing latencies to $LAT" >&2
rm -f "$LAT"

payload=$(jq -Rs --arg k latex '{($k): .}' <<'TXT'
Text with "quotes" -- and --- and tabs\t and ...
TXT
)
echo "$payload" > "$TMP"

for ((i=1;i<=N;i++)); do
  t0=$(python - <<'PY'
import time; print(time.time())
PY
)
  curl -s -X POST "$REST_URL" -H 'Content-Type: application/json' --data-binary @"$TMP" >/dev/null || true
  t1=$(python - <<'PY'
import time; print(time.time())
PY
)
  dt_ms=$(python - "$t0" "$t1" <<'PY'
import sys
t0=float(sys.argv[1]); t1=float(sys.argv[2])
print((t1-t0)*1000.0)
PY
)
  echo "$dt_ms" >> "$LAT"
done

bash acceptance_gate.sh "$LAT"

