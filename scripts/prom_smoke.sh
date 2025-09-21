#!/usr/bin/env bash
set -euo pipefail

MODE=${1:-tcp}
ADDR=${L0_PROM_ADDR:-127.0.0.1:9109}
UDS=${L0_PROM_UDS:-/tmp/l0_prom.sock}

if [[ "$MODE" == "tcp" ]]; then
  URL="http://${ADDR}/metrics"
  echo "[prom-smoke] GET $URL"
  curl -fsS "$URL" | sed -n '1,20p'
  echo "[prom-smoke] OK"
else
  echo "[prom-smoke] GET uds://$UDS"
  curl -fsS --unix-socket "$UDS" http://localhost/metrics | sed -n '1,20p'
  echo "[prom-smoke] OK"
fi
