#!/usr/bin/env bash
set -euo pipefail

HOST=${HOST:-127.0.0.1}
PORT=${PORT:-8080}
URL="http://${HOST}:${PORT}/tokenize"

echo "[rest-smoke:negative] POST ${URL} (expect 503)"
BODY='{"latex":"\\documentclass{article}\\begin{document}Hello\\end{document}"}'

HTTP_CODE=$(curl -s -o /tmp/rest_smoke_neg_out.json -w '%{http_code}' \
  -H 'Content-Type: application/json' \
  -X POST --data "$BODY" "$URL" || true)

if [[ "$HTTP_CODE" == "503" ]]; then
  echo "[rest-smoke:negative] OK (503)"
  exit 0
else
  echo "[rest-smoke:negative] FAIL: expected 503, got ${HTTP_CODE}" >&2
  sed -n '1,10p' /tmp/rest_smoke_neg_out.json || true
  exit 1
fi

