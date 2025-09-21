#!/usr/bin/env bash
set -euo pipefail

HOST=${HOST:-127.0.0.1}
PORT=${PORT:-8080}
URL="http://${HOST}:${PORT}/tokenize"

echo "[rest-smoke] POST ${URL}"
BODY='{"latex":"\\documentclass{article}\\begin{document}Hello $x^2$\\end{document}"}'

HTTP_CODE=$(curl -fsS -o /tmp/rest_smoke_out.json -w '%{http_code}' \
  -H 'Content-Type: application/json' \
  -X POST --data "$BODY" "$URL" || true)

if [[ "$HTTP_CODE" != "200" ]]; then
  echo "[rest-smoke] FAIL: HTTP $HTTP_CODE" >&2
  exit 1
fi

echo "[rest-smoke] OK (200)"
sed -n '1,4p' /tmp/rest_smoke_out.json || true
