#!/usr/bin/env bash
set -euo pipefail

HOST=${HOST:-127.0.0.1}
PORT=${PORT:-8080}
BASE="http://$HOST:$PORT"

ensure_keys() {
  local json=$1; shift
  for k in "$@"; do
    if ! echo "$json" | jq -e ". | has(\"$k\")" >/dev/null; then
      echo "[schema] FAIL: missing key '$k'" >&2; return 1
    fi
  done
}

# /expand
EXP=$(curl -fsS -X POST "$BASE/expand" -H 'Content-Type: application/json' -d '{"latex":"Text with \"quotes\" and -- and ..."}')
ensure_keys "$EXP" expanded validators
echo "$EXP" | jq -e '.validators | has("results") and has("applied") and has("errors")' >/dev/null
echo "$EXP" | jq -e '.validators.results | type == "array"' >/dev/null
echo "$EXP" | jq -e 'all(.validators.results[]?; has("id") and has("severity") and has("message") and has("count"))' >/dev/null
echo "$EXP" | jq -e 'all(.validators.results[]?; (.severity|type)=="string" and (.count|type)=="number")' >/dev/null

# /tokenize
TOK=$(curl -fsS -X POST "$BASE/tokenize" -H 'Content-Type: application/json' -d '{"latex":"Text with \"quotes\" and -- and ..."}')
ensure_keys "$TOK" ok status origin metrics validators service
echo "$TOK" | jq -e '.validators | has("results") and has("applied") and has("errors")' >/dev/null
echo "$TOK" | jq -e '.validators.results | type == "array"' >/dev/null
echo "$TOK" | jq -e 'all(.validators.results[]?; has("id") and has("severity") and has("message") and has("count"))' >/dev/null
echo "$TOK" | jq -e 'all(.validators.results[]?; (.severity|type)=="string" and (.count|type)=="number")' >/dev/null

echo "[schema] PASS: /expand and /tokenize shapes OK"

