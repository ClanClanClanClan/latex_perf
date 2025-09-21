#!/usr/bin/env bash
set -euo pipefail

# Smoke test pilot L0 rules via REST /expand (does not require SIMD service).
# IMPORTANT: Start REST with the env set, e.g. `L0_VALIDATORS=pilot make rest-run`.
# Supports optional forbid: [ID ...] and expect_msgs: ["ID:Message", ...]
# Usage: bash scripts/smoke_rules_pilot.sh [REST_URL]
# Default REST_URL: http://127.0.0.1:8080/expand

REST_URL=${1:-http://127.0.0.1:8080/expand}
GOLDEN=specs/rules/pilot_v1_golden.yaml

if ! command -v jq >/dev/null 2>&1; then
  echo "[smoke] ERROR: jq is required" >&2
  exit 1
fi

if [[ -z "${L0_VALIDATORS:-}" ]]; then
  echo "[smoke] NOTE: enabling pilot validators via L0_VALIDATORS=pilot" >&2
  export L0_VALIDATORS=pilot
fi

if [[ ! -f "$GOLDEN" ]]; then
  echo "[smoke] ERROR: missing golden file $GOLDEN" >&2
  exit 1
fi

pass=0; fail=0

# Parse YAML cases into records: file|expect_ids|forbid_ids|expect_msgs
while IFS='|' read -r file expect forbid emsgs; do
  [[ -z "$file" ]] && continue
  if [[ ! -f "$file" ]]; then
    echo "[smoke] MISSING: $file"; fail=$((fail+1)); continue
  fi

  payload=$(jq -Rs --arg k latex '{($k): .}' < "$file")
  resp=$(curl -s -X POST "$REST_URL" -H 'Content-Type: application/json' -d "$payload" || true)
  if [[ -z "$resp" ]]; then
    echo "[smoke] FAIL: empty response for $file"; fail=$((fail+1)); continue
  fi

  ids=$(echo "$resp" | jq -r 'if (.validators | type) == "array" then .validators[]?.id elif (.validators.results? != null) then .validators.results[]?.id else empty end')
  id_msg_pairs=$(echo "$resp" | jq -r 'if (.validators | type)=="array" then [.validators[]?|[.id, .message]|@tsv] elif (.validators.results?!=null) then [.validators.results[]?|[.id, .message]|@tsv] else [] end | .[]')

  ok=1
  for id in $expect; do
    if ! echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done
  for id in $forbid; do
    if echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done

  if [[ -n "${emsgs:-}" ]]; then
    while IFS= read -r pair; do
      [[ -z "$pair" ]] && continue
      idexp=${pair%%:*}
      msgexp=${pair#*:}
      if ! echo "$id_msg_pairs" | awk -F '\t' -v id="$idexp" -v msg="$msgexp" '($1==id && $2==msg){found=1} END{exit(found?0:1)}'; then
        ok=0
      fi
    done <<< "$(printf "%s" "$emsgs" | tr '\\;' '\n')"
  fi

  if [[ $ok -eq 1 ]]; then
    echo "[smoke] PASS: $file -> expect:[$expect] forbid:[$forbid] messages:[$(echo "$emsgs" | tr '\n' ';')]"
    pass=$((pass+1))
  else
    echo "[smoke] FAIL: $file expected:[$expect] forbid:[$forbid] messages:[$(echo "$emsgs" | tr '\n' ';')] got: $(echo "$ids" | tr '\n' ' ')" >&2
    fail=$((fail+1))
  fi
done < <(
  awk '
    BEGIN { file=""; expect=""; forbid=""; emsgs="" }
    /^[[:space:]]*-[[:space:]]*file:/ {
      if (file!="") { print file "|" expect "|" forbid "|" emsgs; expect=""; forbid=""; emsgs="" }
      sub(/^[[:space:]]*-[[:space:]]*file:[[:space:]]*/,""); file=$0
    }
    /^[[:space:]]*expect:/ {
      s=$0; sub(/^[[:space:]]*expect:[[:space:]]*\[/, "", s); sub(/\][[:space:]]*$/, "", s);
      gsub(/"|,/, "", s); gsub(/^[[:space:]]+|[[:space:]]+$/, "", s);
      expect=s
    }
    /^[[:space:]]*forbid:/ {
      s=$0; sub(/^[[:space:]]*forbid:[[:space:]]*\[/, "", s); sub(/\][[:space:]]*$/, "", s);
      gsub(/"|,/, "", s); gsub(/^[[:space:]]+|[[:space:]]+$/, "", s);
      forbid=s
    }
    /^[[:space:]]*expect_msgs:/, /^[[:space:]]*[^ ]/ {
      if ($0 ~ /^[[:space:]]*expect_msgs:/) { inmsgs=1; next }
      if (inmsgs==1) {
        if ($0 ~ /^[[:space:]]*-/) {
          line=$0; sub(/^[[:space:]]*-[[:space:]]*/, "", line); gsub(/^\"|\"$/, "", line);
          if (emsgs!="") emsgs=emsgs ";" line; else emsgs=line
          next
        } else if ($0 ~ /^[[:space:]]*$/) { next } else { inmsgs=0 }
      }
    }
    END { if (file!="") print file "|" expect "|" forbid "|" emsgs }
  ' "$GOLDEN"
)

echo "[smoke] Summary: pass=$pass fail=$fail"
[[ $fail -eq 0 ]]
