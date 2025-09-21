#!/usr/bin/env bash
set -euo pipefail

# Smoke test Unicode normalization rules via /expand (L0)
# Now supports optional per-case "forbid: [ID ...]" to assert absence
# and optional "expect_msgs: ["ID:Message", ...]" to assert messages.
# Usage: bash scripts/smoke_rules_unicode.sh [REST_URL]

REST_URL=${1:-http://127.0.0.1:8080/expand}
GOLDEN=specs/rules/unicode_golden.yaml

if ! command -v jq >/dev/null 2>&1; then
  echo "[unicode-smoke] ERROR: jq is required" >&2
  exit 1
fi

if [[ ! -f "$GOLDEN" ]]; then
  echo "[unicode-smoke] ERROR: missing golden file $GOLDEN" >&2
  exit 1
fi

pass=0; fail=0

# Extract records: file|expect_ids(space sep)|forbid_ids(space sep)|expect_msgs(\n-delimited id:msg pairs)
while IFS='|' read -r file expect forbid emsgs; do
  if [[ -z "$file" ]]; then continue; fi
  if [[ ! -f "$file" ]]; then
    echo "[unicode-smoke] MISSING: $file"; fail=$((fail+1)); continue
  fi

  payload=$(jq -Rs --arg k latex '{($k): .}' < "$file")
  resp=$(curl -s -X POST "$REST_URL" -H 'Content-Type: application/json' -d "$payload" || true)
  if [[ -z "$resp" ]]; then
    echo "[unicode-smoke] FAIL: empty response for $file"; fail=$((fail+1)); continue
  fi

  ids=$(echo "$resp" | jq -r 'if (.validators | type)=="array" then .validators[]?.id elif (.validators.results?!=null) then .validators.results[]?.id else empty end')
  id_msg_pairs=$(echo "$resp" | jq -r 'if (.validators | type)=="array" then [.validators[]?|[.id, .message]|@tsv] elif (.validators.results?!=null) then [.validators.results[]?|[.id, .message]|@tsv] else [] end | .[]')

  ok=1
  # All expected IDs must be present
  for id in $expect; do
    if ! echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done
  # All forbidden IDs must be absent
  for id in $forbid; do
    if echo "$ids" | grep -q "^$id$"; then ok=0; fi
  done

  # Messages: each line "ID:Message" must match exactly
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
    pretty_expect=$(echo "$expect" | tr '\n' ' ')
    pretty_forbid=$(echo "$forbid" | tr '\n' ' ')
    echo "[unicode-smoke] PASS: $file -> expect:[$pretty_expect] forbid:[$pretty_forbid]"
    pass=$((pass+1))
  else
    echo "[unicode-smoke] FAIL: $file expected:[$expect] forbid:[$forbid] messages:[$(echo "$emsgs" | tr '\n' ';')] got: $(echo "$ids" | tr '\n' ' ')" >&2
    fail=$((fail+1))
  fi
done < <(
  awk '
    BEGIN { file=""; expect=""; forbid=""; emsgs="" }
    /^[[:space:]]*-[[:space:]]*file:/ {
      if (file!="") { print file "|" expect "|" forbid "|" emsgs; expect=""; forbid=""; emsgs="" }
      # file path may have leading spaces; strip key and trim
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
      if ($0 ~ /^[[:space:]]*expect_msgs:/) {
        inmsgs=1; next
      }
      if (inmsgs==1) {
        if ($0 ~ /^[[:space:]]*-/) {
          line=$0; sub(/^[[:space:]]*-[[:space:]]*/, "", line); gsub(/^\"|\"$/, "", line);
          # accumulate as multi-line field separated by semicolons
          if (emsgs!="") emsgs=emsgs ";" line; else emsgs=line
          next
        } else if ($0 ~ /^[[:space:]]*$/) {
          next
        } else {
          inmsgs=0
        }
      }
    }
    END { if (file!="") print file "|" expect "|" forbid "|" emsgs }
  ' "$GOLDEN"
)

echo "[unicode-smoke] Summary: pass=$pass fail=$fail"
[[ $fail -eq 0 ]]
