#!/usr/bin/env bash
set -euo pipefail

# Validate that runtime messages for a whitelist of implemented IDs match
# catalogue descriptions exactly. Initially warns; can be flipped to fail.

CATALOG=specs/rules/rules_v3.yaml
RUNTIME=latex-parse/src/validators.ml

if [[ ! -f "$CATALOG" || ! -f "$RUNTIME" ]]; then
  echo "[msg] ERROR: missing inputs" >&2
  exit 2
fi

# Whitelist of IDs for message validation
IDS=(CMD-001 CMD-003 TYPO-014)

# Build catalogue index (json)
tmp_idx=$(mktemp)
bash scripts/gen_rules_index.sh > "$tmp_idx"

warn=0
for id in "${IDS[@]}"; do
  # Extract catalogue description for id
  catalog_desc=$(jq -r --arg id "$id" '.[] | select(.id==$id) | .description' "$tmp_idx")
  if [[ -z "$catalog_desc" || "$catalog_desc" == "null" ]]; then
    echo "[msg] WARN: no catalogue description for $id" >&2; warn=1; continue
  fi
  # Extract runtime message for id
  runtime_msg=$(awk -v id="$id" '
    BEGIN{RS="\n\n"}
    $0 ~ "id := \""id"\"" {
      if (match($0, /message := \"([^\"]+)\"/, m)) { print m[1] }
    }
  ' "$RUNTIME" | head -n1)
  if [[ -z "$runtime_msg" ]]; then
    echo "[msg] WARN: no runtime message found for $id" >&2; warn=1; continue
  fi
  if [[ "$catalog_desc" != "$runtime_msg" ]]; then
    echo "[msg] WARN: message mismatch for $id" >&2
    echo "  catalog : $catalog_desc" >&2
    echo "  runtime : $runtime_msg" >&2
    warn=1
  else
    echo "[msg] OK: $id matches"
  fi
done

if [[ ${FAIL_ON_MISMATCH:-0} -eq 1 && $warn -eq 1 ]]; then
  echo "[msg] FAIL: message validation" >&2
  exit 3
fi

echo "[msg] Completed (warn=$warn)"
