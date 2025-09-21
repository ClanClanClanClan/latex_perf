#!/usr/bin/env bash
set -euo pipefail

# Validate that runtime rule IDs exist in rules_v3.yaml and that severities
# match the pilot registry (specs/rules/pilot_v1.yaml).

RUNTIME=latex-parse/src/validators.ml
CATALOG=specs/rules/rules_v3.yaml
PILOT=specs/rules/pilot_v1.yaml

if [[ ! -f "$RUNTIME" || ! -f "$CATALOG" || ! -f "$PILOT" ]]; then
  echo "[catalog] ERROR: Missing required files" >&2
  exit 2
fi

# Extract runtime (id,severity)
runtime_ids=$(awk '
  /id := "[A-Z0-9-]+"/ { if (match($0, /id := "([A-Z0-9-]+)"/, m)) id=m[1]; }
  /severity = (Error|Warning|Info)/ { if (match($0, /severity = (Error|Warning|Info)/, m)) { sev=tolower(m[1]); if (id!="") { print id":"sev; id="" } } }
' "$RUNTIME" | sort -u)

if [[ -z "$runtime_ids" ]]; then
  echo "[catalog] ERROR: No runtime IDs found" >&2
  exit 3
fi

# Extract catalogue IDs (from rules_v3.yaml)
catalog_ids=$(awk '
  /^[[:space:]]*- id: / {
    if (match($0, /- id: "([^"]+)"/, m)) {
      print m[1];
    }
  }
' "$CATALOG" | sort -u)

# Extract pilot severities and preconditions (id:severity:precond)
pilot_ids=$(awk '
  /^[[:space:]]*- id: / { if (match($0, /- id: "([^"]+)"/, m)) id=m[1]; }
  /precondition:/ { if (match($0, /precondition:[[:space:]]*([A-Za-z_]+)/, m)) pre=m[1]; }
  /default_severity:/ { if (match($0, /default_severity:[[:space:]]*([A-Za-z]+)/, m)) { sev=tolower(m[1]); if (id!="") { print id":"sev":""pre; id=""; pre="" } } }
' "$PILOT" | sort -u)

fail=0

# Check existence in catalog
while IFS= read -r pair; do
  rid=${pair%%:*}
  if ! grep -q "^- id: \"$rid\"" "$CATALOG"; then
    echo "[catalog] FAIL: runtime rule not in catalog: $rid" >&2
    fail=1
  fi
done <<< "$runtime_ids"

# Check severities and preconditions against pilot registry (subset compliance)
while IFS= read -r pair; do
  rid=${pair%%:*}; rsev=${pair##*:}
  psev=$(echo "$pilot_ids" | grep "^$rid:" | cut -d: -f2 || true)
  ppre=$(echo "$pilot_ids" | grep "^$rid:" | cut -d: -f3 || true)
  if [[ -n "$psev" && "$psev" != "$rsev" ]]; then
    echo "[catalog] FAIL: severity mismatch for $rid: runtime=$rsev pilot=$psev" >&2
    fail=1
  fi
  if [[ -n "$ppre" && "$ppre" != "L0_Lexer" ]]; then
    echo "[catalog] FAIL: precondition mismatch for $rid: pilot=$ppre expected=L0_Lexer" >&2
    fail=1
  fi
done <<< "$runtime_ids"

if [[ $fail -eq 0 ]]; then
  echo "[catalog] PASS: catalogue compliance checks OK"
else
  echo "[catalog] FAIL: catalogue compliance checks failed" >&2
  exit 4
fi
