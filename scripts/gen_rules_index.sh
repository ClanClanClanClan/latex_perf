#!/usr/bin/env bash
set -euo pipefail

# Generate a normalized rules index (JSON array) from specs/rules/rules_v3.yaml
# Fields: id, precondition, default_severity, owner, description

YAML=specs/rules/rules_v3.yaml
if [[ ! -f "$YAML" ]]; then
  echo "missing $YAML" >&2; exit 2
fi

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

awk '
  BEGIN { inrec=0; id=""; pre=""; sev=""; own=""; desc="" }
  /^-[[:space:]]+id:/ { if (inrec==1 && id!="") { printf "{\"id\":\"%s\",\"precondition\":\"%s\",\"default_severity\":\"%s\",\"owner\":\"%s\",\"description\":\"%s\"}\n", id, pre, sev, own, desc; id=""; pre=""; sev=""; own=""; desc="" } inrec=1; if (match($0, /- id: "([^"]+)"/, m)) id=m[1] }
  /^[[:space:]]+precondition:/ { if (match($0, /precondition:[[:space:]]*([A-Za-z_]+)/, m)) pre=m[1] }
  /^[[:space:]]+default_severity:/ { if (match($0, /default_severity:[[:space:]]*([A-Za-z]+)/, m)) { sev=tolower(m[1]) } }
  /^[[:space:]]+owner:/ { if (match($0, /owner:[[:space:]]*"([^"]+)"/, m)) own=m[1] }
  /^[[:space:]]+description:/ {
    if (match($0, /description:[[:space:]]*"(.*)"/, m)) {
      desc=m[1];
      gsub(/\\/, "\\\\", desc);
      gsub(/"/, "\\\"", desc);
    }
  }
  END { if (inrec==1 && id!="") { printf "{\"id\":\"%s\",\"precondition\":\"%s\",\"default_severity\":\"%s\",\"owner\":\"%s\",\"description\":\"%s\"}\n", id, pre, sev, own, desc } }
' "$YAML" > "$tmp"

echo '['
nl=0
while IFS= read -r line; do
  if [[ $nl -eq 0 ]]; then echo "  $line"; nl=1; else echo "  ,$line"; fi
done < "$tmp"
echo ']'
