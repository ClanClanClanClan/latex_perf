#!/usr/bin/env bash
set -euo pipefail

# Combined smoke runner: pilot (L0), Unicode, and L1
# Requires REST running on 8080 and jq installed

echo "[all-smokes] Pilot (L0)"
L0_VALIDATORS=${L0_VALIDATORS:-pilot} bash scripts/smoke_rules_pilot.sh http://127.0.0.1:8080/expand

echo "[all-smokes] Unicode"
bash scripts/smoke_rules_unicode.sh http://127.0.0.1:8080/expand

echo "[all-smokes] L1"
bash scripts/smoke_rules_l1.sh http://127.0.0.1:8080/expand?layer=l1

echo "[all-smokes] Done"

