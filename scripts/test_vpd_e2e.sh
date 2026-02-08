#!/usr/bin/env bash
# E2E test: rules_v3.yaml + vpd_patterns.json → vpd_grammar → vpd_compile → OCaml
set -euo pipefail

echo "[vpd-e2e] Building grammar and compile tools..."
opam exec -- dune build generator/vpd_grammar.exe generator/vpd_compile.exe

MANIFEST=$(mktemp /tmp/vpd_e2e_XXXXXX.json)
trap "rm -f $MANIFEST" EXIT

# ── Test 1: TYPO-001 single-rule E2E ──────────────────────────────────

echo "[vpd-e2e] Generating TYPO-001 manifest from YAML + patterns..."
./_build/default/generator/vpd_grammar.exe \
  specs/rules/rules_v3.yaml \
  specs/rules/vpd_patterns.json \
  --filter TYPO-001 \
  -o "$MANIFEST" 2>&1

echo "[vpd-e2e] Compiling manifest to OCaml..."
GENERATED=$(./_build/default/generator/vpd_compile.exe "$MANIFEST" --internal)

echo "[vpd-e2e] Checking TYPO-001 generated code..."
echo "$GENERATED" | grep -q 'strip_math_segments' || { echo "FAIL: missing strip_math_segments"; exit 1; }
echo "$GENERATED" | grep -q 'count_char s' || { echo "FAIL: missing count_char"; exit 1; }
echo "$GENERATED" | grep -q '"TYPO-001"' || { echo "FAIL: missing TYPO-001 ID"; exit 1; }
echo "$GENERATED" | grep -q '"ASCII straight quotes' || { echo "FAIL: missing TYPO-001 message"; exit 1; }
echo "$GENERATED" | grep -q 'severity = Error' || { echo "FAIL: wrong severity"; exit 1; }
echo "[vpd-e2e] PASS: TYPO-001 single-rule E2E"

# ── Test 2: Full manifest (all pattern entries) ───────────────────────

echo "[vpd-e2e] Generating full manifest..."
./_build/default/generator/vpd_grammar.exe \
  specs/rules/rules_v3.yaml \
  specs/rules/vpd_patterns.json \
  -o "$MANIFEST" 2>&1

FULL=$(./_build/default/generator/vpd_compile.exe "$MANIFEST" --internal)
RULE_COUNT=$(echo "$FULL" | grep -c 'let r_typo_')
echo "[vpd-e2e] Full manifest generated $RULE_COUNT rules"

# Verify all 6 rules present
for id in TYPO-001 TYPO-004 TYPO-005 TYPO-006 TYPO-023 TYPO-030; do
  echo "$FULL" | grep -q "\"$id\"" || { echo "FAIL: missing $id"; exit 1; }
done
echo "[vpd-e2e] PASS: all 6 rules present in full manifest"

# ── Test 3: --validate flag ───────────────────────────────────────────

echo "[vpd-e2e] Testing --validate flag..."
VOUT=$(./_build/default/generator/vpd_grammar.exe \
  specs/rules/rules_v3.yaml \
  specs/rules/vpd_patterns.json \
  --validate --filter TYPO-001 2>&1 >/dev/null)
if echo "$VOUT" | grep -q "WARNING"; then
  echo "FAIL: --validate produced unexpected warnings: $VOUT"
  exit 1
fi
echo "[vpd-e2e] PASS: --validate clean"

echo "[vpd-e2e] ALL TESTS PASSED"
