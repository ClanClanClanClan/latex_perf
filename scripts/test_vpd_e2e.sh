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
RULE_COUNT=$(echo "$FULL" | grep -c 'let r_\(typo\|enc\)_')
echo "[vpd-e2e] Full manifest generated $RULE_COUNT rules"
if [ "$RULE_COUNT" -ne 80 ]; then
  echo "FAIL: expected 80 rules, got $RULE_COUNT"
  exit 1
fi
echo "[vpd-e2e] PASS: rule count = 80"

# Verify all 80 VPD-patterned rules present (56 TYPO + 24 ENC)
for id in TYPO-001 TYPO-002 TYPO-003 TYPO-004 TYPO-005 TYPO-006 \
          TYPO-007 TYPO-008 TYPO-009 TYPO-010 TYPO-011 TYPO-012 \
          TYPO-013 TYPO-014 TYPO-015 TYPO-016 TYPO-017 TYPO-018 \
          TYPO-021 TYPO-022 TYPO-023 TYPO-024 TYPO-025 TYPO-026 \
          TYPO-027 TYPO-028 TYPO-029 TYPO-030 TYPO-032 TYPO-033 \
          TYPO-034 TYPO-035 TYPO-036 TYPO-037 TYPO-038 TYPO-039 \
          TYPO-040 TYPO-041 TYPO-042 TYPO-043 TYPO-045 TYPO-046 \
          TYPO-047 TYPO-048 TYPO-049 TYPO-051 TYPO-052 TYPO-053 \
          TYPO-054 TYPO-055 TYPO-056 TYPO-057 TYPO-058 TYPO-061 \
          TYPO-062 TYPO-063 \
          ENC-001 ENC-002 ENC-003 ENC-004 ENC-005 ENC-006 \
          ENC-007 ENC-008 ENC-009 ENC-010 ENC-011 ENC-012 \
          ENC-013 ENC-014 ENC-015 ENC-016 ENC-017 ENC-018 \
          ENC-019 ENC-020 ENC-021 ENC-022 ENC-023 ENC-024; do
  echo "$FULL" | grep -q "\"$id\"" || { echo "FAIL: missing $id"; exit 1; }
done
echo "[vpd-e2e] PASS: all 80 rules present in full manifest"

# ── Test 2b: Batch 2 regex rules compile correctly ─────────────────

echo "[vpd-e2e] Checking batch 2 regex rules..."
echo "$FULL" | grep -q 'Str.regexp' || { echo "FAIL: no Str.regexp in generated code"; exit 1; }
echo "$FULL" | grep -q '"TYPO-036"' || { echo "FAIL: missing TYPO-036 (shouting)"; exit 1; }
echo "$FULL" | grep -q '"TYPO-038"' || { echo "FAIL: missing TYPO-038 (email)"; exit 1; }
echo "$FULL" | grep -q '"TYPO-054"' || { echo "FAIL: missing TYPO-054 (en-dash)"; exit 1; }
echo "$FULL" | grep -q '"TYPO-057"' || { echo "FAIL: missing TYPO-057 (degree)"; exit 1; }
echo "[vpd-e2e] PASS: batch 2 regex rules verified"

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
