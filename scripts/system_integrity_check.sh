#!/bin/bash
# System Integrity Check - Quick validation of core components
# Can be run frequently to ensure system health

echo "=== SYSTEM INTEGRITY CHECK ==="
echo "Date: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

ERRORS=0

check() {
    if eval "$2" >/dev/null 2>&1; then
        echo "✅ $1"
    else
        echo "❌ $1"
        ((ERRORS++))
    fi
}

echo "Core Environment:"
check "Coq compiler available" "command -v coqc"
check "OCaml compiler available" "command -v ocamlc"
check "Build system present" "test -f Makefile"

echo ""
echo "Critical Files:"
check "CARC manifest exists" "test -f carc_manifest.json"
check "UVSNA core module exists" "test -f src/coq/vsna/UVSNA.v"
check "Rule loader exists" "test -f src/ocaml/rule_loader.ml"
check "Bridge module exists" "test -f src/ocaml/carc_uvsna_bridge.ml"

echo ""
echo "Build System:"
check "Validation target works" "make validate"
check "Status target works" "make status"

echo ""
echo "Data Integrity:"
if [ -f "carc_manifest.json" ]; then
    RULE_COUNT=$(grep -c '"rule_id"' carc_manifest.json)
    if [ "$RULE_COUNT" -eq 499 ]; then
        echo "✅ CARC manifest has correct rule count ($RULE_COUNT)"
    else
        echo "❌ CARC manifest rule count incorrect (expected 499, found $RULE_COUNT)"
        ((ERRORS++))
    fi
fi

if [ -f "src/coq/vsna/UVSNA.v" ]; then
    LINE_COUNT=$(wc -l < src/coq/vsna/UVSNA.v)
    if [ "$LINE_COUNT" -eq 253 ]; then
        echo "✅ UVSNA module has correct line count ($LINE_COUNT)"
    else
        echo "❌ UVSNA module line count changed (expected 253, found $LINE_COUNT)"
        ((ERRORS++))
    fi
fi

echo ""
if [ $ERRORS -eq 0 ]; then
    echo "🎉 SYSTEM INTEGRITY: PASSED"
    echo "Core components are healthy."
else
    echo "⚠️  SYSTEM INTEGRITY: $ERRORS ISSUES DETECTED"
    echo "System needs attention."
fi

exit $ERRORS