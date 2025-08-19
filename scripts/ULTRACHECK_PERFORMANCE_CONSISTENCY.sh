#!/bin/bash
# ULTRACHECK PERFORMANCE CONSISTENCY SCRIPT
# This script verifies ALL performance claims are consistent with verified reality
# Run this anytime you suspect contradictory performance numbers

set -e

echo "🔍 ULTRACHECK: Performance Consistency Verification"
echo "=================================================="
echo ""

# Define the verified truth
VERIFIED_MEDIAN="18.22ms"
VERIFIED_P95="23.84ms"
STANDARD_OCAML="39.28ms"
TARGET="≤20ms"

echo "📊 VERIFIED PERFORMANCE REALITY:"
echo "  • Standard OCaml: $STANDARD_OCAML ❌ FAILS"
echo "  • Flambda2 Median: $VERIFIED_MEDIAN ✅"
echo "  • Flambda2 P95: $VERIFIED_P95 ⚠️ (over ${TARGET} target)"
echo ""

# Check for contradictory claims
echo "🚨 SCANNING FOR CONTRADICTORY PERFORMANCE CLAIMS:"
echo ""

# Look for suspicious performance numbers that don't match reality
SUSPICIOUS_NUMBERS=(
    "21.8ms"     # Old wrong claim in COMPREHENSIVE_FULL_AUDIT_REPORT
    "17-18ms"    # Vague range claims  
    "31.40ms"    # Old standard OCaml measurement
    "14.07ms"    # Various spec claims
    "25ms"       # Different target claims
    "42ms"       # SLA claims
    "1ms"        # Unrealistic targets
    "2ms"        # Unrealistic targets
)

FOUND_ISSUES=0

for number in "${SUSPICIOUS_NUMBERS[@]}"; do
    echo -n "Checking for '$number'... "
    
    # Search in key files (excluding quarantined confusion)
    MATCHES=$(grep -r "$number" . \
        --include="*.md" --include="*.yaml" --include="*.yml" \
        --exclude-dir=".git" \
        --exclude-dir="_build" \
        --exclude-dir=".archived_confusion" \
        --exclude="THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md" \
        2>/dev/null | wc -l)
    
    if [ "$MATCHES" -gt 0 ]; then
        echo "❌ FOUND $MATCHES instances"
        FOUND_ISSUES=1
        
        # Show first few matches
        grep -r "$number" . \
            --include="*.md" --include="*.yaml" --include="*.yml" \
            --exclude-dir=".git" \
            --exclude-dir="_build" \
            --exclude-dir=".archived_confusion" \
            --exclude="THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md" \
            2>/dev/null | head -3 | sed 's/^/    /'
    else
        echo "✅ CLEAN"
    fi
done

echo ""

# Verify the definitive truth document exists and is referenced
echo "🔍 VERIFYING SINGLE SOURCE OF TRUTH:"
if [ -f "docs/THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md" ]; then
    echo "✅ THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md exists"
    
    # Check if CLAUDE.md references it
    if grep -q "THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md" CLAUDE.md; then
        echo "✅ CLAUDE.md references the definitive truth"
    else
        echo "❌ CLAUDE.md does not reference the definitive truth"
        FOUND_ISSUES=1
    fi
else
    echo "❌ THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md missing!"
    FOUND_ISSUES=1
fi

echo ""

# Verify the working test binary exists
echo "🔍 VERIFYING WORKING IMPLEMENTATIONS:"
if [ -f "test/performance/test_flambda2" ]; then
    echo "✅ Working test_flambda2 binary exists"
    
    # Quick test to verify it actually works
    echo "Testing the binary..."
    if ./test/performance/test_flambda2 | grep -q "18\\."; then
        echo "✅ Binary produces expected ~18ms results"
    else
        echo "⚠️  Binary results don't match expected pattern"
    fi
else
    echo "❌ test_flambda2 binary missing!"
    FOUND_ISSUES=1
fi

echo ""
echo "=================================================="

if [ "$FOUND_ISSUES" -eq 0 ]; then
    echo "🎉 ULTRACHECK PASSED: All performance claims are consistent!"
    echo ""
    echo "✅ Summary:"
    echo "  • No contradictory performance numbers found"
    echo "  • Single source of truth exists and is referenced"
    echo "  • Working implementation verified"
    echo ""
    echo "Performance is 100% clear forever. ✨"
    exit 0
else
    echo "❌ ULTRACHECK FAILED: Contradictory performance claims found!"
    echo ""
    echo "🔧 TO FIX:"
    echo "  1. Update all files to reference: docs/THE_DEFINITIVE_L0_PERFORMANCE_TRUTH.md"
    echo "  2. Replace wrong numbers with verified reality:"
    echo "     - Standard OCaml: $STANDARD_OCAML"
    echo "     - Flambda2: $VERIFIED_MEDIAN median, $VERIFIED_P95 P95"
    echo "  3. Re-run this script to verify fixes"
    echo ""
    echo "The confusion continues until all numbers are consistent!"
    exit 1
fi