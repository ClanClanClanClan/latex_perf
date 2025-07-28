#!/bin/bash

echo "🔍 Testing CORE files only (in dependency order)"
echo "================================================"

# Clean first
rm -f *.vo *.vok *.vos *.glob core/*.vo core/*.vok core/*.vos core/*.glob

# Test core files in dependency order
CORE_FILES=(
    "basic_test.v"
    "super_quick_test.v"
    "core/LatexCatcodes.v"
    "core/LatexLexer.v"
    "ValidationTypes.v"
)

SUCCESS_COUNT=0
TOTAL_COUNT=${#CORE_FILES[@]}

for file in "${CORE_FILES[@]}"; do
    echo -n "Testing $file... "
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅ SUCCESS"
        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
    else
        echo "❌ FAILED"
        # Show the error for debugging
        coqc -R . "" "$file" 2>&1 | head -3
    fi
done

echo ""
echo "📊 CORE RESULTS:"
echo "   Tested: $TOTAL_COUNT core files"
echo "   Success: $SUCCESS_COUNT"
echo "   Failed: $((TOTAL_COUNT - SUCCESS_COUNT))"
echo "   Success rate: $(( SUCCESS_COUNT * 100 / TOTAL_COUNT ))%"

if [ $SUCCESS_COUNT -eq $TOTAL_COUNT ]; then
    echo "✅ ALL CORE FILES WORK!"
else
    echo "❌ CORE FOUNDATION IS BROKEN"
fi