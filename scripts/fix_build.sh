#!/bin/bash

echo "🔧 FIXING BUILD SYSTEMATICALLY..."
echo "================================="

# Clean everything first
echo "🧹 Cleaning..."
make clean 2>/dev/null || true
rm -f *.glob *.vo *.vok *.vos
rm -f core/*.glob core/*.vo core/*.vok core/*.vos  
rm -f rules/*/*.glob rules/*/*.vo rules/*/*.vok rules/*/*.vos

# Build core files in correct order
echo ""
echo "📦 Building core files..."
coqc -R . Top core/LatexCatcodes.v || { echo "❌ LatexCatcodes failed"; exit 1; }
echo "✅ LatexCatcodes"

coqc -R . Top core/LatexLexer.v || { echo "❌ LatexLexer failed"; exit 1; }
echo "✅ LatexLexer"

coqc -R . Top ValidationTypes.v || { echo "❌ ValidationTypes failed"; exit 1; }
echo "✅ ValidationTypes"

coqc -R . Top core/LatexExpanderEnhanced.v || { echo "❌ LatexExpanderEnhanced failed"; exit 1; }
echo "✅ LatexExpanderEnhanced"

# Build test files that should work
echo ""
echo "🧪 Building test files..."
SUCCESS_COUNT=0
FAIL_COUNT=0

for file in *.v; do
    if [[ "$file" != "ValidationTypes.v" ]]; then
        if coqc -R . Top "$file" >/dev/null 2>&1; then
            echo "✅ $file"
            ((SUCCESS_COUNT++))
        else
            echo "❌ $file"
            ((FAIL_COUNT++))
        fi
    fi
done

# Build rule files
echo ""
echo "📏 Building rule files..."
for file in rules/phase1/*.v rules/phase1_5/*.v; do
    if [ -f "$file" ]; then
        if coqc -R . Top "$file" >/dev/null 2>&1; then
            echo "✅ $file"
            ((SUCCESS_COUNT++))
        else
            echo "❌ $file"
            ((FAIL_COUNT++))
        fi
    fi
done

echo ""
echo "================================="
echo "📊 BUILD RESULTS:"
echo "   ✅ Success: $SUCCESS_COUNT files"
echo "   ❌ Failed:  $FAIL_COUNT files"
echo "   📈 Success rate: $(( SUCCESS_COUNT * 100 / (SUCCESS_COUNT + FAIL_COUNT) ))%"

# Check critical files
echo ""
echo "🔍 Critical file status:"
CRITICAL_FILES=(
    "core/LatexExpanderEnhanced.v"
    "tier1_hardcore_paranoid_tests.v"
    "EXTREME_PARANOID_TESTS.v"
    "ACTUAL_HELL_LEVEL_TESTS.v"
)

ALL_CRITICAL_OK=true
for file in "${CRITICAL_FILES[@]}"; do
    if [ -f "${file%.v}.vo" ]; then
        echo "   ✅ $file"
    else
        echo "   ❌ $file"
        ALL_CRITICAL_OK=false
    fi
done

if [ "$ALL_CRITICAL_OK" = true ]; then
    echo ""
    echo "🎉 All critical files compile!"
else
    echo ""
    echo "⚠️  Some critical files failed"
fi