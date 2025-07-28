#!/bin/bash

echo "🎯 ACCURATE PROJECT AUDIT"
echo "========================="

# Clean everything first
rm -f *.vo *.vok *.vos *.glob core/*.vo core/*.vok core/*.vos core/*.glob rules/*/*.vo rules/*/*.vok rules/*/*.vos rules/*/*.glob

echo "Phase 1: Testing core foundation (in dependency order)..."

# Core files that MUST work
CORE_FOUNDATION=(
    "basic_test.v"
    "super_quick_test.v"  
    "core/LatexCatcodes.v"
    "core/LatexLexer.v"
    "ValidationTypes.v"
    "rules/phase1/TypoRules.v"
    "rules/phase1/CommandRules.v"
)

CORE_SUCCESS=0
CORE_TOTAL=${#CORE_FOUNDATION[@]}

echo "🔧 Building core foundation..."
for file in "${CORE_FOUNDATION[@]}"; do
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅ $file"
        CORE_SUCCESS=$((CORE_SUCCESS + 1))
    else
        echo "❌ $file FAILED"
        coqc -R . "" "$file" 2>&1 | head -2
    fi
done

echo ""
echo "Phase 2: Testing additional files..."

# Additional files that might work
ADDITIONAL_FILES=(
    "ValidationRules.v"
    "ultra_minimal_tests.v"
    "HELL_LEVEL_TESTS.v"
    "rules/phase1/RuleTests.v"
    "core/CatcodeAnalysis.v"
    "core/LatexExpanderEnhanced.v"
)

ADDITIONAL_SUCCESS=0
ADDITIONAL_TOTAL=${#ADDITIONAL_FILES[@]}

for file in "${ADDITIONAL_FILES[@]}"; do
    if [ -f "$file" ]; then
        if coqc -R . "" "$file" >/dev/null 2>&1; then
            echo "✅ $file"
            ADDITIONAL_SUCCESS=$((ADDITIONAL_SUCCESS + 1))
        else
            echo "❌ $file"
        fi
    else
        echo "⚠️  $file (not found)"
    fi
done

echo ""
echo "📊 ACCURATE RESULTS:"
echo "Core foundation: $CORE_SUCCESS/$CORE_TOTAL ($(( CORE_SUCCESS * 100 / CORE_TOTAL ))%)"
echo "Additional files: $ADDITIONAL_SUCCESS/$ADDITIONAL_TOTAL ($(( ADDITIONAL_SUCCESS * 100 / ADDITIONAL_TOTAL ))%)"

TOTAL_WORKING=$(( CORE_SUCCESS + ADDITIONAL_SUCCESS ))
TOTAL_TESTED=$(( CORE_TOTAL + ADDITIONAL_TOTAL ))

echo ""
echo "🎯 HONEST ASSESSMENT:"
if [ $CORE_SUCCESS -eq $CORE_TOTAL ]; then
    echo "✅ CORE FOUNDATION: SOLID ($CORE_SUCCESS/$CORE_TOTAL working)"
    echo "📈 Total working files: $TOTAL_WORKING/$TOTAL_TESTED"
    echo "🚀 Project has working foundation for development"
else
    echo "❌ CORE FOUNDATION: BROKEN (only $CORE_SUCCESS/$CORE_TOTAL working)"
    echo "🚨 Cannot proceed until core is fixed"
fi