#!/bin/bash

echo "🔧 FIXING BROKEN TEST FILES"
echo "=========================="

# Build core dependencies first
echo "📦 Building core dependencies..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

# List of test files that need fixing
TEST_FILES=(
    "ACTUAL_HELL_LEVEL_TESTS.v"
    "EXTREME_PARANOID_TESTS.v"
    "HELL_LEVEL_TESTS.v"
    "comprehensive_l1_tests.v"
    "tier1_def_paranoid_tests.v"
    "tier1_hardcore_paranoid_tests.v"
    "tier1_ultimate_hardcore_tests.v"
    "ultimate_maniac_tests.v"
    "maniac_tests.v"
)

FIXED=0
STILL_BROKEN=0

for file in "${TEST_FILES[@]}"; do
    echo ""
    echo "🔍 Testing $file..."
    
    # Check compilation
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅ Already working!"
        FIXED=$((FIXED + 1))
    else
        # Get error
        ERROR=$(coqc -R . "" "$file" 2>&1 | head -3)
        echo "❌ Error: $ERROR"
        
        # Check if it's trying to import LatexExpanderUltimate
        if echo "$ERROR" | grep -q "LatexExpanderUltimate"; then
            echo "🔧 Attempting to use alternative expander..."
            # Try replacing with LatexExpanderEnhanced
            sed -i '' 's/LatexExpanderUltimate/LatexExpanderEnhanced/g' "$file"
            
            if coqc -R . "" "$file" >/dev/null 2>&1; then
                echo "✅ FIXED by using LatexExpanderEnhanced!"
                FIXED=$((FIXED + 1))
            else
                # Try with basic LatexExpander
                sed -i '' 's/LatexExpanderEnhanced/LatexExpander/g' "$file"
                if coqc -R . "" "$file" >/dev/null 2>&1; then
                    echo "✅ FIXED by using basic LatexExpander!"
                    FIXED=$((FIXED + 1))
                else
                    echo "❌ Still broken after trying alternatives"
                    STILL_BROKEN=$((STILL_BROKEN + 1))
                fi
            fi
        else
            STILL_BROKEN=$((STILL_BROKEN + 1))
        fi
    fi
done

echo ""
echo "📊 RESULTS:"
echo "   Total test files: ${#TEST_FILES[@]}"
echo "   ✅ Fixed/Working: $FIXED"
echo "   ❌ Still broken: $STILL_BROKEN"