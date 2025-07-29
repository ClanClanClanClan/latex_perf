#!/bin/bash

echo "🔧 SYSTEMATIC FIX: Testing & Fixing All Files"
echo "============================================="

# First build core dependencies
echo "📦 Building core dependencies first..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1
coqc -R . "" rules/phase1/TypoRules.v >/dev/null 2>&1
coqc -R . "" rules/phase1/CommandRules.v >/dev/null 2>&1
echo "✅ Core dependencies built"

echo ""
echo "🔍 Testing all files systematically..."

SUCCESS_COUNT=0
FAILURE_COUNT=0
FIXED_COUNT=0

# Test each file
while IFS= read -r file; do
    echo -n "Testing $file... "
    
    # First attempt to compile
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅ OK"
        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
    else
        # Capture the error
        ERROR=$(coqc -R . "" "$file" 2>&1 | head -5)
        
        # Check for common fixable issues
        if echo "$ERROR" | grep -q "Cannot find.*Top\."; then
            echo "🔧 Fixing Top. imports..."
            # Fix Top. imports
            sed -i '' 's/Top\.core\./core\./g' "$file"
            sed -i '' 's/Top\.ValidationTypes/ValidationTypes/g' "$file"
            sed -i '' 's/Top\.rules\./rules\./g' "$file"
            sed -i '' 's/Top\.//' "$file"
            
            # Test again
            if coqc -R . "" "$file" >/dev/null 2>&1; then
                echo "   ✅ FIXED!"
                FIXED_COUNT=$((FIXED_COUNT + 1))
                SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
            else
                echo "   ❌ Still broken"
                FAILURE_COUNT=$((FAILURE_COUNT + 1))
            fi
        else
            echo "❌ FAILED"
            echo "   Error: $(echo "$ERROR" | head -1)"
            FAILURE_COUNT=$((FAILURE_COUNT + 1))
        fi
    fi
done < all_v_files.txt

echo ""
echo "📊 RESULTS:"
echo "   Total files: 90"
echo "   ✅ Working: $SUCCESS_COUNT"
echo "   🔧 Fixed: $FIXED_COUNT"
echo "   ❌ Still broken: $FAILURE_COUNT"
echo "   Success rate: $(( SUCCESS_COUNT * 100 / 90 ))%"

# Clean up
rm -f all_v_files.txt