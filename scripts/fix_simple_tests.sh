#!/bin/bash

echo "🔧 FIXING SIMPLE TEST FILES"
echo "========================="

# Build core dependencies
echo "📦 Building core dependencies..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

# Test simple files that don't use LatexExpanderUltimate
SIMPLE_FILES=(
    "test_clean_install.v"
    "test_compute.v"
    "test_errors.v"
    "test_print_result.v"
    "test_single.v"
    "test_vm_compute.v"
    "debug_errors.v"
    "debug_test.v"
    "debug_test2.v"
    "debug_test3.v"
    "debug_test4.v"
    "debug_test5.v"
)

FIXED=0
ALREADY_WORKING=0
STILL_BROKEN=0

for file in "${SIMPLE_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo -n "Testing $file... "
        
        # Check if it compiles
        if coqc -R . "" "$file" >/dev/null 2>&1; then
            echo "✅ Already working"
            ALREADY_WORKING=$((ALREADY_WORKING + 1))
        else
            # Get the error
            ERROR=$(coqc -R . "" "$file" 2>&1 | head -5)
            
            # Check for common fixable issues
            if echo "$ERROR" | grep -q "Cannot find.*Top\."; then
                echo "🔧 Fixing Top. imports..."
                sed -i '' 's/Top\.core\./core\./g' "$file"
                sed -i '' 's/Top\.ValidationTypes/ValidationTypes/g' "$file"
                sed -i '' 's/Top\.rules\./rules\./g' "$file"
                sed -i '' 's/Top\.//' "$file"
                
                if coqc -R . "" "$file" >/dev/null 2>&1; then
                    echo "   ✅ FIXED!"
                    FIXED=$((FIXED + 1))
                else
                    echo "   ❌ Still broken"
                    STILL_BROKEN=$((STILL_BROKEN + 1))
                fi
            else
                echo "❌ Error: $(echo "$ERROR" | head -1)"
                STILL_BROKEN=$((STILL_BROKEN + 1))
            fi
        fi
    fi
done

echo ""
echo "📊 RESULTS:"
echo "   Total files: ${#SIMPLE_FILES[@]}"
echo "   ✅ Already working: $ALREADY_WORKING"
echo "   🔧 Fixed: $FIXED"
echo "   ❌ Still broken: $STILL_BROKEN"
echo "   Success rate: $(( (ALREADY_WORKING + FIXED) * 100 / ${#SIMPLE_FILES[@]} ))%"