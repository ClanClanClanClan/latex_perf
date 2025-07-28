#!/bin/bash

echo "📊 FINAL PROJECT STATUS CHECK"
echo "============================"

# Count total files
TOTAL=$(find . -name "*.v" -not -path "./archive/*" | wc -l)

# Build core dependencies silently
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

# Test compilation status
WORKING=0
BROKEN=0

echo "Testing all files..."
find . -name "*.v" -not -path "./archive/*" | sort | while read file; do
    if timeout 3 coqc -R . "" "$file" >/dev/null 2>&1; then
        WORKING=$((WORKING + 1))
        echo -n "✅"
    else
        BROKEN=$((BROKEN + 1))
        echo -n "❌"
        echo "$file" >> broken_files_final.txt
    fi
done

echo ""
echo ""

# Count results from temp file
WORKING=$(find . -name "*.v" -not -path "./archive/*" | while read f; do timeout 3 coqc -R . "" "$f" >/dev/null 2>&1 && echo 1; done | wc -l)
BROKEN=$((TOTAL - WORKING))

echo "📊 SUMMARY:"
echo "   Total .v files: $TOTAL"
echo "   ✅ Working: $WORKING"
echo "   ❌ Broken: $BROKEN"
echo "   Success rate: $((WORKING * 100 / TOTAL))%"

echo ""
echo "🎯 KEY FILES STATUS:"
echo "   Core foundation (LatexCatcodes, LatexLexer, ValidationTypes):"
for f in core/LatexCatcodes.v core/LatexLexer.v ValidationTypes.v; do
    if coqc -R . "" "$f" >/dev/null 2>&1; then
        echo "      ✅ $f"
    else
        echo "      ❌ $f"
    fi
done

echo ""
echo "   Test files:"
for f in ultra_minimal_tests.v HELL_LEVEL_TESTS.v quick_test.v; do
    if [ -f "$f" ]; then
        if coqc -R . "" "$f" >/dev/null 2>&1; then
            echo "      ✅ $f"
        else
            echo "      ❌ $f"
        fi
    fi
done

if [ -f broken_files_final.txt ]; then
    echo ""
    echo "❌ Broken files saved to: broken_files_final.txt"
fi