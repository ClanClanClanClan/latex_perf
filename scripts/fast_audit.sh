#!/bin/bash

echo "🚀 FAST AUDIT - Checking compilation status"
echo "==========================================="

# Build core dependencies first
echo "📦 Building core dependencies..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

WORKING=()
BROKEN=()

echo ""
echo "🔍 Testing files..."

# Test each file
find . -name "*.v" -not -path "./archive/*" | sort | while read file; do
    printf "%-50s" "$file"
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅"
        WORKING+=("$file")
    else
        echo "❌"
        BROKEN+=("$file")
        # Save error for analysis
        echo "$file" >> broken_files.txt
        coqc -R . "" "$file" 2>&1 | head -5 >> broken_files_errors.txt
        echo "---" >> broken_files_errors.txt
    fi
done

# Count results
TOTAL=$(find . -name "*.v" -not -path "./archive/*" | wc -l)
WORKING_COUNT=$(find . -name "*.v" -not -path "./archive/*" | while read f; do coqc -R . "" "$f" >/dev/null 2>&1 && echo 1; done | wc -l)
BROKEN_COUNT=$((TOTAL - WORKING_COUNT))

echo ""
echo "📊 RESULTS:"
echo "   Total: $TOTAL files"
echo "   ✅ Working: $WORKING_COUNT"
echo "   ❌ Broken: $BROKEN_COUNT"
echo "   Success rate: $((WORKING_COUNT * 100 / TOTAL))%"

if [ -f broken_files.txt ]; then
    echo ""
    echo "💾 Broken files saved to: broken_files.txt"
    echo "💾 Error details saved to: broken_files_errors.txt"
fi