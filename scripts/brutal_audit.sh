#!/bin/bash

echo "🚨 BRUTAL HONEST AUDIT"
echo "====================="

# Count all .v files
TOTAL_FILES=$(find . -name "*.v" | grep -v archive | wc -l)
echo "📊 Total .v files (excluding archive): $TOTAL_FILES"

# Test compilation with timeout for each file
echo ""
echo "🔍 Testing ALL files for compilation..."

SUCCESS_COUNT=0
FAILURE_COUNT=0
TIMEOUT_COUNT=0

# Get list of non-archive .v files
find . -name "*.v" | grep -v archive > /tmp/all_files.txt

while IFS= read -r file; do
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅ $file"
        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
    else
        exit_code=$?
        echo "❌ $file (ERROR)"
        FAILURE_COUNT=$((FAILURE_COUNT + 1))
    fi
done < /tmp/all_files.txt

echo ""
echo "📊 BRUTAL HONEST RESULTS:"
echo "   Total files tested: $TOTAL_FILES"
echo "   ✅ Successful: $SUCCESS_COUNT"
echo "   ❌ Failed: $FAILURE_COUNT"  
echo ""

WORKING_PERCENT=$(( SUCCESS_COUNT * 100 / TOTAL_FILES ))
echo "📈 ACTUAL SUCCESS RATE: $WORKING_PERCENT%"

if [ $WORKING_PERCENT -lt 50 ]; then
    echo "🚨 REALITY CHECK: MAJORITY OF PROJECT IS BROKEN"
elif [ $WORKING_PERCENT -lt 80 ]; then
    echo "⚠️  WARNING: SIGNIFICANT PORTION IS BROKEN"
else
    echo "✅ GOOD: MAJORITY OF PROJECT WORKS"
fi

rm -f /tmp/all_files.txt