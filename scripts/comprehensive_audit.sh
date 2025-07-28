#!/bin/bash

echo "4. SYSTEMATIC FILE COMPILATION TEST:"
echo "===================================="

# Initialize counters
TOTAL=0
WORKING=0
FAILED=0

# Arrays to store results
declare -a WORKING_FILES
declare -a FAILED_FILES

# Test each .v file
find . -name "*.v" -not -path "./archive/*" | sort | while read file; do
    TOTAL=$((TOTAL + 1))
    printf "%-50s: " "$file"
    
    # Test compilation with timeout
    if timeout 10 coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅"
        WORKING=$((WORKING + 1))
        echo "$file" >> working_files_audit.txt
    else
        echo "❌"
        FAILED=$((FAILED + 1))
        echo "$file" >> failed_files_audit.txt
    fi
done

# Count results
if [ -f working_files_audit.txt ]; then
    WORKING=$(wc -l < working_files_audit.txt)
else
    WORKING=0
fi

if [ -f failed_files_audit.txt ]; then
    FAILED=$(wc -l < failed_files_audit.txt)
else
    FAILED=0
fi

TOTAL=$((WORKING + FAILED))

echo ""
echo "SUMMARY:"
echo "--------"
echo "Total files: $TOTAL"
echo "✅ Working: $WORKING"
echo "❌ Failed: $FAILED"
echo "Success rate: $(( WORKING * 100 / TOTAL ))%"

# Clean up temp files
rm -f working_files_audit.txt failed_files_audit.txt