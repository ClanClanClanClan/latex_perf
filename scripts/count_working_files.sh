#!/bin/bash

echo "9. ACCURATE WORKING FILE COUNT:"
echo "==============================="

WORKING=0
FAILED=0
TOTAL=0

# Test all .v files
find . -name "*.v" -not -path "./archive/*" | sort | while read file; do
    TOTAL=$((TOTAL + 1))
    
    # Quick existence check
    if timeout 30 coqc -R . "" "$file" >/dev/null 2>&1; then
        WORKING=$((WORKING + 1))
        echo "$file" >> working_files.tmp
    else
        FAILED=$((FAILED + 1))
        echo "$file" >> failed_files.tmp
    fi
    
    # Show progress every 10 files
    if [ $((TOTAL % 10)) -eq 0 ]; then
        echo "Progress: $TOTAL files tested..."
    fi
done

# Get final counts
if [ -f working_files.tmp ]; then
    WORKING=$(wc -l < working_files.tmp)
    echo ""
    echo "WORKING FILES:"
    cat working_files.tmp | head -20
    echo "... (showing first 20)"
fi

if [ -f failed_files.tmp ]; then
    FAILED=$(wc -l < failed_files.tmp)
fi

TOTAL=$((WORKING + FAILED))

echo ""
echo "FINAL COUNT:"
echo "Total: $TOTAL"
echo "Working: $WORKING"
echo "Failed: $FAILED"
echo "Success rate: $(( WORKING * 100 / TOTAL ))%"

# Clean up
rm -f working_files.tmp failed_files.tmp