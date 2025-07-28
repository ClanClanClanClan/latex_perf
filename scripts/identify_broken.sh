#!/bin/bash

echo "IDENTIFYING ALL BROKEN FILES"
echo "============================"

# Clear previous results
rm -f broken_files.txt working_files.txt

# Build core dependencies first
echo "Building core dependencies..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

# Test each file
find . -name "*.v" -not -path "./archive/*" | sort | while read file; do
    echo -n "Testing $file... "
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅"
        echo "$file" >> working_files.txt
    else
        echo "❌"
        echo "$file" >> broken_files.txt
        # Capture error for analysis
        echo "=== $file ===" >> broken_errors.txt
        coqc -R . "" "$file" 2>&1 | head -5 >> broken_errors.txt
        echo "" >> broken_errors.txt
    fi
done

echo ""
echo "SUMMARY:"
if [ -f working_files.txt ]; then
    WORKING=$(wc -l < working_files.txt)
else
    WORKING=0
fi

if [ -f broken_files.txt ]; then
    BROKEN=$(wc -l < broken_files.txt)
else
    BROKEN=0
fi

echo "Working: $WORKING"
echo "Broken: $BROKEN"
echo ""
echo "Broken files saved to: broken_files.txt"
echo "Error details saved to: broken_errors.txt"