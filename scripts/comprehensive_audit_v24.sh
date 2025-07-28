#!/bin/bash

echo "=== LaTeX Perfectionist v24 Comprehensive Audit ==="
echo "Date: $(date)"
echo

# Find all test files
TEST_FILES=$(find . -maxdepth 1 -name "test_*.v" -o -name "tier*.v" -o -name "*_tests.v" | sort)

echo "=== COMPILATION STATUS ==="
echo

# Check compilation status
for file in $TEST_FILES; do
    basename=$(basename "$file")
    if [ -f "${file}o" ]; then
        echo "✓ COMPILED: $basename"
    else
        echo "✗ NOT COMPILED: $basename"
    fi
done

echo
echo "=== ATTEMPTING TO COMPILE KEY TEST FILES ==="
echo

# Try to compile some key test files
KEY_FILES="basic_test.v super_quick_test.v minimal_tests.v test_def_simple.v comprehensive_l1_tests.v"

for file in $KEY_FILES; do
    if [ -f "$file" ]; then
        echo "Attempting to compile: $file"
        if coqc -I core -R . Top "$file" 2>&1 | grep -E "(Error:|error:)" > /dev/null; then
            echo "  ✗ FAILED - Errors found:"
            coqc -I core -R . Top "$file" 2>&1 | grep -E "(Error:|error:)" | head -3
        else
            echo "  ✓ SUCCESS (or timeout)"
        fi
    fi
done

echo
echo "=== CHECKING AUX FILES (PARTIAL COMPILATION) ==="
echo

# Check .aux files for partial compilation
AUX_FILES=$(find . -maxdepth 1 -name ".*.aux" | wc -l)
echo "Found $AUX_FILES .aux files indicating partial compilation attempts"

# Check which test files have non-empty .aux files
for file in $TEST_FILES; do
    basename=$(basename "$file")
    aux_file=".${basename%.v}.aux"
    if [ -f "$aux_file" ] && [ -s "$aux_file" ]; then
        echo "◐ PARTIAL: $basename (has non-empty .aux file)"
    fi
done

echo
echo "=== DEPENDENCY ANALYSIS ==="
echo

# Check what core files are needed
echo "Core files required by test files:"
grep -h "Require Import core\." $TEST_FILES 2>/dev/null | sort | uniq -c | sort -nr

echo
echo "=== SUMMARY ==="
echo

TOTAL=$(echo "$TEST_FILES" | wc -l)
COMPILED=$(ls *.vo 2>/dev/null | grep -E "(test_|tier)" | wc -l)
NOT_COMPILED=$((TOTAL - COMPILED))

echo "Total test files: $TOTAL"
echo "Compiled successfully: $COMPILED"
echo "Not compiled: $NOT_COMPILED"

echo
echo "=== WORKING VS BROKEN ==="
echo

# List of files that should work based on .vo files
echo "CONFIRMED WORKING:"
ls *.vo 2>/dev/null | sed 's/\.vo$/\.v/' | grep -E "(test_|tier)" | sort

echo
echo "LIKELY BROKEN:"
for file in $TEST_FILES; do
    basename=$(basename "$file")
    if [ ! -f "${file}o" ]; then
        echo "- $basename"
    fi
done