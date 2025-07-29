#!/bin/bash

# Simple test compilation audit script
echo "=== LaTeX Perfectionist v24 Test Compilation Audit ==="
echo "Date: $(date)"
echo

# Test files to check
test_files=(
    "basic_test.v"
    "quick_test.v"
    "super_quick_test.v"
    "ultra_minimal_tests.v"
    "minimal_tests.v"
    "tier1_tests_simple.v"
    "rules/phase1/RuleTests.v"
    "tests/LatexLexerTests.v"
    "tests/TestLexerDemo.v"
    "tests/TestSpaces.v"
    "tests/audit_test.v"
    "SUCCESS_TESTS.v"
    "SUCCESS_COMPLETE.v"
    "VERIFICATION_COMPLETE.v"
)

# Statistics
total_files=0
compiled_files=0
error_files=0

echo "Testing compilation of key test files..."
echo

for file in "${test_files[@]}"; do
    total_files=$((total_files + 1))
    echo "Testing: $file"
    
    if [[ ! -f "$file" ]]; then
        echo "  Status: FILE NOT FOUND"
        error_files=$((error_files + 1))
        continue
    fi
    
    # Try compilation
    if coqc -R . "" "$file" > /dev/null 2>&1; then
        echo "  Status: COMPILED SUCCESSFULLY"
        compiled_files=$((compiled_files + 1))
    else
        echo "  Status: COMPILATION ERROR"
        error_files=$((error_files + 1))
        # Show error details
        echo "  Error details:"
        coqc -R . "" "$file" 2>&1 | head -2 | sed 's/^/    /'
    fi
    echo
done

echo "=== SUMMARY ==="
echo "Total files tested: $total_files"
echo "Successfully compiled: $compiled_files"
echo "Compilation errors: $error_files"
echo
echo "Success rate: $((compiled_files * 100 / total_files))%"