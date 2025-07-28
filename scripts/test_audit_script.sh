#!/bin/bash

# Test compilation audit script
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
    "tier1_ultimate_hardcore_tests.v"
    "ultimate_maniac_tests.v"
    "rules/phase1/RuleTests.v"
    "tests/LatexLexerTests.v"
    "tests/TestLexerDemo.v"
    "tests/TestSpaces.v"
    "tests/audit_test.v"
    "SUCCESS_TESTS.v"
    "SUCCESS_COMPLETE.v"
    "VERIFICATION_COMPLETE.v"
    "HELL_LEVEL_TESTS.v"
    "EXTREME_PARANOID_TESTS.v"
    "ACTUAL_HELL_LEVEL_TESTS.v"
    "maniac_tests.v"
    "comprehensive_l1_tests.v"
)

# Statistics
total_files=0
compiled_files=0
timeout_files=0
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
    
    # Try compilation with timeout
    if timeout 30s coqc -R . "" "$file" > /dev/null 2>&1; then
        echo "  Status: COMPILED SUCCESSFULLY"
        compiled_files=$((compiled_files + 1))
    else
        exit_code=$?
        if [[ $exit_code -eq 124 ]]; then
            echo "  Status: TIMEOUT (>30s)"
            timeout_files=$((timeout_files + 1))
        else
            echo "  Status: COMPILATION ERROR"
            error_files=$((error_files + 1))
            # Show error details
            echo "  Error details:"
            timeout 5s coqc -R . "" "$file" 2>&1 | head -3 | sed 's/^/    /'
        fi
    fi
    echo
done

echo "=== SUMMARY ==="
echo "Total files tested: $total_files"
echo "Successfully compiled: $compiled_files"
echo "Timed out (>30s): $timeout_files"
echo "Compilation errors: $error_files"
echo
echo "Success rate: $(echo "scale=1; $compiled_files * 100 / $total_files" | bc -l)%"