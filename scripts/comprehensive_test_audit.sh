#!/bin/bash

# Comprehensive Test Execution Audit for LaTeX Perfectionist v24
echo "========================================================================="
echo "LaTeX Perfectionist v24 - Comprehensive Test Execution Audit"
echo "Date: $(date)"
echo "========================================================================="
echo

# Categories to analyze
declare -A TEST_CATEGORIES
TEST_CATEGORIES[basic]="basic_test.v quick_test.v super_quick_test.v ultra_minimal_tests.v"
TEST_CATEGORIES[core_tests]="tests/LatexLexerTests.v tests/TestLexerDemo.v tests/TestSpaces.v tests/audit_test.v"
TEST_CATEGORIES[rule_tests]="rules/phase1/RuleTests.v rules/phase1_5/PostExpansionRules.v"
TEST_CATEGORIES[minimal_verification]="minimal_tests.v SUCCESS_TESTS.v SUCCESS_COMPLETE.v VERIFICATION_COMPLETE.v"
TEST_CATEGORIES[tier1_tests]="tier1_tests_simple.v tier1_ultimate_hardcore_tests.v tier1_verified_tests.v"
TEST_CATEGORIES[comprehensive]="ultimate_maniac_tests.v comprehensive_l1_tests.v maniac_tests.v"
TEST_CATEGORIES[extreme]="HELL_LEVEL_TESTS.v EXTREME_PARANOID_TESTS.v ACTUAL_HELL_LEVEL_TESTS.v"

# Audit statistics
total_files=0
successful_compilations=0
timeout_compilations=0
error_compilations=0
files_with_compute=0
files_with_examples=0
files_with_theorems=0

echo "PHASE 1: COMPILATION TESTING"
echo "============================="
echo

# Test each category
for category in "${!TEST_CATEGORIES[@]}"; do
    echo "Testing Category: $category"
    echo "Files: ${TEST_CATEGORIES[$category]}"
    echo
    
    for file in ${TEST_CATEGORIES[$category]}; do
        total_files=$((total_files + 1))
        echo "  Testing: $file"
        
        if [[ ! -f "$file" ]]; then
            echo "    Status: FILE NOT FOUND"
            error_compilations=$((error_compilations + 1))
            continue
        fi
        
        # Try compilation with manual timeout simulation
        start_time=$(date +%s)
        if coqc -R . "" "$file" > /tmp/compile_output_$$ 2>&1; then
            end_time=$(date +%s)
            duration=$((end_time - start_time))
            
            if [[ $duration -gt 60 ]]; then
                echo "    Status: COMPILED (SLOW - ${duration}s)"
                timeout_compilations=$((timeout_compilations + 1))
            else
                echo "    Status: COMPILED SUCCESSFULLY (${duration}s)"
                successful_compilations=$((successful_compilations + 1))
            fi
        else
            echo "    Status: COMPILATION ERROR"
            error_compilations=$((error_compilations + 1))
            echo "    Error details:"
            head -3 /tmp/compile_output_$$ | sed 's/^/      /'
        fi
        rm -f /tmp/compile_output_$$
    done
    echo
done

echo "PHASE 2: EXECUTABLE CONTENT ANALYSIS"
echo "====================================="
echo

# Check for executable content in all test files
echo "Analyzing executable test content..."
echo

# Find all test files (excluding archive)
test_files=$(find . -name "*.v" -not -path "./archive/*" | grep -E "(test|Test|debug|tier|maniac|SUCCESS|HELL|EXTREME|VERIFICATION|minimal|quick)" | sort)

for file in $test_files; do
    if [[ -f "$file" ]]; then
        # Count different types of executable content
        compute_count=$(grep -c "Compute\|Eval" "$file" 2>/dev/null || echo 0)
        example_count=$(grep -c "Example" "$file" 2>/dev/null || echo 0)
        theorem_count=$(grep -c "Theorem\|Lemma" "$file" 2>/dev/null || echo 0)
        
        if [[ $compute_count -gt 0 ]]; then
            files_with_compute=$((files_with_compute + 1))
            echo "  $file: $compute_count Compute/Eval statements"
        fi
        
        if [[ $example_count -gt 0 ]]; then
            files_with_examples=$((files_with_examples + 1))
            echo "  $file: $example_count Example proofs"
        fi
        
        if [[ $theorem_count -gt 0 ]]; then
            files_with_theorems=$((files_with_theorems + 1))
            echo "  $file: $theorem_count Theorem/Lemma proofs"
        fi
    fi
done

echo
echo "PHASE 3: DEPENDENCY ANALYSIS"
echo "============================="
echo

# Check common compilation failures
echo "Common compilation failure patterns:"
echo

# Check for import issues
grep -r "Cannot find a physical path" . --include="*.v" 2>/dev/null | head -5 | sed 's/^/  /'

echo
echo "FINAL AUDIT SUMMARY"
echo "==================="
echo "Total test files examined: $total_files"
echo "Successfully compiled: $successful_compilations"
echo "Timed out (>60s): $timeout_compilations"
echo "Compilation errors: $error_compilations"
echo
echo "Executable Content Analysis:"
echo "Files with Compute/Eval statements: $files_with_compute"
echo "Files with Example proofs: $files_with_examples"  
echo "Files with Theorem/Lemma proofs: $files_with_theorems"
echo
echo "Overall Compilation Success Rate: $(echo "scale=1; $successful_compilations * 100 / $total_files" | bc -l 2>/dev/null || echo "N/A")%"

# Determine test readiness
if [[ $successful_compilations -gt $((total_files / 2)) ]]; then
    echo "Assessment: BASIC test infrastructure is working"
else
    echo "Assessment: SIGNIFICANT compilation issues detected"
fi

if [[ $files_with_compute -gt 5 && $files_with_examples -gt 5 ]]; then
    echo "Test Coverage: COMPREHENSIVE executable tests available"
elif [[ $files_with_compute -gt 0 && $files_with_examples -gt 0 ]]; then
    echo "Test Coverage: BASIC executable tests available"
else
    echo "Test Coverage: LIMITED executable test coverage"
fi