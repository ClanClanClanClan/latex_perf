#!/bin/bash
set -e

echo "🔍 AUTOMATIC CLAIM VERIFICATION STARTING..."
echo "========================================"

VERIFICATION_FAILED=0

# 1. Compilation Check
echo "📝 Checking compilation..."
COMPILE_FAILURES=0
for file in *.v core/*.v; do
    if [ -f "$file" ]; then
        echo "   Compiling: $file"
        if ! coqc -I . -I core -I rules -R . "" "$file" >/dev/null 2>&1; then
            echo "   ❌ COMPILATION FAILED: $file"
            COMPILE_FAILURES=$((COMPILE_FAILURES + 1))
            VERIFICATION_FAILED=1
        fi
    fi
done

if [ $COMPILE_FAILURES -eq 0 ]; then
    echo "✅ All files compile successfully"
else
    echo "❌ $COMPILE_FAILURES files failed to compile"
fi

# 2. TODO Audit
echo ""
echo "🔍 Checking for incomplete code..."
TODOS=$(find . -name "*.v" -exec grep -l "TODO\|FIXME\|XXX\|HACK\|INCOMPLETE" {} \; 2>/dev/null | wc -l)
TODO_COUNT=$(find . -name "*.v" -exec grep -c "TODO\|FIXME\|XXX\|HACK\|INCOMPLETE" {} \; 2>/dev/null | awk '{sum+=$1} END {print sum+0}')

if [ "$TODO_COUNT" -gt 0 ]; then
    echo "❌ FOUND $TODO_COUNT INCOMPLETE IMPLEMENTATIONS:"
    find . -name "*.v" -exec grep -H "TODO\|FIXME\|XXX\|HACK\|INCOMPLETE" {} \; 2>/dev/null
    VERIFICATION_FAILED=1
else
    echo "✅ No incomplete code markers found"
fi

# 3. Test Coverage Analysis
echo ""
echo "📊 Verifying test coverage..."
TEST_FILES=$(find . -name "*test*.v" -o -name "*Test*.v" 2>/dev/null)
TOTAL_TESTS=0

if [ -z "$TEST_FILES" ]; then
    echo "❌ NO TEST FILES FOUND"
    VERIFICATION_FAILED=1
else
    for test_file in $TEST_FILES; do
        if [ -f "$test_file" ]; then
            TEST_COUNT=$(grep -c "Example\|Compute\|Theorem\|Lemma" "$test_file" 2>/dev/null || echo 0)
            TOTAL_TESTS=$((TOTAL_TESTS + TEST_COUNT))
            echo "   📊 $test_file: $TEST_COUNT tests"
            if [ "$TEST_COUNT" -lt 5 ]; then
                echo "   ⚠️  LOW TEST COVERAGE: $test_file"
            fi
        fi
    done
    echo "   📊 TOTAL TESTS: $TOTAL_TESTS"
fi

# 4. Feature Implementation Check
echo ""
echo "🎯 Verifying claimed features exist in code..."
FEATURES=("renewcommand" "providecommand" "let" "warning" "debug")
MISSING_FEATURES=0

for feature in "${FEATURES[@]}"; do
    if find . -name "*.v" -exec grep -l "$feature" {} \; >/dev/null 2>&1; then
        echo "   ✅ Found: $feature"
    else
        echo "   ❌ MISSING FEATURE: $feature"
        MISSING_FEATURES=$((MISSING_FEATURES + 1))
        VERIFICATION_FAILED=1
    fi
done

# 5. Documentation Assessment
echo ""
echo "📚 Checking documentation..."
DOC_SCORE=0
if [ -f "README.md" ]; then
    echo "   ✅ README.md exists"
    DOC_SCORE=$((DOC_SCORE + 1))
else
    echo "   ❌ README.md missing"
fi

if [ -f "DOCUMENTATION.md" ] || [ -f "docs/" ]; then
    echo "   ✅ Additional documentation found"
    DOC_SCORE=$((DOC_SCORE + 1))
else
    echo "   ❌ No additional documentation"
fi

# 6. File Organization Check
echo ""
echo "📁 Checking project organization..."
REQUIRED_DIRS=("core" "rules")
ORG_ISSUES=0

for dir in "${REQUIRED_DIRS[@]}"; do
    if [ -d "$dir" ]; then
        FILE_COUNT=$(find "$dir" -name "*.v" | wc -l)
        echo "   ✅ $dir/ exists with $FILE_COUNT .v files"
    else
        echo "   ❌ Missing directory: $dir/"
        ORG_ISSUES=$((ORG_ISSUES + 1))
    fi
done

# Final Assessment
echo ""
echo "========================================"
echo "🎯 VERIFICATION SUMMARY"
echo "========================================"

if [ $VERIFICATION_FAILED -eq 0 ]; then
    echo "✅ BASIC VERIFICATION PASSED"
    echo ""
    echo "📊 METRICS:"
    echo "   • Compilation: PASS"
    echo "   • TODO count: $TODO_COUNT"
    echo "   • Total tests: $TOTAL_TESTS"
    echo "   • Features found: $((${#FEATURES[@]} - MISSING_FEATURES))/${#FEATURES[@]}"
    echo "   • Documentation: $DOC_SCORE/2"
    echo ""
    echo "✅ SAFE TO MAKE CONSERVATIVE CLAIMS"
    echo ""
    echo "📋 RECOMMENDED HONEST LANGUAGE:"
    echo "   • 'Basic implementation of key features'"
    echo "   • 'Foundation for enterprise development'"
    echo "   • 'Working prototype with $TOTAL_TESTS tests'"
    echo "   • 'Functional but requires additional development'"
else
    echo "❌ VERIFICATION FAILED"
    echo ""
    echo "🚫 DO NOT MAKE COMPLETION CLAIMS"
    echo "🚫 DO NOT CLAIM 'PRODUCTION READY'"
    echo "🚫 DO NOT CLAIM 'ENTERPRISE READY'"
    echo ""
    echo "📋 ISSUES TO FIX:"
    [ $COMPILE_FAILURES -gt 0 ] && echo "   • Fix $COMPILE_FAILURES compilation failures"
    [ $TODO_COUNT -gt 0 ] && echo "   • Complete $TODO_COUNT TODO items"
    [ $MISSING_FEATURES -gt 0 ] && echo "   • Implement $MISSING_FEATURES missing features"
    [ -z "$TEST_FILES" ] && echo "   • Add comprehensive test files"
fi

echo ""
echo "⚠️  MANUAL VERIFICATION STILL REQUIRED:"
echo "   • Actually run and test claimed functionality"
echo "   • Test with realistic inputs and edge cases"
echo "   • Verify performance under load"
echo "   • Check error handling and recovery"
echo ""

exit $VERIFICATION_FAILED