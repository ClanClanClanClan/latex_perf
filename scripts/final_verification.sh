#!/bin/bash
echo "=== Final System Verification ==="
echo "Timestamp: $(date)"
echo ""

# Track failures
FAILURES=0

# Check 1: Build system
echo "1. Testing build system..."
echo "   Running: make clean"
make clean >/dev/null 2>&1 || { echo "   ❌ Make clean failed"; FAILURES=$((FAILURES + 1)); }
echo "   Running: make -j4 (this may take a moment...)"
make -j4 >/dev/null 2>&1 || { echo "   ❌ Build failed"; FAILURES=$((FAILURES + 1)); }
if [ $FAILURES -eq 0 ]; then
    echo "   ✅ Build system working"
fi

# Check 2: Test framework
echo ""
echo "2. Checking test framework..."
if [ -f "tests/run_all_rule_tests.py" ]; then
    echo "   ✅ Test runner found"
else
    echo "   ❌ Test runner missing"
    FAILURES=$((FAILURES + 1))
fi

# Check 3: Corpus validation
echo ""
echo "3. Validating corpus..."
if python3 corpus/validate_perfect_corpus.py >/dev/null 2>&1; then
    echo "   ✅ Corpus validation passed"
else
    echo "   ❌ Corpus validation failed"
    FAILURES=$((FAILURES + 1))
fi

# Check 4: Documentation
echo ""
echo "4. Checking documentation..."
required_docs=("README.md" "PROJECT_STATUS.md" "docs/unified-vision.md")
for doc in "${required_docs[@]}"; do
    if [[ -f "$doc" ]]; then
        echo "   ✅ $doc found"
    else
        echo "   ❌ Missing required doc: $doc"
        FAILURES=$((FAILURES + 1))
    fi
done

# Check 5: No broken references
echo ""
echo "5. Checking for broken references..."
BROKEN_REFS=$(find . -name "*.v" -o -name "*.py" | xargs grep -l "\.broken\|\.backup\|\.old" 2>/dev/null | grep -v ".cleanup_staging" | wc -l)
if [ $BROKEN_REFS -eq 0 ]; then
    echo "   ✅ No broken references found"
else
    echo "   ❌ Found $BROKEN_REFS files with broken references"
    FAILURES=$((FAILURES + 1))
fi

# Check 6: Essential directories
echo ""
echo "6. Checking essential directories..."
essential_dirs=("src" "core" "tests" "docs" "corpus" "archive" "rules")
for dir in "${essential_dirs[@]}"; do
    if [[ -d "$dir" ]]; then
        echo "   ✅ $dir/ exists"
    else
        echo "   ❌ Missing essential directory: $dir/"
        FAILURES=$((FAILURES + 1))
    fi
done

# Summary
echo ""
echo "=== Verification Summary ==="
if [ $FAILURES -eq 0 ]; then
    echo "✅ ALL CHECKS PASSED - System is healthy!"
else
    echo "❌ FAILURES DETECTED: $FAILURES issues found"
    echo ""
    echo "Consider running restoration if critical failures occurred:"
    echo "  ../LP_v24_FULL_BACKUP_20250716_165548/RESTORE_IF_NEEDED.sh"
fi

exit $FAILURES