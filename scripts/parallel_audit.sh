#!/bin/bash

echo "⚡ PARALLEL AUDIT - Fast compilation check"
echo "========================================="

# Clean previous results
rm -f working_files.txt broken_files.txt

# Build core first
echo "📦 Building core dependencies..."
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1 &
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1 &
coqc -R . "" ValidationTypes.v >/dev/null 2>&1 &
wait

echo "🔍 Testing all files in parallel..."

# Function to test a file
test_file() {
    local file=$1
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "$file" >> working_files.txt
    else
        echo "$file" >> broken_files.txt
    fi
}

export -f test_file

# Run tests in parallel
find . -name "*.v" -not -path "./archive/*" | xargs -P 8 -I {} bash -c 'test_file "$@"' _ {}

# Wait for all to complete
wait

# Count results
TOTAL=$(find . -name "*.v" -not -path "./archive/*" | wc -l)
WORKING=$(cat working_files.txt 2>/dev/null | wc -l || echo 0)
BROKEN=$(cat broken_files.txt 2>/dev/null | wc -l || echo 0)

echo ""
echo "📊 RESULTS:"
echo "   Total: $TOTAL files"
echo "   ✅ Working: $WORKING"
echo "   ❌ Broken: $BROKEN"
echo "   Success rate: $((WORKING * 100 / TOTAL))%"

echo ""
echo "🔍 Sample of broken files:"
head -10 broken_files.txt 2>/dev/null || echo "No broken files!"