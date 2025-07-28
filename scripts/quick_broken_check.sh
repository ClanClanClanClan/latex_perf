#!/bin/bash

echo "🔍 QUICK CHECK FOR BROKEN FILES"
echo "=============================="

# Build core first
coqc -R . "" core/LatexCatcodes.v >/dev/null 2>&1
coqc -R . "" core/LatexLexer.v >/dev/null 2>&1
coqc -R . "" ValidationTypes.v >/dev/null 2>&1

# Check files that reference LatexExpanderUltimate
echo ""
echo "Files using LatexExpanderUltimate:"
grep -l "LatexExpanderUltimate" *.v 2>/dev/null | while read file; do
    echo -n "  $file: "
    if coqc -R . "" "$file" >/dev/null 2>&1; then
        echo "✅"
    else
        echo "❌"
    fi
done

# Check other potentially broken files
echo ""
echo "Other test files status:"
for file in test_*.v debug_*.v tier*.v; do
    if [ -f "$file" ]; then
        echo -n "  $file: "
        if timeout 5 coqc -R . "" "$file" >/dev/null 2>&1; then
            echo "✅"
        else
            echo "❌"
        fi
    fi
done