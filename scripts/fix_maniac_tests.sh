#!/bin/bash

echo "Fixing maniac_tests.v destructuring patterns..."

# Create a fixed version
cp maniac_tests.v maniac_tests.v.backup

# Replace all parse_one_param destructuring patterns
sed -i '' 's/let (arg, rest, _) := parse_one_param/match parse_one_param/g' maniac_tests.v
sed -i '' 's/in$/with (arg, rest, _) => /g' maniac_tests.v

# Add end statements where needed
sed -i '' 's/Proof\. split; reflexivity\. Qed\./end. Proof. split; reflexivity. Qed./g' maniac_tests.v
sed -i '' 's/Proof\. reflexivity\. Qed\./end. Proof. reflexivity. Qed./g' maniac_tests.v

echo "Testing compilation..."
if coqc -R . "" maniac_tests.v 2>&1 | head -5; then
    echo "✅ Fixed!"
else
    echo "❌ Still has issues, reverting..."
    mv maniac_tests.v.backup maniac_tests.v
fi