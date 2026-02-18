#!/usr/bin/env bash
# CI gate: parse eval JSON and fail if F1 < 0.94.
# Usage: bash ml/scripts/f1_gate.sh [eval_results.json]
set -euo pipefail

EVAL_FILE="${1:-ml/eval_results.json}"
THRESHOLD="0.94"

if [ ! -f "$EVAL_FILE" ]; then
    echo "ERROR: Evaluation file not found: $EVAL_FILE"
    exit 1
fi

# Extract F1 using Python (portable, no jq dependency)
F1=$(python3 -c "
import json, sys
with open('$EVAL_FILE') as f:
    d = json.load(f)
print(d.get('overall_f1', 0.0))
")

DELTA=$(python3 -c "
import json
with open('$EVAL_FILE') as f:
    d = json.load(f)
print(d.get('delta', 1.0))
")

MODEL=$(python3 -c "
import json
with open('$EVAL_FILE') as f:
    d = json.load(f)
print(d.get('model', 'unknown'))
")

echo "=== F1 Gate Check ==="
echo "File: $EVAL_FILE"
echo "Model: $MODEL"
echo "F1: $F1"
echo "Delta: $DELTA"
echo "Threshold: $THRESHOLD"

# Compare using Python for float comparison
PASS=$(python3 -c "print('PASS' if float('$F1') >= float('$THRESHOLD') else 'FAIL')")

if [ "$PASS" = "PASS" ]; then
    echo "RESULT: PASS (F1 $F1 >= $THRESHOLD)"
    exit 0
else
    echo "RESULT: FAIL (F1 $F1 < $THRESHOLD)"
    exit 1
fi
