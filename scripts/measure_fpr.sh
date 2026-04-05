#!/usr/bin/env bash
# ══════════════════════════════════════════════════════════════════════
# measure_fpr.sh — False Positive Rate baseline measurement
#
# Runs all validators on a "clean" corpus (documents known to have
# zero violations) and counts how many rules fire (false positives).
#
# Usage: bash scripts/measure_fpr.sh [corpus_dir]
# Default corpus: corpora/perf/ (performance corpus, expected clean)
#
# FPR = (files with false fires) / (total files)
# Per-rule FPR = (times rule fires on clean files) / (total clean files)
#
# Spec target: FPR ≤ 0.1% (§1.2 of v25_master.md)
# ══════════════════════════════════════════════════════════════════════
set -euo pipefail

CORPUS_DIR="${1:-corpora/perf}"
VALIDATOR_CLI="./_build/default/latex-parse/src/validators_cli.exe"

echo "═══════════════════════════════════════════════════════"
echo "FPR Baseline Measurement"
echo "Corpus: $CORPUS_DIR"
echo "═══════════════════════════════════════════════════════"

# Build if needed
if [ ! -f "$VALIDATOR_CLI" ]; then
    echo "Building validators..."
    opam exec -- dune build latex-parse/src/validators_cli.exe 2>/dev/null || {
        echo "ERROR: dune build failed"
        exit 2
    }
fi

# Count files
TOTAL=0
FILES_WITH_FIRES=0
TOTAL_FIRES=0
RULE_FIRES=""

for tex_file in "$CORPUS_DIR"/*.tex; do
    [ -f "$tex_file" ] || continue
    TOTAL=$((TOTAL + 1))

    # Run validators on this file
    FIRES=$(L0_VALIDATORS=pilot "$VALIDATOR_CLI" "$tex_file" 2>/dev/null | grep -c "^" || true)

    if [ "$FIRES" -gt 0 ]; then
        FILES_WITH_FIRES=$((FILES_WITH_FIRES + 1))
        TOTAL_FIRES=$((TOTAL_FIRES + FIRES))

        # Collect per-rule fires
        RULES=$(L0_VALIDATORS=pilot "$VALIDATOR_CLI" "$tex_file" 2>/dev/null | awk -F: '{print $1}' || true)
        RULE_FIRES="$RULE_FIRES $RULES"
    fi
done

if [ "$TOTAL" -eq 0 ]; then
    echo "ERROR: no .tex files found in $CORPUS_DIR"
    exit 1
fi

# Calculate FPR
FPR=$(echo "scale=4; $FILES_WITH_FIRES * 100 / $TOTAL" | bc)

echo ""
echo "Results:"
echo "  Total files:        $TOTAL"
echo "  Files with fires:   $FILES_WITH_FIRES"
echo "  Total fires:        $TOTAL_FIRES"
echo "  FPR (file-level):   ${FPR}%"
echo ""

# Per-rule breakdown
if [ -n "$RULE_FIRES" ]; then
    echo "Per-rule fires on clean corpus:"
    echo "$RULE_FIRES" | tr ' ' '\n' | sort | uniq -c | sort -rn | head -20
fi

echo ""
if [ "$(echo "$FPR < 0.1" | bc)" -eq 1 ]; then
    echo "PASS: FPR ${FPR}% < 0.1% target"
else
    echo "FAIL: FPR ${FPR}% >= 0.1% target"
    exit 1
fi
