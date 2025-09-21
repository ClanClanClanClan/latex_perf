#!/bin/bash
set -euo pipefail

LATENCIES="${1:-/tmp/latencies_ms.txt}"
TAIL_CSV="${2:-/tmp/l0_service_tail.csv}"

if [[ ! -f "$LATENCIES" ]]; then
    echo "[gate] ERROR: Missing latencies file: $LATENCIES"
    exit 1
fi

# Compute percentiles
N=$(wc -l < "$LATENCIES" | tr -d ' ')
if [[ $N -lt 100 ]]; then
    echo "[gate] ERROR: Too few samples: $N < 100"
    exit 1
fi

# Sort the latencies
sort -n "$LATENCIES" > /tmp/sorted_latencies.txt

# Calculate percentile indices
P50_IDX=$((N * 50 / 100))
P95_IDX=$((N * 95 / 100))
P99_IDX=$((N * 99 / 100))
P999_IDX=$((N * 999 / 1000))

# Get percentile values
P50=$(sed -n "${P50_IDX}p" /tmp/sorted_latencies.txt)
P95=$(sed -n "${P95_IDX}p" /tmp/sorted_latencies.txt)
P99=$(sed -n "${P99_IDX}p" /tmp/sorted_latencies.txt)
P999=$(sed -n "${P999_IDX}p" /tmp/sorted_latencies.txt)

echo "[gate] Percentiles (ms):"
echo "  P50:  $P50"
echo "  P95:  $P95"
echo "  P99:  $P99"
echo "  P99.9: $P999"

# Check acceptance criteria
PASS=true

# P95 < 20ms gate (Tier A)
if (( $(echo "$P95 > 20" | bc -l) )); then
    echo "[gate] FAIL: P95 = ${P95}ms > 20ms"
    PASS=false
fi

# P99.9 < 40ms gate
if (( $(echo "$P999 > 40" | bc -l) )); then
    echo "[gate] FAIL: P99.9 = ${P999}ms > 40ms"
    PASS=false
fi

# Check tail behavior if CSV exists
if [[ -f "$TAIL_CSV" ]]; then
    # ms_total is the first column
    TAIL_MAX=$(tail -n +2 "$TAIL_CSV" | cut -d, -f1 | sort -rn | head -1)
    echo "[gate] Tail max: ${TAIL_MAX}ms"

    if (( $(echo "$TAIL_MAX > 100" | bc -l) )); then
        echo "[gate] WARNING: Tail max = ${TAIL_MAX}ms > 100ms"
    fi
fi

if $PASS; then
    echo "[gate] PASS: All criteria met"
    exit 0
else
    echo "[gate] FAIL: Performance gate not met"
    exit 1
fi
