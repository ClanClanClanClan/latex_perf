#!/usr/bin/env bash
# bench_compile_check.sh — wall-clock benchmark of the FAST readiness kernel
# (--compile-check) vs the FULL path (--compile-check-full) on real papers.
#
# The fast kernel (compile_contract.ml, v27.1.59) parses once and runs only the
# ~37 compile-blocking rules; the full path parses twice and runs all ~641 rules
# then filters. Both must produce the byte-identical verdict — this script
# asserts that too.
#
# Usage: bench_compile_check.sh <cli.exe> <file1.tex> [file2.tex ...]
# Env:   REPS (default 9) — timed repetitions per path (median reported).
#
# Copy papers to LOCAL disk before timing to exclude network/Dropbox read cost,
# and this script warms the binary once per file before timing.
set -euo pipefail

CLI="${1:?usage: bench_compile_check.sh <cli.exe> <file.tex>...}"
shift
REPS="${REPS:-9}"

# median of stdin numbers
median() { sort -n | awk '{a[NR]=$1} END{print (NR%2)?a[(NR+1)/2]:(a[NR/2]+a[NR/2+1])/2}'; }

# wall-clock ms of one invocation
time_ms() {
  local t0 t1
  t0=$(python3 -c 'import time;print(time.time())')
  "$@" >/dev/null 2>&1 || true
  t1=$(python3 -c 'import time;print(time.time())')
  python3 -c "print(f'{($t1-$t0)*1000:.1f}')"
}

printf '%-10s %-12s %-12s %-10s %s\n' "size" "full_ms" "fast_ms" "speedup" "verdict_match"
for f in "$@"; do
  sz=$(stat -f '%z' "$f" 2>/dev/null || stat -c '%s' "$f")
  # verdict parity (normalise the filename line out)
  vf_full=$("$CLI" --compile-check-full "$f" 2>&1 | grep -E '^  T[0-5]' || true)
  vf_fast=$("$CLI" --compile-check "$f" 2>&1 | grep -E '^  T[0-5]' || true)
  [ "$vf_full" = "$vf_fast" ] && match="OK" || match="MISMATCH"

  # warm
  "$CLI" --compile-check "$f" >/dev/null 2>&1 || true
  "$CLI" --compile-check-full "$f" >/dev/null 2>&1 || true

  full=$(for _ in $(seq "$REPS"); do time_ms "$CLI" --compile-check-full "$f"; done | median)
  fast=$(for _ in $(seq "$REPS"); do time_ms "$CLI" --compile-check "$f"; done | median)
  speed=$(python3 -c "print(f'{$full/$fast:.1f}x')")
  printf '%-10s %-12s %-12s %-10s %s\n' "$sz" "$full" "$fast" "$speed" "$match"
done
