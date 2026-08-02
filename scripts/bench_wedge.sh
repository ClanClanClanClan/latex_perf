#!/usr/bin/env bash
# bench_wedge.sh — R-BENCH: the cold+warm wedge bench, banked.
#
# ROADMAP.md:285 specifies this script by name: "reports COLD and WARM columns at
# every size band; the SLO numbers are tracked artefacts." It did not exist, which
# is why ROADMAP.md:271's baseline table is still the v27.1.57 measurement taken
# BEFORE the R1 fast kernel shipped in v27.1.59.
#
# The two columns are not the same measurement and conflating them is how the
# roadmap's "13.7 s @ 316 KB" got quoted as though it were the product's latency:
#
#   COLD  a full `validators_cli --compile-check` process. Includes ~55 ms of
#         process start, registry and context setup. This is what a user gets
#         today, because R2/R-WARM (the session daemon) is NOT STARTED.
#   WARM  `bench_readiness_kernel` — parse + the 37 compile-blocking rules, with
#         a warmup pass, startup excluded. This is the number the per-keystroke
#         claim rests on, and the one ROADMAP:276 budgets per stage.
#
# Bands are deterministic line-aligned slices of corpora/perf/perf_smoke_big.tex,
# so no duplicate corpus is committed and the bands cannot desync from source.
#
# Usage: bench_wedge.sh [REPS]        (default 11)
set -euo pipefail

REPS=${1:-11}
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/corpora/perf/perf_smoke_big.tex"
CLI="$REPO/_build/default/latex-parse/src/validators_cli.exe"
BENCH="$REPO/_build/default/latex-parse/src/bench_readiness_kernel.exe"
BANDS_KB=(4 50 100 300)

for b in "$CLI" "$BENCH"; do
  [[ -x "$b" ]] || { echo "[wedge] FATAL: not built: $b" >&2; exit 2; }
done
[[ -f "$SRC" ]] || { echo "[wedge] FATAL: missing $SRC" >&2; exit 2; }

TMP=$(mktemp -d "${TMPDIR:-/tmp}/wedge.XXXXXX")
trap 'rm -rf "$TMP"' EXIT

for kb in "${BANDS_KB[@]}"; do
  head -c $((kb * 1000)) "$SRC" | sed '$d' > "$TMP/band_${kb}kb.tex"
  printf '\n\\end{document}\n' >> "$TMP/band_${kb}kb.tex"
done

echo "[wedge] load average at start:$(uptime | sed 's/.*load average[s]*://')"
echo "[wedge] COLD = full CLI process (startup included) | WARM = kernel only"
printf '%8s  %12s  %12s  %12s  %12s\n' band cold_check_ms warm_total_ms warm_parse_ms warm_rules_ms

# WARM: one bench invocation covers every band.
WARM=$("$BENCH" "$REPS" $(for kb in "${BANDS_KB[@]}"; do echo -n "$TMP/band_${kb}kb.tex "; done))

i=0
for kb in "${BANDS_KB[@]}"; do
  i=$((i + 1))
  # COLD: best-of-REPS wall clock of a real process, so startup is included.
  best=""
  for _ in $(seq 1 "$REPS"); do
    s=$(python3 -c "
import subprocess,time,sys
t=time.monotonic(); subprocess.run(sys.argv[1:],capture_output=True); print((time.monotonic()-t)*1000)
" "$CLI" --compile-check "$TMP/band_${kb}kb.tex")
    best=$(python3 -c "print(min(float('${best:-1e9}'), float('$s')))")
  done
  row=$(echo "$WARM" | awk -v n=$i 'NR>1 && $1 ~ /^[0-9]+$/ {c++; if (c==n) {print $2, $4, $3}}')
  read -r wparse wrules wtotal <<< "$row"
  printf '%6dKB  %12.1f  %12.1f  %12.1f  %12.1f\n' \
    "$kb" "$best" "${wtotal:-0}" "${wparse:-0}" "${wrules:-0}"
done

echo "[wedge] NOTE: WARM is what the per-keystroke claim rests on, but no shipped"
echo "[wedge]       path serves it — R2/R-WARM (session daemon) is NOT STARTED, so"
echo "[wedge]       every real invocation today pays the COLD column."
