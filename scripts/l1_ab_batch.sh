#!/usr/bin/env bash
set -euo pipefail

# Batch A/B for L1 (opt-in). Requires core/l1_expander enabled.
# Usage: l1_ab_batch.sh OUT.csv [FILES...]

OUT=${1:-l1_ab_batch.csv}
shift || true

if [[ ! -x ./_build/default/core/l1_expander/l1_ab_test.exe ]]; then
  echo "[l1-batch] L1 not built. Enable via: OPAMSWITCH=l0-testing opam exec -- bash scripts/enable_l1.sh" >&2
  exit 2
fi

echo "file,ctrl_a,text_a,ctrl_b,text_b,equal" > "$OUT"
MISM=/tmp/l1_ab_mismatches.csv
echo "file,ctrl_a,text_a,ctrl_b,text_b" > "$MISM"

if [[ $# -eq 0 ]]; then
  set -- corpora/perf/edit_window_4kb.tex corpora/perf/perf_smoke_big.tex
fi

for f in "$@"; do
  if [[ -f "$f" ]]; then
    ./_build/default/core/l1_expander/l1_ab_test.exe "$f" --csv /tmp/l1_tmp.csv >/dev/null
    tail -n +2 /tmp/l1_tmp.csv >> "$OUT"
    # Append mismatches (equal=false)
    awk -F, 'NR>1 && $6!="true"{print $1","$2","$3","$4","$5}' /tmp/l1_tmp.csv >> "$MISM" || true
  else
    echo "[l1-batch] WARN: missing $f" >&2
  fi
done

echo "[l1-batch] wrote $OUT" >&2
echo "[l1-batch] mismatches (if any): $MISM" >&2
