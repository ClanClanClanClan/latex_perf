#!/usr/bin/env bash
# Differential validation of --compile-check against the real pdflatex engine.
#
# Runs `validators_cli --compile-check` and real `pdflatex` on a labeled corpus
# and prints the confusion matrix. The point is to MEASURE (not assume) the
# readiness pre-check's soundness:
#   - FALSE READY  (cc=READY  but pdflatex FAILS)  = DANGEROUS (pre-check missed a
#                                                     real failure). Must be rare;
#                                                     each is a documented limit.
#   - FALSE NOT-READY (cc=NOT-READY but pdflatex COMPILES) = SAFE over-rejection
#                                                     (conservative by design).
#
# Requires pdflatex on PATH (skips gracefully if absent). Not a CI gate (CI has
# no TeX); run locally after touching compile_contract.ml.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CLI="$ROOT/_build/default/latex-parse/src/validators_cli.exe"
CORPUS="${1:-$ROOT/corpora/compile_check}"
export L0_VALIDATORS=pilot

if ! command -v pdflatex >/dev/null 2>&1; then
  echo "[diff-compile-check] SKIP: pdflatex not on PATH"; exit 0
fi
if [ ! -x "$CLI" ]; then
  echo "[diff-compile-check] building CLI..."; (cd "$ROOT" && opam exec -- dune build latex-parse/src/validators_cli.exe) || exit 1
fi

tp=0; tn=0; false_ready=0; false_notready=0; total=0
printf '%-26s | %-10s | %-9s | %s\n' "file" "compile-check" "pdflatex" "class"
printf -- '---------------------------+------------+-----------+------\n'
for f in "$CORPUS"/*.tex; do
  [ -e "$f" ] || continue
  total=$((total+1))
  if "$CLI" --compile-check "$f" >/dev/null 2>&1; then cc=READY; else cc=NOT-READY; fi
  d=$(mktemp -d); cp "$f" "$d/"
  if (cd "$d" && pdflatex -interaction=nonstopmode -halt-on-error "$(basename "$f")" >/dev/null 2>&1); then pl=COMPILES; else pl=FAILS; fi
  rm -rf "$d"
  cls=ok
  if   [ "$cc" = READY ]     && [ "$pl" = FAILS ];    then cls="FALSE-READY";     false_ready=$((false_ready+1))
  elif [ "$cc" = NOT-READY ] && [ "$pl" = COMPILES ]; then cls="false-not-ready"; false_notready=$((false_notready+1))
  elif [ "$cc" = READY ]     && [ "$pl" = COMPILES ]; then tp=$((tp+1))
  else tn=$((tn+1)); fi
  printf '%-26s | %-10s | %-9s | %s\n' "$(basename "$f")" "$cc" "$pl" "$cls"
done
echo
echo "[diff-compile-check] total=$total  READY&compiles=$tp  NOT-READY&fails=$tn"
echo "[diff-compile-check] FALSE-READY (dangerous, pre-check missed)=$false_ready"
echo "[diff-compile-check] false-not-ready (safe over-reject)=$false_notready"
# Non-zero exit ONLY on a dangerous false-READY (the soundness direction that matters).
[ "$false_ready" -eq 0 ]
