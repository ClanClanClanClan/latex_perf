#!/usr/bin/env bash
# Differential validation of --compile-check against the real pdflatex engine.
#
# Runs `validators_cli --compile-check` and real `pdflatex` on a labeled corpus
# and prints the confusion matrix. The point is to MEASURE (not assume) the
# readiness pre-check's soundness at scale:
#   - FALSE READY  (cc=READY  but pdflatex FAILS)  = DANGEROUS (pre-check missed a
#                                                     real failure). This is the
#                                                     soundness residual; each one
#                                                     is a documented limit-class.
#   - FALSE NOT-READY (cc=NOT-READY but pdflatex COMPILES) = SAFE over-rejection
#                                                     (conservative by design).
#
# Classification is OUTCOME-driven (from the two real verdicts), NOT from the
# filename. Filenames (good_/fail_/tolerated_) are documentation only.
#
# Regression contract (issue 3): the harness exits NONZERO only on a NEW
# false-READY, i.e. a false-READY file whose basename is NOT in the documented
# allowlist KNOWN_FALSE_READY below. Known-limitation false-READYs (undefined
# control sequences, missing packages, semantic errors requiring full macro
# expansion — things the pre-check provably cannot catch without modeling the
# whole macro universe) are expected and do NOT fail the run; a genuinely new
# soundness miss does.
#
# Requires pdflatex on PATH (skips gracefully if absent). Not a CI gate (CI has
# no TeX); run locally after touching compile_contract.ml or the corpus.
#
# Usage: diff_compile_check.sh [CORPUS_DIR]
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CLI="$ROOT/_build/default/latex-parse/src/validators_cli.exe"
CORPUS="${1:-$ROOT/corpora/compile_check}"
export L0_VALIDATORS=pilot

# --- Documented allowlist of KNOWN false-READY classes ------------------------
# These are the measured soundness residual: docs the pre-check reports READY
# but pdflatex FAILS, for reasons the pre-check provably cannot detect without
# modeling the full macro/package universe (undefined control sequences, missing
# \usepackage, arg-count/semantic errors that only surface during expansion).
# A NEW false-READY outside this list is a real regression and fails the run.
# This list is populated from the measured at-scale run and kept in sync with
# docs/COMPILATION_GUARANTEE.md. Only add a basename here after confirming the
# miss is a genuine modeling limitation (undefined-cs / missing-package /
# expansion-time semantic error), never to paper over a real T0/T5 gap.
#
# The list below is EXACTLY the set measured as true false-READY at scale
# (cc=READY yet pdflatex FAILS). Each maps to a limit-class analyzed in
# docs/COMPILATION_GUARANTEE.md. Entries deliberately EXCLUDED because the
# pre-check DOES catch them (measured NOT-READY): fail_left_without_right,
# fail_dollar_in_dollar, fail_runaway_argument (T0 parser), and
# fail_duplicate_label (pdflatex only warns, so it COMPILES — not a false-READY).
KNOWN_FALSE_READY="
fail_undefined_cs.tex
fail_missing_usepackage.tex
fail_undefined_environment.tex
fail_bad_usepackage.tex
fail_align_no_amsmath.tex
fail_math_in_text.tex
fail_newcommand_wrong_args.tex
fail_bad_graphics_include.tex
fail_missing_begin_document.tex
"

is_known_false_ready() {
  local base="$1"
  printf '%s\n' "$KNOWN_FALSE_READY" | grep -qxF "$base"
}

if ! command -v pdflatex >/dev/null 2>&1; then
  echo "[diff-compile-check] SKIP: pdflatex not on PATH"; exit 0
fi
if [ ! -x "$CLI" ]; then
  echo "[diff-compile-check] building CLI..."; (cd "$ROOT" && opam exec -- dune build latex-parse/src/validators_cli.exe) || exit 1
fi

tp=0; tn=0; false_ready=0; false_notready=0; total=0
new_false_ready=0
false_ready_files=""
new_false_ready_files=""
printf '%-34s | %-10s | %-9s | %s\n' "file" "compile-check" "pdflatex" "class"
printf -- '-----------------------------------+------------+-----------+------\n'
for f in "$CORPUS"/*.tex; do
  [ -e "$f" ] || continue
  base="$(basename "$f")"
  # Skip non-standalone child fragments (included via \input by a good_ parent).
  case "$base" in
    *_part.tex) continue ;;
  esac
  total=$((total+1))
  if "$CLI" --compile-check "$f" >/dev/null 2>&1; then cc=READY; else cc=NOT-READY; fi
  d=$(mktemp -d); cp "$f" "$d/"
  # Also copy any sibling _part.tex fragments so \input parents resolve.
  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true
  if (cd "$d" && pdflatex -interaction=nonstopmode -halt-on-error "$base" >/dev/null 2>&1); then pl=COMPILES; else pl=FAILS; fi
  rm -rf "$d"
  cls=ok
  if   [ "$cc" = READY ]     && [ "$pl" = FAILS ];    then
    cls="FALSE-READY"; false_ready=$((false_ready+1)); false_ready_files="$false_ready_files $base"
    if is_known_false_ready "$base"; then
      cls="FALSE-READY(known)"
    else
      cls="FALSE-READY(NEW!)"; new_false_ready=$((new_false_ready+1)); new_false_ready_files="$new_false_ready_files $base"
    fi
  elif [ "$cc" = NOT-READY ] && [ "$pl" = COMPILES ]; then cls="false-not-ready"; false_notready=$((false_notready+1))
  elif [ "$cc" = READY ]     && [ "$pl" = COMPILES ]; then tp=$((tp+1))
  else tn=$((tn+1)); fi
  printf '%-34s | %-10s | %-9s | %s\n' "$base" "$cc" "$pl" "$cls"
done
echo
echo "[diff-compile-check] total=$total  READY&compiles=$tp  NOT-READY&fails=$tn"
echo "[diff-compile-check] FALSE-READY (cc=READY,pdflatex FAILS) total=$false_ready :$false_ready_files"
echo "[diff-compile-check]   of which KNOWN-limitation (allowlisted)=$((false_ready-new_false_ready))"
echo "[diff-compile-check]   of which NEW (regression)=$new_false_ready :$new_false_ready_files"
echo "[diff-compile-check] false-not-ready (safe over-reject)=$false_notready"
# Non-zero exit ONLY on a NEW false-READY beyond the documented allowlist.
[ "$new_false_ready" -eq 0 ]
