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
# pdflatex COMPILES means rc 0 AND a PDF (STRICT_TIER_DESIGN.md §B.4, E0).
# Requires the pinned-image oracle (_oracle.sh). Runs locally and in CI's tex-oracle workflow, where
# it is ADVISORY (continue-on-error): its exit condition is a measurement of the
# soundness residual, and it needs a large, correctness-critical TeX install — an
# incomplete one manufactures spurious FALSE-READY(NEW!) rows. It is also blind to
# a CLI broken in the over-rejection direction, so it is the wrong shape for a
# blocking regression gate. The blocking gates are check_known_false_ready.py
# (CLI-only, monotone) and false_ready_oracle.sh (pdflatex, HARD drift only).
#
# EXIT CODES: 0 clean | 1 a NEW false-READY beyond the allowlist | 2 infrastructure
# (no oracle, no CLI, too few docs, a timeout or oracle failure on ANY document,
# or a vacuous run) | 3 engine skew
# | 4 over-rejection budget exceeded (SAFE direction — never conflate with 1).
#
# ENV: REQUIRE_PDFLATEX=1 makes every precondition an error instead of a skip;
#      EXPECT_TEX_VERSION=<substring> asserts the engine; MIN_DOCS (default 65)
#      floors the corpus size; MAX_FALSE_NOTREADY (default 6) caps over-rejection;
#      TEX_TIMEOUT (default 60) bounds each pdflatex run.
#
# Usage: diff_compile_check.sh [CORPUS_DIR]
set -u
set -o pipefail
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
# fail_dollar_in_dollar, fail_runaway_argument, fail_missing_begin_document
# (all T0 parser), and fail_duplicate_label (pdflatex only warns, so it
# COMPILES — not a false-READY).
KNOWN_FALSE_READY="
fail_undefined_cs.tex
fail_missing_usepackage.tex
fail_undefined_environment.tex
fail_bad_usepackage.tex
fail_align_no_amsmath.tex
fail_math_in_text.tex
fail_newcommand_wrong_args.tex
fail_bad_graphics_include.tex
"

is_known_false_ready() {
  local base="$1"
  printf '%s\n' "$KNOWN_FALSE_READY" | grep -qxF "$base"
}

REQUIRE="${REQUIRE_PDFLATEX:-0}"
TEX_TIMEOUT="${TEX_TIMEOUT:-60}"
die_infra() { echo "[diff-compile-check] FATAL: $*" >&2; exit 2; }

# The ONE oracle (ADR-012 decision 7): the pinned TeX Live image, run in a
# fresh container per run by _oracle.py's one launch definition, locally and
# in CI (from the runner host; the in-image native branch is retired, ADR-015
# E15, OPEN-128). A host pdflatex never grades; see _oracle.sh.
# shellcheck source=scripts/tools/_oracle.sh
. "$ROOT/scripts/tools/_oracle.sh"
oracle_setup diff-compile-check "$REQUIRE"

# A timeout produces pl=FAILS, which against a READY verdict manufactures a
# FALSE-READY(NEW!) out of thin air. Never grade an unbounded run.
TIMEOUT=""
[ "$ORACLE_TIMEOUT_INSIDE" = 1 ] || TIMEOUT="$(command -v gtimeout || command -v timeout || true)"
if [ -z "$TIMEOUT" ] && [ "$ORACLE_TIMEOUT_INSIDE" != 1 ]; then
  [ "$REQUIRE" = 1 ] && die_infra "REQUIRE_PDFLATEX=1 but neither gtimeout nor timeout is available"
  echo "[diff-compile-check] WARNING: no timeout binary; a hung pdflatex would be scored as a failure" >&2
fi

if [ -n "${EXPECT_TEX_VERSION:-}" ]; then
  GOT_ENGINE="$ORACLE_BANNER"
  case "$GOT_ENGINE" in
    *"$EXPECT_TEX_VERSION"*) ;;
    *) echo "[diff-compile-check] PIN MISMATCH: engine '$GOT_ENGINE' != expected '$EXPECT_TEX_VERSION'." >&2
       echo "[diff-compile-check]   This is NOT a soundness regression. Re-pin or re-record." >&2
       exit 3 ;;
  esac
fi

if [ ! -x "$CLI" ]; then
  # A gate must never build its own subject.
  [ "$REQUIRE" = 1 ] && die_infra "REQUIRE_PDFLATEX=1 but the CLI is missing at $CLI (build it in its own step)"
  echo "[diff-compile-check] building CLI..."
  (cd "$ROOT" && opam exec -- dune build latex-parse/src/validators_cli.exe) || die_infra "CLI build failed"
  [ -x "$CLI" ] || die_infra "CLI still missing after build: $CLI"
fi

tp=0; tn=0; false_ready=0; false_notready=0; total=0; timeouts=0
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
  d=$(mktemp -d "${TMPDIR:-/tmp}/lp-oracle.XXXXXX"); cp "$f" "$d/"
  # Also copy any sibling _part.tex fragments so \input parents resolve.
  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true
  # Free space BEFORE and AFTER, and the run's stdout for pdfTeX failing to
  # write its OWN output (oracle_vet, _oracle.sh). MEASURED 2026-09-27: with
  # the work root full, pdfTeX printed its banner, failed on its own .pdf and
  # exited 1 with a log -- ran=yes, pdf=no, i.e. graded FAILS.
  pout="$(mktemp "${TMPDIR:-/tmp}/lp-oracle-out.XXXXXX")"
  envok=yes
  oracle_vet "$d" 2>/dev/null || envok=no
  if [ "$envok" = no ]; then
    prc=125
  elif [ -n "$TIMEOUT" ]; then
    ( cd "$d" && "$TIMEOUT" "$TEX_TIMEOUT" "${PDFLATEX[@]}" -interaction=nonstopmode -halt-on-error "$base" >"$pout" 2>/dev/null )
    prc=$?
  else
    ( cd "$d" && "${PDFLATEX[@]}" -interaction=nonstopmode -halt-on-error "$base" >"$pout" 2>/dev/null )
    prc=$?
  fi
  if [ "$envok" = yes ] && ! oracle_vet "$d" "$pout" -interaction=nonstopmode -halt-on-error "$base" 2>/dev/null; then
    envok=no
  fi
  # The §B.4 predicate (STRICT_TIER_DESIGN.md, E0): COMPILES = rc 0 AND a PDF,
  # and the PDF is pdfTeX's own final report in this run's log AND its
  # terminal output ($pout, the shim's stdout), which must agree -- not a file
  # named .pdf (a document can \openout one), nor a report it could forge
  # (C-97, C-99): _oracle.pdf_written. Exit 1 = no PDF; else not a grade.
  pv=0
  oracle_pdf_written "$d" "$base" "$pout" 2>/dev/null || pv=$?
  [ "$pv" -gt 1 ] && envok=no
  rm -f "$pout"
  if [ "$envok" = no ]; then
    printf '%-34s | %-10s | %-9s | %s\n' "$base" "$cc" "ENVFAIL" "not graded (work root short of space, or pdfTeX could not write its own output)"
    rm -rf "$d"; timeouts=$((timeouts+1)); continue
  fi
  # Grading by rc alone scored tolerated_write18.tex (rc 0, no PDF: its body
  # typesets nothing) COMPILES, i.e. a false-not-ready, where every other
  # grader in the repo scores it FAILS.
  [ "$pv" = 0 ] && pdf=yes || pdf=no
  job="$(oracle_job "$base")"
  # Affirmative proof that pdfTeX ran, as false_ready_oracle.sh requires: the
  # banner pdfTeX writes as the first line of the log. $d is fresh per document
  # and the protocol here is ONE pass, so a log carrying it can only be this
  # run's. (It used to match 'pdftex' anywhere, case-insensitively.)
  if [ -s "$d/$job.log" ] && grep -q 'This is pdfTeX' "$d/$job.log" 2>/dev/null; then
    ran=yes
  else
    ran=no
  fi
  rm -rf "$d"
  # 124 = timeout; 125 = the oracle itself failed (_oracle.py INFRA_RC: docker
  # unreachable, container gone, a refused environment); 126/127 = a wrapper
  # could not execute. None is a property of the DOCUMENT. Grading them as
  # FAILS turned an infrastructure failure into FALSE-READY(NEW!) rows against
  # the CLI and silently counted every NOT-READY row as a correct rejection.
  case "$prc" in
    124|125|126|127)
      printf '%-34s | %-10s | %-9s | %s\n' "$base" "$cc" "rc=$prc" "not graded (timeout/oracle failure)"
      timeouts=$((timeouts+1)); continue ;;
  esac
  if [ "$ran" = no ]; then
    printf '%-34s | %-10s | %-9s | %s\n' "$base" "$cc" "NO-LOG" "not graded (no pdfTeX log: pdflatex did not run)"
    timeouts=$((timeouts+1)); continue
  fi
  if [ "$prc" = 0 ] && [ "$pdf" = yes ]; then pl=COMPILES; else pl=FAILS; fi
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
# First, before any verdict-shaped message: a run with ungraded documents has
# no verdicts to report (the anti-vacuity message below would otherwise blame
# the CLI for what the oracle did).
[ "$timeouts" -eq 0 ] || die_infra "$timeouts document(s) not graded (timeout, oracle failure, no pdfTeX log, or a work root short of space / pdfTeX unable to write its own output); the classification is not trustworthy"

# Allowlist staleness: an entry the CLI now catches is dead weight, and worse, it
# would silently absorb the NEXT regression in that file. Warn, never fail.
stale=""
for known in $KNOWN_FALSE_READY; do
  case " $false_ready_files " in
    *" $known "*) ;;
    *) stale="$stale $known" ;;
  esac
done
[ -n "$stale" ] && echo "[diff-compile-check] NOTE: allowlist entries no longer false-READY (retire them):$stale"

# ── anti-vacuity ─────────────────────────────────────────────────────────────
# Without these a misrooted corpus prints total=0 and exits 0, and a CLI that
# rejects EVERYTHING scores total=65, FALSE-READY=0 and exits 0 — a green gate on
# a completely broken checker. A gate that measures nothing must never pass.
MIN_DOCS="${MIN_DOCS:-65}"
if [ "$total" -lt "$MIN_DOCS" ]; then
  die_infra "processed $total documents, expected at least $MIN_DOCS (corpus misrooted or empty?)"
fi
if [ "$tp" -eq 0 ]; then
  die_infra "ZERO documents were both READY and compiled — the CLI is rejecting everything; these numbers are meaningless"
fi
# Headroom on purpose. Every fix train in this repo is add-NOT-READY-only by
# construction, so a cap sitting exactly at today's measurement (3) would trip on
# the very next conservative detector and misreport routine work as breakage.
# Over-rejection is SAFE — it is not a soundness failure — so it gets its own exit
# code (4) and must never be confused with a false-READY (1).
MAX_FALSE_NOTREADY="${MAX_FALSE_NOTREADY:-6}"
if [ "$false_notready" -gt "$MAX_FALSE_NOTREADY" ]; then
  echo "[diff-compile-check] OVER-REJECTION: $false_notready exceeds MAX_FALSE_NOTREADY=$MAX_FALSE_NOTREADY" >&2
  echo "[diff-compile-check]   This is the SAFE direction (conservative), not a soundness regression." >&2
  exit 4
fi

# Non-zero exit ONLY on a NEW false-READY beyond the documented allowlist.
if [ "$new_false_ready" -ne 0 ]; then
  echo "[diff-compile-check] FAIL: $new_false_ready NEW false-READY:$new_false_ready_files" >&2
  exit 1
fi
exit 0
