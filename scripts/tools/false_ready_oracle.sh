#!/usr/bin/env bash
# pdflatex oracle for the round-7 false-READY corpus (R7-INFRA-2).
#
# For every fixture in corpora/false_ready/manifest.json it runs the CLI and real
# pdflatex (both protocols) and checks the observed grade still matches the
# manifest's recorded `pdflatex` field (strong-fatal | error-halt). This is the
# drift guard: if a TeX Live change alters a fixture's real behaviour, it surfaces
# here rather than silently invalidating the corpus.
#
# Runs BOTH locally and in CI (.github/workflows/tex-oracle.yml, inside a
# digest-pinned TeX Live image). The CLI-only monotone gate remains
# scripts/tools/check_known_false_ready.py, wired into ci.yml's `build` job.
#
# ── DRIFT SEVERITY ───────────────────────────────────────────────────────────
# HARD (exit 1): a fixture that pdflatex now COMPILES. This is the soundness
#   signal, and it is the one grade no environmental defect can manufacture — a
#   missing package or font makes a document fail, never succeed.
# SOFT (warn):  strong-fatal <-> error-halt. Both mean "pdflatex rejects it"; the
#   distinction only records whether nonstopmode limped to a PDF, which is exactly
#   what an incomplete font install or a TeX error-recovery change moves.
#   Measured: with Type1 fonts hidden, all 8 error-halt fixtures flip to
#   strong-fatal. Failing on that would be crying wolf, and a gate that cries wolf
#   gets disabled. STRICT_GRADE=1 makes SOFT fatal too (use when deliberately
#   re-recording the manifest).
# For the record: TL2024 (pdfTeX 1.40.26) vs TL2026 (1.40.29) produce ZERO drift
# and byte-identical first-error text on all 21 fixtures. Engine YEAR is not the
# fragile axis; install COMPLETENESS is.
#
# ── EXIT CODES ───────────────────────────────────────────────────────────────
#   0  clean
#   1  HARD drift (a fixture now compiles / grade mismatch under STRICT_GRADE)
#   2  infrastructure (no pdflatex, no CLI, no timeout, unparseable manifest,
#      zero fixtures processed, a pdflatex run that timed out)
#   3  engine skew (pdflatex version != manifest oracle.version)
#
# ── ENV ──────────────────────────────────────────────────────────────────────
#   REQUIRE_PDFLATEX=1  every precondition is an error, never a skip (CI sets it)
#   STRICT_GRADE=1      SOFT drift also fails
#   ALLOW_ENGINE_SKEW=1 engine mismatch warns instead of exit 3
#   FR_FIXTURE_TSV=path pre-computed fixture TSV; skips the python3 fixture
#                       emitter (the pdflatex runs themselves still need python3:
#                       since C-91 every one goes through the _oracle.py shim)
#   TEX_TIMEOUT=30      per-pdflatex-run timeout in seconds
#
# Usage:
#   false_ready_oracle.sh                  verify the manifest matches reality
#   false_ready_oracle.sh --emit-fixtures  print the fixture TSV and exit
set -u
set -o pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CLI="$ROOT/_build/default/latex-parse/src/validators_cli.exe"
FRDIR="$ROOT/corpora/false_ready"
MAN="$FRDIR/manifest.json"
REQUIRE="${REQUIRE_PDFLATEX:-0}"
TEX_TIMEOUT="${TEX_TIMEOUT:-30}"
# `gtimeout 0 CMD` means "no limit" — that silently reinstates the ungraded-hang
# condition this script argues at length must never happen.
case "$TEX_TIMEOUT" in
  ''|*[!0-9]*) echo "[fr-oracle] FATAL: TEX_TIMEOUT must be a positive integer, got '$TEX_TIMEOUT'" >&2; exit 2 ;;
  0) echo "[fr-oracle] FATAL: TEX_TIMEOUT=0 disables the timeout; refusing (a hang would be graded)" >&2; exit 2 ;;
esac

die_infra() { echo "[fr-oracle] FATAL: $*" >&2; exit 2; }

emit_fixtures() { # -> TSV on stdout; nonzero if the manifest is unusable
  python3 -c "
import json, sys
m = json.load(open('$MAN'))
fx = m.get('fixtures')
if not isinstance(fx, list) or not fx:
    sys.exit('manifest has no usable fixtures list')
for f in fx:
    print('\t'.join([f['id'], f['path'], f['kind'], f['pdflatex'],
                     f.get('expected_cli', '')]))
"
}

if [ "${1:-}" = "--emit-fixtures" ]; then
  emit_fixtures || die_infra "cannot emit fixtures from $MAN"
  exit 0
fi

# ── preconditions ────────────────────────────────────────────────────────────
# The ONE oracle (ADR-012 decision 7): the pinned TeX Live image, natively when
# this runs inside it (tex-oracle.yml sets LP_ORACLE_IN_IMAGE), through the
# container otherwise. A host pdflatex never grades; see _oracle.sh.
# shellcheck source=scripts/tools/_oracle.sh
. "$ROOT/scripts/tools/_oracle.sh"
oracle_setup fr-oracle "$REQUIRE"

TIMEOUT=""
[ "$ORACLE_TIMEOUT_INSIDE" = 1 ] || TIMEOUT="$(command -v gtimeout || command -v timeout || true)"
if [ -z "$TIMEOUT" ] && [ "$ORACLE_TIMEOUT_INSIDE" != 1 ]; then
  # Without a timeout a hung pdflatex would be GRADED: GNU timeout's 124 looks
  # exactly like "failed with no PDF" = strong-fatal, which MATCHES the manifest
  # for most fixtures. A hanging TeX Live would report `ok`. Refuse to grade.
  [ "$REQUIRE" = 1 ] && die_infra "REQUIRE_PDFLATEX=1 but neither gtimeout nor timeout is available"
  echo "[fr-oracle] WARNING: no timeout binary; a hung pdflatex is indistinguishable from a fatal" >&2
fi

if [ ! -x "$CLI" ]; then
  # A gate must never build its own subject: CI builds the CLI in an earlier,
  # separately-visible step so a build failure is reported as a build failure.
  [ "$REQUIRE" = 1 ] && die_infra "REQUIRE_PDFLATEX=1 but the CLI is missing at $CLI (build it in its own step)"
  echo "[fr-oracle] building CLI..."
  (cd "$ROOT" && opam exec -- dune build latex-parse/src/validators_cli.exe) \
    || die_infra "CLI build failed"
  [ -x "$CLI" ] || die_infra "CLI still missing after build: $CLI"
fi

[ -f "$MAN" ] || die_infra "no manifest at $MAN"

# A CLI that cannot execute (wrong ABI inside the container, missing loader)
# returns non-zero for EVERY document, which reads as a uniform column of
# NOT-READY and grades perfectly `ok`. Prove it runs before trusting its verdicts.
# Invoked with no arguments the CLI prints its usage banner and exits 2. We check
# for the BANNER, not the exit code: a binary that cannot load (wrong ABI inside
# the container, missing loader) also exits non-zero but prints nothing, and would
# otherwise answer NOT-READY to all 21 fixtures — a uniform column of lies that
# grades perfectly `ok`.
# NB: capture, then test. A pipeline would be governed by `set -o pipefail`, and
# the CLI deliberately exits 2 here, so `"$CLI" | grep -q` fails even when grep
# matches.
CLI_BANNER="$("$CLI" 2>&1 || true)"
if ! printf '%s' "$CLI_BANNER" | grep -q 'Usage:'; then
  die_infra "the CLI at $CLI did not produce its usage banner — it cannot execute here (ABI/loader problem?), so its verdicts would be meaningless"
fi

# ── engine pin ───────────────────────────────────────────────────────────────
# A re-pin must report as "PIN MISMATCH", never as 21 lines of DRIFT. Those are
# different problems with different fixes, and conflating them is how a gate gets
# switched off instead of understood.
# FR_EXPECT_ENGINE lets the caller supply the pin directly. Without it we parse
# the manifest with python3. The TeX image this ran in when that was written had
# no python3, so relying on the parse alone made the pin FAIL OPEN exactly where
# it ships; the pinned image of ADR-012 decision 7 does have /usr/bin/python3
# (the native oracle backend needs it), but the workflow still passes the pin in.
MAN_ENGINE="${FR_EXPECT_ENGINE:-}"
if [ -z "$MAN_ENGINE" ]; then
  MAN_ENGINE="$(python3 -c "
import json
print(json.load(open('$MAN')).get('oracle', {}).get('version', ''))
" 2>/dev/null || true)"
fi
if [ -z "$MAN_ENGINE" ] && [ "$REQUIRE" = 1 ]; then
  die_infra "cannot determine the expected engine (no FR_EXPECT_ENGINE and no readable manifest oracle.version) — refusing to grade against an unpinned engine"
fi
GOT_ENGINE="$ORACLE_BANNER"
if [ -n "$MAN_ENGINE" ]; then
  case "$GOT_ENGINE" in
    *"$MAN_ENGINE"*) ;;
    *)
      if [ "${ALLOW_ENGINE_SKEW:-0}" = 1 ]; then
        echo "[fr-oracle] WARNING: engine skew (have '$GOT_ENGINE', manifest '$MAN_ENGINE')" >&2
      else
        echo "[fr-oracle] PIN MISMATCH: pdflatex is '$GOT_ENGINE' but the manifest records '$MAN_ENGINE'." >&2
        echo "[fr-oracle]   This is NOT oracle drift. Either re-pin the engine, or deliberately" >&2
        echo "[fr-oracle]   re-record the manifest (see docs/COMPILATION_GUARANTEE.md SO1)." >&2
        echo "[fr-oracle]   ALLOW_ENGINE_SKEW=1 downgrades this to a warning." >&2
        exit 3
      fi
      ;;
  esac
fi

# ── fixtures ─────────────────────────────────────────────────────────────────
# Read from a FILE, never a process substitution: `done < <(python3 ...)` hides
# python's exit status, so a manifest whose shape changed printed
# "checked 0 fixtures; drift=0" and exited 0 — a green gate that tested nothing.
TSV="$(mktemp)"; trap 'rm -f "$TSV"' EXIT
if [ -n "${FR_FIXTURE_TSV:-}" ]; then
  [ -f "$FR_FIXTURE_TSV" ] || die_infra "FR_FIXTURE_TSV=$FR_FIXTURE_TSV does not exist"
  cp "$FR_FIXTURE_TSV" "$TSV"
else
  emit_fixtures > "$TSV" || die_infra "cannot parse $MAN (fixtures list missing or malformed)"
fi
EXPECT_N="$(wc -l < "$TSV" | tr -d ' ')"
[ "${EXPECT_N:-0}" -gt 0 ] || die_infra "zero fixtures to check — refusing to report success"

# ⚠ SUCCESS MUST BE STABLE, NOT JUST REACHED. This used to run pdflatex exactly
# ONCE per protocol and grade on that, which cannot see a document that succeeds
# and then breaks ITSELF on the next run. `fr_toc_second_pass` is exactly that:
# \addcontentsline writes a raw token into .toc, \tableofcontents reads it on the
# NEXT run, so pass 1 is rc 0 with a PDF and pass 2 is rc 1. The .aux cannot do
# this — \enddocument closes and immediately re-inputs it in the same run
# (latex.ltx:15483-15489) — so the hazard is the write-once-read-next-run files
# .toc/.lof/.lot. Same defect, same fix as run_to_fixpoint in diff_real_roots.py.
#
# A healthy document therefore costs 2 runs, not 1; the reported rc is the
# CONFIRMING run's when it disagrees, because the last state is the one a real
# build tool would leave the author in.
#
# POSITIVE PROOF, PER PASS (OPEN-118 review round 2). An rc counts only when
# THAT pass's own output carries pdfTeX's banner ("This is pdfTeX", printed
# under -interaction=nonstopmode before the document is read). MEASURED
# 2026-09-27: with a docker wrapper that sent only the -halt-on-error passes to
# a dead daemon socket, the docker CLI exited 1 on every halt pass, this
# function returned "1 no", every fixture graded error-halt and the run was
# RC 0 "hard=0 soft=19" with 66 `ok` rows although no halt-protocol pdflatex
# had run: the only proof-of-run check read the NONSTOP pass's log, after the
# halt pass's log had been deleted. A pass without the banner now reports rc
# NOPROOF, which the caller refuses to grade.
run_pdflatex() { # $1=workdir $2=base $3=halt(0/1) -> echoes "rc pdf"
  local wd="$1" base="$2" halt="$3" rc pdf i out
  local -a cmd=("${PDFLATEX[@]}" -interaction=nonstopmode)
  [ "$halt" = 1 ] && cmd+=(-halt-on-error)
  cmd+=("$base")
  rc=1
  out="$(mktemp)"
  # Free space BEFORE the first pass (oracle_vet, _oracle.sh): a full work root
  # makes pdfTeX fail on its own output, banner and all.
  if ! oracle_vet "$wd" 2>/dev/null; then rm -f "$out"; echo "ENVFAIL no"; return; fi
  for i in 1 2; do
    if [ -n "$TIMEOUT" ]; then
      ( cd "$wd" && "$TIMEOUT" "$TEX_TIMEOUT" "${cmd[@]}" >"$out" 2>/dev/null )
    else
      ( cd "$wd" && "${cmd[@]}" >"$out" 2>/dev/null )
    fi
    rc=$?
    # A timeout kill (124) or a broken `timeout` (125-127, also _oracle.py's
    # INFRA_RC) is not a property of the document; surface it immediately
    # rather than masking it with a retry.
    case "$rc" in 124|125|126|127) break ;; esac
    if ! grep -q 'This is pdfTeX' "$out" 2>/dev/null; then rc=NOPROOF; break; fi
    # Proof pdfTeX ran is not proof its rc is the document's: refuse a pass in
    # which pdfTeX could not write its own output, or after which the work
    # root is short of space.
    if ! oracle_vet "$wd" "$out" "${cmd[@]}" 2>/dev/null; then rc=ENVFAIL; break; fi
  done
  rm -f "$out"
  # The PDF verdict is pdfTeX's own report in this pass's log, not a file
  # named .pdf (a document can \openout one, C-97): _oracle.pdf_written.
  oracle_pdf_written "$wd" "$base" 2>/dev/null && pdf=yes || pdf=no
  echo "$rc $pdf"
}

# The drift class of one fixture: $1 = this run's grade, $2 = the manifest's.
# A function so check_oracle_infra_grading.py can test it without an oracle.
#   hard-compiles  pdflatex compiles a fixture the manifest records as rejected
#   hard-rejects   pdflatex rejects a fixture the manifest records as compiles.
#                  This used to fall through to `soft` under the message "both
#                  are rejections", which is false for a `compiles` fixture, and
#                  the run exited 0 (OPEN-118 review round 2, defect 5)
#   soft           strong-fatal <-> error-halt: both still rejections
#   ok             equal
drift_class() {
  if [ "$1" = "$2" ]; then echo ok
  elif [ "$1" = compiles ]; then echo hard-compiles
  elif [ "$2" = compiles ]; then echo hard-rejects
  else echo soft; fi
}

hard=0; soft=0; n=0; timeouts=0
while IFS=$'\t' read -r id path kind pdfl exp_cli; do
  [ -n "$id" ] || continue
  n=$((n+1))
  # Stage a fresh copy so committed sibling .aux/.bbl inputs are preserved.
  # An unchecked `cp` let a DELETED fixture grade `ok`: 13 of 21 are strong-fatal,
  # and a missing input also fails to compile, so they look identical. #506 already
  # lost a fixture to .gitignore once.
  [ -e "$FRDIR/$path" ] || die_infra "fixture input missing on disk: $path (id=$id)"
  wd="$(mktemp -d "${TMPDIR:-/tmp}/lp-oracle.XXXXXX")"
  if [ "$kind" = single ]; then
    cp "$FRDIR/$path" "$wd/" || die_infra "cannot stage fixture $id"
    base="$(basename "$path")"; rundir="$wd"
  else
    sub="${path%%/*}"
    cp -R "$FRDIR/$sub" "$wd/" || die_infra "cannot stage fixture tree $id"
    base="$(basename "$path")"; rundir="$wd/$sub"
  fi
  # pdfTeX's job name (doc.TEX -> doc), the one definition in _oracle.py.
  job="$(oracle_job "$base")" || die_infra "cannot compute the job name of $base"
  if "$CLI" --compile-check "$FRDIR/$path" >/dev/null 2>&1; then cli=READY; else cli=NOT-READY; fi

  # ORDERING IS LOAD-BEARING: halt-on-error FIRST. fr_corrupt_aux's doc.aux is
  # rewritten by a run that gets far enough, so a nonstop-first ordering makes the
  # second run see a repaired .aux and grade `compiles`. Do not reorder.
  read -r hrc hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"
  # Check the HALT pass BEFORE its artefacts are deleted: the only proof-of-run
  # check used to read the nonstop pass's log, so a lost halt pass was invisible
  # (see run_pdflatex). Both the per-pass banner and the halt run's own log.
  case "$hrc" in
    124|125|126|127|NOPROOF|ENVFAIL)
      printf '%-24s halt-protocol pdflatex could not be run (rc %s) — refusing to grade\n' "$id" "$hrc"
      rm -rf "$wd"; timeouts=$((timeouts+1)); continue ;;
  esac
  if ! grep -q 'This is pdfTeX' "$rundir/$job.log" 2>/dev/null; then
    printf '%-24s no pdfTeX log from the halt run — pdflatex did not really run; refusing to grade\n' "$id"
    rm -rf "$wd"; timeouts=$((timeouts+1)); continue
  fi
  # Clear artefacts between protocols: a PDF left by the halt run would be
  # attributed to the nonstop run and silently convert strong-fatal -> error-halt.
  # Through the oracle, not a host `rm`: see ORACLE_RM in _oracle.sh.
  "${ORACLE_RM[@]}" "$rundir/$job.pdf" "$rundir/$job.log" \
    || die_infra "cannot clear the halt run's artefacts for $id"
  read -r nrc npdf  <<<"$(run_pdflatex "$rundir" "$base" 0)"
  logfile="$(mktemp)"
  cp "$rundir/$job.log" "$logfile" 2>/dev/null || : > "$logfile"
  rm -rf "$wd"

  # 124 = timeout kill; 125/126/127 = timeout itself failed / not executable /
  # not found, and 125 is also _oracle.py's INFRA_RC (the container oracle
  # failed: docker unreachable, container gone, a refused environment). None is a property of the DOCUMENT, yet all of them look exactly
  # like "failed with no PDF" = strong-fatal, which MATCHES the manifest for most
  # fixtures. A pdflatex that cannot run at all would have graded 21/21 `ok`.
  case "$hrc:$nrc" in
    *124*|*125*|*126*|*127*|*NOPROOF*|*ENVFAIL*)
      printf '%-24s pdflatex could not be run (rc halt=%s nonstop=%s) — refusing to grade\n' \
        "$id" "$hrc" "$nrc"
      timeouts=$((timeouts+1)); continue ;;
  esac
  # Affirmative proof that TeX actually ran, rather than inference from a failure.
  if [ ! -s "$logfile" ] || ! grep -q 'This is pdfTeX' "$logfile" 2>/dev/null; then
    printf '%-24s no pdfTeX log produced — pdflatex did not really run; refusing to grade\n' "$id"
    timeouts=$((timeouts+1)); continue
  fi

  # `compiles` is the §B.4 predicate (STRICT_TIER_DESIGN.md, E0): rc 0 AND a
  # PDF under the halt protocol. It used to be "hrc 0" alone, so an rc-0 run
  # that typeset nothing (no PDF) graded `compiles`. Such a run is now graded
  # like the failure it is: strong-fatal when nonstop produced no PDF either,
  # error-halt otherwise. The first two branches are unchanged.
  if [ "$nrc" != 0 ] && [ "$npdf" = no ]; then grade=strong-fatal
  elif [ "$hrc" != 0 ]; then grade=error-halt
  elif [ "$hpdf" != yes ]; then
    if [ "$npdf" = no ]; then grade=strong-fatal; else grade=error-halt; fi
  else grade=compiles; fi

  status=ok
  # HARD: pdflatex compiles a fixture the manifest records as REJECTED. For a
  # LIVE fixture that means it was never a false-READY; for a FIXED one it
  # means we now over-reject a compiling doc. Both are real, both are loud.
  #
  # A manifest-recorded grade of `compiles` is LEGAL since the comment-train
  # target fixtures (fr_cmt_target_*): those pin the OVER-REJECTION direction —
  # documents pdflatex accepts that the CLI must eventually accept too — so
  # for them `compiles` is the expected steady state, and the drift signal is
  # the opposite one: such a fixture STOPPING compiling is graded below like
  # any other mismatch.
  case "$(drift_class "$grade" "$pdfl")" in
    hard-compiles)
      status="HARD DRIFT: pdflatex now COMPILES this fixture (cli=$cli)"; hard=$((hard+1)) ;;
    hard-rejects)
      status="HARD DRIFT: pdflatex now REJECTS ($grade) a fixture the manifest records as compiles (cli=$cli)"; hard=$((hard+1)) ;;
    soft)
      status="soft drift: grade $grade != manifest $pdfl (both are rejections)"; soft=$((soft+1)) ;;
  esac
  # F1: the cli column was computed and never checked. A CLI that answers READY to
  # everything (i.e. every round-7 fix reverted) graded 21/21 `ok`.
  if [ -n "${exp_cli:-}" ] && [ "$cli" != "$exp_cli" ]; then
    status="$status | CLI MISMATCH: got $cli, manifest expects $exp_cli"
    hard=$((hard+1))
  fi
  printf '%-24s cli=%-9s pdflatex=%-12s manifest=%-12s %s\n' "$id" "$cli" "$grade" "$pdfl" "$status"
  rm -f "$logfile"
done < "$TSV"

# Anti-vacuity: processing fewer fixtures than the manifest lists is a failure,
# not a pass. This is what makes "checked 0 fixtures" impossible.
if [ "$n" -ne "$EXPECT_N" ]; then
  die_infra "processed $n of $EXPECT_N fixtures — refusing to report success"
fi
[ "$timeouts" -eq 0 ] || die_infra "$timeouts fixture(s) not graded (timeout, oracle failure, a full work root, or no proof pdfTeX ran); grades are not trustworthy"

echo "[fr-oracle] checked $n fixtures; hard=$hard soft=$soft (engine: $GOT_ENGINE; oracle: $ORACLE_BACKEND)"
if [ "$hard" -ne 0 ]; then
  echo "[fr-oracle] FAIL: $hard fixture(s) that pdflatex now compiles." >&2
  exit 1
fi
# Mass reclassification is not a benign font difference; it is what a broken or
# fake TeX install looks like. Half the corpus moving at once is not a soft signal.
if [ "$soft" -ge $(( (n + 1) / 2 )) ] && [ "$soft" -gt 0 ]; then
  echo "[fr-oracle] FAIL: $soft of $n fixtures reclassified — that is the signature of a" >&2
  echo "[fr-oracle]   broken or incomplete TeX install, not of per-fixture drift." >&2
  exit 2
fi
if [ "$soft" -ne 0 ]; then
  echo "[fr-oracle] NOTE: $soft strong-fatal/error-halt reclassification(s); all still rejections." >&2
  if [ "${STRICT_GRADE:-0}" = 1 ]; then
    echo "[fr-oracle] STRICT_GRADE=1 -> failing." >&2; exit 1
  fi
fi
exit 0
