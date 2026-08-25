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
#   FR_FIXTURE_TSV=path pre-computed fixture TSV; skips python3 entirely, which is
#                       what lets the TeX container stay dependency-free
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
if ! command -v pdflatex >/dev/null 2>&1; then
  [ "$REQUIRE" = 1 ] && die_infra "REQUIRE_PDFLATEX=1 but pdflatex is not on PATH"
  echo "[fr-oracle] SKIP: no pdflatex on PATH"; exit 0
fi

TIMEOUT="$(command -v gtimeout || command -v timeout || true)"
if [ -z "$TIMEOUT" ]; then
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
# the manifest with python3 — but the TeX container deliberately has no python3,
# so relying on that alone made the pin FAIL OPEN exactly where it ships: a
# skewed engine would have been graded silently. The workflow passes it in.
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
GOT_ENGINE="$(pdflatex --version 2>/dev/null | head -1)"
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
run_pdflatex() { # $1=workdir $2=base $3=halt(0/1) -> echoes "rc pdf"
  local wd="$1" base="$2" halt="$3" rc pdf i
  local -a cmd=(pdflatex -interaction=nonstopmode)
  [ "$halt" = 1 ] && cmd+=(-halt-on-error)
  cmd+=("$base")
  rc=1
  for i in 1 2; do
    if [ -n "$TIMEOUT" ]; then
      ( cd "$wd" && "$TIMEOUT" "$TEX_TIMEOUT" "${cmd[@]}" >/dev/null 2>&1 )
    else
      ( cd "$wd" && "${cmd[@]}" >/dev/null 2>&1 )
    fi
    rc=$?
    # A timeout kill (124) or a broken `timeout` (125-127) is not a property of
    # the document; surface it immediately rather than masking it with a retry.
    case "$rc" in 124|125|126|127) break ;; esac
  done
  [ -f "$wd/${base%.tex}.pdf" ] && pdf=yes || pdf=no
  echo "$rc $pdf"
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
  wd="$(mktemp -d)"
  if [ "$kind" = single ]; then
    cp "$FRDIR/$path" "$wd/" || die_infra "cannot stage fixture $id"
    base="$(basename "$path")"; rundir="$wd"
  else
    sub="${path%%/*}"
    cp -R "$FRDIR/$sub" "$wd/" || die_infra "cannot stage fixture tree $id"
    base="$(basename "$path")"; rundir="$wd/$sub"
  fi
  if "$CLI" --compile-check "$FRDIR/$path" >/dev/null 2>&1; then cli=READY; else cli=NOT-READY; fi

  # ORDERING IS LOAD-BEARING: halt-on-error FIRST. fr_corrupt_aux's doc.aux is
  # rewritten by a run that gets far enough, so a nonstop-first ordering makes the
  # second run see a repaired .aux and grade `compiles`. Do not reorder.
  read -r hrc _hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"
  # Clear artefacts between protocols: a PDF left by the halt run would be
  # attributed to the nonstop run and silently convert strong-fatal -> error-halt.
  rm -f "$rundir/${base%.tex}.pdf" "$rundir/${base%.tex}.log"
  read -r nrc npdf  <<<"$(run_pdflatex "$rundir" "$base" 0)"
  logfile="$(mktemp)"
  cp "$rundir/${base%.tex}.log" "$logfile" 2>/dev/null || : > "$logfile"
  rm -rf "$wd"

  # 124 = timeout kill; 125/126/127 = timeout itself failed / not executable /
  # not found. None is a property of the DOCUMENT, yet all of them look exactly
  # like "failed with no PDF" = strong-fatal, which MATCHES the manifest for most
  # fixtures. A pdflatex that cannot run at all would have graded 21/21 `ok`.
  case "$hrc:$nrc" in
    *124*|*125*|*126*|*127*)
      printf '%-24s pdflatex could not be run (rc halt=%s nonstop=%s) — refusing to grade\n' \
        "$id" "$hrc" "$nrc"
      timeouts=$((timeouts+1)); continue ;;
  esac
  # Affirmative proof that TeX actually ran, rather than inference from a failure.
  if [ ! -s "$logfile" ] || ! grep -qi 'pdftex\|pdflatex' "$logfile" 2>/dev/null; then
    printf '%-24s no pdfTeX log produced — pdflatex did not really run; refusing to grade\n' "$id"
    timeouts=$((timeouts+1)); continue
  fi

  if [ "$nrc" != 0 ] && [ "$npdf" = no ]; then grade=strong-fatal
  elif [ "$hrc" != 0 ]; then grade=error-halt
  else grade=compiles; fi

  status=ok
  # HARD: pdflatex compiles it. For a LIVE fixture that means it was never a
  # false-READY; for a FIXED one it means we now over-reject a compiling doc.
  # Both are real, both are loud.
  if [ "$grade" = compiles ]; then
    status="HARD DRIFT: pdflatex now COMPILES this fixture (cli=$cli)"; hard=$((hard+1))
  elif [ "$grade" != "$pdfl" ]; then
    status="soft drift: grade $grade != manifest $pdfl (both are rejections)"; soft=$((soft+1))
  fi
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
[ "$timeouts" -eq 0 ] || die_infra "$timeouts fixture(s) timed out; grades are not trustworthy"

echo "[fr-oracle] checked $n fixtures; hard=$hard soft=$soft (engine: $GOT_ENGINE)"
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
