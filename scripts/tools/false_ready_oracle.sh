#!/usr/bin/env bash
# Local pdflatex oracle for the round-7 false-READY corpus (R7-INFRA-2, local
# form). For every fixture in corpora/false_ready/manifest.json it runs the CLI
# and real pdflatex (both protocols) and checks the observed grade still matches
# the manifest's recorded `pdflatex` field (strong-fatal | error-halt). This is
# the drift guard: if a TeX Live upgrade changes a fixture's real behaviour, this
# surfaces it. CI has no TeX, so this is a LOCAL / pre-release gate; the CI gate
# is scripts/tools/check_known_false_ready.py (CLI-only, ground truth baked in).
#
# Usage: false_ready_oracle.sh          # verify manifest matches reality
# Requires: pdflatex on PATH, the CLI built, python3. Exits nonzero on mismatch.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CLI="$ROOT/_build/default/latex-parse/src/validators_cli.exe"
FRDIR="$ROOT/corpora/false_ready"
MAN="$FRDIR/manifest.json"
TIMEOUT="$(command -v gtimeout || command -v timeout || true)"

command -v pdflatex >/dev/null 2>&1 || { echo "[fr-oracle] SKIP: no pdflatex on PATH"; exit 0; }
[ -x "$CLI" ] || { echo "[fr-oracle] building CLI..."; (cd "$ROOT" && opam exec -- dune build latex-parse/src/validators_cli.exe) || exit 2; }
[ -f "$MAN" ] || { echo "[fr-oracle] ERROR: no manifest at $MAN"; exit 2; }

run_pdflatex() { # $1=workdir $2=base $3=halt(0/1) -> echoes "rc pdf"
  local wd="$1" base="$2" halt="$3" rc pdf
  local -a cmd=(pdflatex -interaction=nonstopmode)
  [ "$halt" = 1 ] && cmd+=(-halt-on-error)
  cmd+=("$base")
  if [ -n "$TIMEOUT" ]; then ( cd "$wd" && "$TIMEOUT" 30 "${cmd[@]}" >/dev/null 2>&1 ); else ( cd "$wd" && "${cmd[@]}" >/dev/null 2>&1 ); fi
  rc=$?
  [ -f "$wd/${base%.tex}.pdf" ] && pdf=yes || pdf=no
  echo "$rc $pdf"
}

fails=0; n=0
while IFS=$'\t' read -r id path kind pdfl; do
  n=$((n+1))
  # stage a fresh copy so committed sibling .aux/.bbl inputs are preserved
  wd="$(mktemp -d)"
  if [ "$kind" = single ]; then
    cp "$FRDIR/$path" "$wd/"; base="$(basename "$path")"; rundir="$wd"
  else
    sub="${path%%/*}"; cp -R "$FRDIR/$sub" "$wd/"; base="$(basename "$path")"; rundir="$wd/$sub"
  fi
  if "$CLI" --compile-check "$FRDIR/$path" >/dev/null 2>&1; then cli=READY; else cli=NOT-READY; fi
  read -r hrc _hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"
  read -r nrc npdf  <<<"$(run_pdflatex "$rundir" "$base" 0)"
  rm -rf "$wd"
  if [ "$nrc" != 0 ] && [ "$npdf" = no ]; then grade=strong-fatal
  elif [ "$hrc" != 0 ]; then grade=error-halt
  else grade=compiles; fi
  status=ok
  # Every fixture must remain a false-READY relative to its recorded strictness,
  # while it is still live (CLI READY). A CLI NOT-READY here means it was fixed
  # (the CLI gate handles that bookkeeping); we only flag pdflatex-side drift.
  if [ "$cli" = READY ] && [ "$grade" = compiles ]; then status="DRIFT: pdflatex now COMPILES (no longer a false-READY)"; fails=$((fails+1)); fi
  if [ "$grade" != compiles ] && [ "$grade" != "$pdfl" ]; then status="DRIFT: pdflatex grade $grade != manifest $pdfl"; fails=$((fails+1)); fi
  printf '%-24s cli=%-9s pdflatex=%-12s manifest=%-12s %s\n' "$id" "$cli" "$grade" "$pdfl" "$status"
done < <(python3 -c "
import json,sys
m=json.load(open('$MAN'))
for f in m['fixtures']:
    print('\t'.join([f['id'],f['path'],f['kind'],f['pdflatex']]))
")

echo "[fr-oracle] checked $n fixtures; drift=$fails"
[ "$fails" -eq 0 ]
