#!/usr/bin/env bash
set -euo pipefail

# False-positive scan harness over a directory of .tex files using the CLI.
# Usage: L0_VALIDATORS=pilot bash scripts/pilot_fp_scan.sh <dir> [<dir2> ...]

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <corpus_dir> [<corpus_dir2> ...]" >&2
  exit 2
fi

CLI=_build/default/latex-parse/src/validators_cli.exe
if [[ ! -x "$CLI" ]]; then
  echo "[fp-scan] Building validators_cli..." >&2
  OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build latex-parse/src/validators_cli.exe
fi

export L0_VALIDATORS=${L0_VALIDATORS:-pilot}

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

for dir in "$@"; do
  find "$dir" -type f -name '*.tex' -print0 | while IFS= read -r -d '' f; do
    "$CLI" "$f" >> "$tmp" || true
  done
done

if [[ ! -s "$tmp" ]]; then
  echo "[fp-scan] No validator hits."; exit 0
fi

echo "id,count" > /tmp/pilot_fp_summary.csv
awk '{print $1}' "$tmp" | sort | uniq -c | awk '{printf "%s,%d\n", $2, $1}' | tee -a /tmp/pilot_fp_summary.csv
echo "[fp-scan] CSV: /tmp/pilot_fp_summary.csv"

