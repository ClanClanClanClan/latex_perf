#!/usr/bin/env bash
# Regenerate the committed Coq→OCaml extraction of the strict tier's decision
# on BYTES (ADR-012, milestone M2 phase 2).
#
# Emits latex-parse/strict/strict_bytes_extracted.ml from
# proofs/Strict/ExtractBytes.v: DecideBytes.decide_bytes, the lexer
# Lexer.lex, the parser Front.parse, the phase-1 kernel it runs and the
# diagnostic Explain.explain. The proofs about them (lex_exact, parse_exact,
# in_strict_bytes_dec, decide_bytes_exact, BridgeBytes.
# strict_ready_iff_pdflatex_bytes) are in proofs/Strict/*.v. The phase-1
# extraction (regen_strict_kernel_extract.sh) is separate and unchanged.
#
# The committed .ml is a GENERATED source, checked in for a hermetic OCaml build
# that needs no Coq toolchain. dune's coq.theory stanza discards the .ml that
# building ExtractBytes.v emits, so drift is caught by
# scripts/tools/check_extract_identity.py, which re-runs this script (proof CI)
# and compares ASTs.
#
# Usage:  scripts/tools/regen_strict_kernel_extract.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

DEST_ML="latex-parse/strict/strict_bytes_extracted.ml"

# The kernel is its own theory (proofs/Strict/dune) and depends on the Coq
# standard library only, so only it needs building.
opam exec -- dune build --root . proofs/Strict

VODIR="$ROOT/_build/default/proofs"

# Resolve coqc once, from $ROOT (opam infers the switch from the cwd; CI uses a
# repo-local switch).
COQC="$(opam exec -- which coqc 2>/dev/null | tail -1)"
[ -x "$COQC" ] || COQC="$(command -v coqc || true)"
[ -x "$COQC" ] || { echo "ERROR: cannot locate coqc" >&2; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp proofs/Strict/ExtractBytes.v "$WORK/StrictExtractBytes.v"
( cd "$WORK" && "$COQC" -R "$VODIR" LaTeXPerfectionist StrictExtractBytes.v )

GEN_ML="$WORK/strict_bytes_extracted.ml"
if [ ! -f "$GEN_ML" ]; then
  echo "ERROR: extraction did not produce strict_bytes_extracted.ml" >&2
  exit 1
fi

HEADER='(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the strict-tier decision on bytes (ADR-012, M2
   phase 2): [decide_bytes] (proofs/Strict/DecideBytes.v), the lexer [lex]
   (proofs/Strict/Lexer.v), the parser [parse] (proofs/Strict/Front.v) and
   the phase-1 kernel they run, with the diagnostic [explain]
   (proofs/Strict/Explain.v). Regenerate with
   scripts/tools/regen_strict_bytes_extract.sh from proofs/Strict/ExtractBytes.v.

   [decide_bytes] is proved equal to the declarative reading, parse and
   semantics (decide_bytes_exact, lex_exact, parse_exact; Print Assumptions:
   Closed). Nothing in the product links this module (M3 wires it): it runs in
   strict_decide.exe (file mode) and the byte-level evidence
   (scripts/tools/strict_differential.py --bytes).

   nat is extracted to OCaml int (ExtrOcamlNatInt): token positions, line
   numbers, byte offsets, lengths and TeX group counts, all non-negative. *)

[@@@warning "-a"]
'

# Strip Coq's per-definition `(** val ... **)` comments (see
# regen_body_token_frontend_extract.sh for why).
STRIPPED="$WORK/stripped.ml"
awk '
  /^[[:space:]]*\(\*\* val / { skip=1 }
  skip { if ($0 ~ /\*\*\)[[:space:]]*$/) { skip=0 }; next }
  { print }
' "$GEN_ML" > "$STRIPPED"

{ printf '%s\n' "$HEADER"; cat "$STRIPPED"; } > "$DEST_ML"

# Canonicalise with dune's own formatter (the CI `format` gate's), unless the
# extract-identity gate asked to skip it (it compares ASTs).
DEST_DIR="$(dirname "$DEST_ML")"
DEST_BASE="$(basename "$DEST_ML")"
FMT_STAGE="$ROOT/_build/default/$DEST_DIR/.formatted/$DEST_BASE"
if [ "${EXTRACT_SKIP_FMT:-0}" = "1" ]; then
  echo "EXTRACT_SKIP_FMT=1: leaving $DEST_ML unformatted" >&2
else
  opam exec -- dune build --root "$ROOT" "@$DEST_DIR/fmt" >/dev/null 2>&1 || true
  if [ -f "$FMT_STAGE" ]; then
    cp "$FMT_STAGE" "$DEST_ML"
  else
    echo "WARNING: dune @fmt staging copy not found ($FMT_STAGE); leaving raw" >&2
  fi
fi

echo "Wrote $DEST_ML"
