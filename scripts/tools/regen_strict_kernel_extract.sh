#!/usr/bin/env bash
# Regenerate the committed Coq→OCaml extraction of the strict-tier kernel L_S0
# (ADR-012, milestone M2 phase 1).
#
# Emits latex-parse/strict/strict_kernel_extracted.ml from
# proofs/Strict/Extract.v: the decider Decide.decide, the byte printer
# Syntax.render and their dependencies. The proofs about them
# (strict_decider_exact, runs_deterministic, runs_total, in_strict_dec,
# Bridge.strict_ready_iff_pdflatex) are in proofs/Strict/*.v.
#
# The committed .ml is a GENERATED source, checked in for a hermetic OCaml build
# that needs no Coq toolchain. dune's coq.theory stanza discards the .ml that
# building Extract.v emits, so drift is caught by
# scripts/tools/check_extract_identity.py, which re-runs this script (proof CI)
# and compares ASTs.
#
# Usage:  scripts/tools/regen_strict_kernel_extract.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

DEST_ML="latex-parse/strict/strict_kernel_extracted.ml"

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
cp proofs/Strict/Extract.v "$WORK/StrictExtract.v"
( cd "$WORK" && "$COQC" -R "$VODIR" LaTeXPerfectionist StrictExtract.v )

GEN_ML="$WORK/strict_kernel_extracted.ml"
if [ ! -f "$GEN_ML" ]; then
  echo "ERROR: extraction did not produce strict_kernel_extracted.ml" >&2
  exit 1
fi

HEADER='(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the strict-tier kernel L_S0 (ADR-012, M2 phase 1):
   [decide] (proofs/Strict/Decide.v) and [render] (proofs/Strict/Syntax.v)
   with their dependencies. Regenerate with
   scripts/tools/regen_strict_kernel_extract.sh from proofs/Strict/Extract.v.

   [decide] is proved equal, in both directions, to the declarative semantics
   [Runs] (strict_decider_exact; Print Assumptions: Closed). Nothing in the
   product links this module: phase 1 runs it only in the generated
   differential (scripts/tools/strict_differential.py via strict_decide.exe).

   nat is extracted to OCaml int (ExtrOcamlNatInt): the only nats are token
   positions, non-negative and bounded by the length of the token list. *)

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
