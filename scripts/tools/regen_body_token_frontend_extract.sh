#!/usr/bin/env bash
# Regenerate the committed Coq→OCaml extraction of the verified bytes→body_token
# front-end.
#
# Emits latex-parse/src/body_token_frontend_extracted.ml from
# proofs/BodyTokenFrontEndExtract.v (which extracts
# BodyTokenFrontEnd.body_of_source + all its dependencies: the label/ref
# scanners, the offset-sorted merge, the FNV-1a 30-bit hash, the feature
# detector, is_blank and in_ranges_b).
#
# The committed .ml is a GENERATED source (like proofs/generated/*.v): it is
# checked in for a hermetic OCaml build that does not depend on a Coq toolchain,
# but is reproducible from the proofs by re-running this script. The build of
# proofs/BodyTokenFrontEndExtract.v (via `dune build --root . proofs`) also
# exercises the extraction, but dune's coq.theory stanza DISCARDS the emitted
# .ml — so that build proves only that extraction still SUCCEEDS, never that the
# committed .ml still matches. Actual drift is caught by
# scripts/tools/check_extract_identity.py, which re-runs this script in CI
# (proof-ci) and compares the result against the committed file.
#
# Usage:  scripts/tools/regen_body_token_frontend_extract.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

DEST_ML="latex-parse/src/body_token_frontend_extracted.ml"

# Build the proofs so the .vo dependencies of BodyTokenFrontEndExtract.v exist.
opam exec -- dune build --root . proofs

VODIR="$ROOT/_build/default/proofs"
GENDIR="$ROOT/_build/default/proofs/generated"

# Extraction emits its .ml/.mli into coqc's cwd, which dune's coq.theory stanza
# does not capture — so run coqc directly against the built theory in a temp dir.
# Resolve coqc ONCE, from $ROOT, before entering the temp dir below. `opam exec`
# infers the switch from the CURRENT DIRECTORY, and CI uses a repo-local switch
# (_opam/) — so `opam exec -- coqc` run from a temp dir fails with "No switch is
# currently set". Resolving here keeps the invocation cwd-independent.
COQC="$(opam exec -- which coqc 2>/dev/null | tail -1)"
[ -x "$COQC" ] || COQC="$(command -v coqc || true)"
[ -x "$COQC" ] || { echo "ERROR: cannot locate coqc" >&2; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp proofs/BodyTokenFrontEndExtract.v "$WORK/"
( cd "$WORK" && "$COQC" \
    -R "$VODIR" LaTeXPerfectionist \
    -Q "$GENDIR" LaTeXPerfectionist.Generated \
    BodyTokenFrontEndExtract.v )

GEN_ML="$WORK/body_token_frontend_extracted.ml"
if [ ! -f "$GEN_ML" ]; then
  echo "ERROR: extraction did not produce body_token_frontend_extracted.ml" >&2
  exit 1
fi

HEADER='(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the VERIFIED bytes→body_token front-end
   [BodyTokenFrontEnd.body_of_source] and all its dependencies (label/ref
   scanners, offset-sorted merge, FNV-1a 30-bit hash, feature detector,
   is_blank, in_ranges_b). Regenerate with
   scripts/tools/regen_body_token_frontend_extract.sh from
   proofs/BodyTokenFrontEndExtract.v.

   [body_of_source] here is the PROVEN front-end itself (not a hand mirror):
   soundness/completeness of the scanners, sortedness of the merge and the
   premise-function bridges are Qed-proved in proofs/BodyTokenFrontEnd.v, and
   [compile_safe_of_source] (Print Assumptions: Closed) connects a body built
   by THIS code to [PdflatexModel.pdflatex_compile_safe]. [Compile_evidence]
   executes this module as the production extract-body path.

   nat is extracted to OCaml int (ExtrOcamlNatInt): every value stays below
   2^32 and the single product below 2^55 (fnv_mul_bound), inside OCaml 63-bit
   ints. *)

[@@@warning "-a"]
'

# Strip Coq's per-definition `(** val foo : ... **)` annotation comments
# (single- OR multi-line): they are noise, and their docstring re-wrapping is the
# only thing that makes ocamlformat output depend on invocation details (breaking
# byte-reproducibility vs `dune fmt`). Removing them makes the formatted file
# stable and deterministic.
STRIPPED="$WORK/stripped.ml"
awk '
  /^[[:space:]]*\(\*\* val / { skip=1 }
  skip { if ($0 ~ /\*\*\)[[:space:]]*$/) { skip=0 }; next }
  { print }
' "$GEN_ML" > "$STRIPPED"

{ printf '%s\n' "$HEADER"; cat "$STRIPPED"; } > "$DEST_ML"

# Canonicalise with `dune fmt` — the SAME formatter the CI `format` gate uses —
# so the committed generated file is byte-identical to what that gate expects.
# A standalone `ocamlformat` invocation resolves the nested latex-parse/ project's
# .ocamlformat config at a different comment margin than dune does, and would wrap
# the header comment differently (making the file @fmt-dirty in CI). We write the
# raw source above, let dune produce its canonical formatting into the .formatted
# staging copy, and copy that back. Byte-reproducible: regen -> exactly what CI's
# `dune build @fmt` promotes.
DEST_DIR="$(dirname "$DEST_ML")"
DEST_BASE="$(basename "$DEST_ML")"
FMT_STAGE="$ROOT/_build/default/$DEST_DIR/.formatted/$DEST_BASE"
# EXTRACT_SKIP_FMT=1 skips the ocamlformat canonicalisation below. The
# extract-identity gate (scripts/tools/check_extract_identity.py) sets it: that
# gate compares a CANONICAL form (comments stripped, whitespace collapsed), so
# formatting is irrelevant to it — and on the 90k-line front-end extract
# ocamlformat takes over an hour (it is superlinear on the deeply-nested unary
# Peano numerals Coq emits for numeric constants), which would blow any CI
# timeout. Humans regenerating for a commit must NOT set it: the committed file
# has to stay @fmt-clean or the `format` gate fails.
if [ "${EXTRACT_SKIP_FMT:-0}" = "1" ]; then
  echo "EXTRACT_SKIP_FMT=1: leaving $DEST_ML unformatted" >&2
else
  opam exec -- dune build --root "$ROOT" @fmt >/dev/null 2>&1 || true  # exits 1 on diff; still stages .formatted
  if [ -f "$FMT_STAGE" ]; then
    cp "$FMT_STAGE" "$DEST_ML"
  else
    echo "WARNING: dune @fmt staging copy not found ($FMT_STAGE); leaving raw" >&2
  fi
fi

echo "Wrote $DEST_ML"
