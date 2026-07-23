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
# exercises the extraction, so drift is caught by CI.
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
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp proofs/BodyTokenFrontEndExtract.v "$WORK/"
( cd "$WORK" && opam exec -- coqc \
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

# Canonicalise with ocamlformat so the committed generated file is @fmt-clean
# (dune fmt would otherwise flag it). --enable-outside-detected-project makes
# ocamlformat honour the repo-root .ocamlformat even though latex-parse/ is a
# nested dune sub-project without its own config. The file is byte-reproducible:
# regen -> same ocamlformat output as `dune fmt` promotes.
TMP_FMT="$(mktemp).ml"
opam exec -- ocamlformat --enable-outside-detected-project "$DEST_ML" > "$TMP_FMT"
mv "$TMP_FMT" "$DEST_ML"

echo "Wrote $DEST_ML"
