#!/usr/bin/env bash
# Regenerate the committed Coq→OCaml extraction of the capstone premise-checker.
#
# Emits latex-parse/src/compile_guarantee_extracted.ml from
# proofs/CompileGuaranteeExtract.v (which extracts
# CompileGuaranteeBridge.project_wf_dec + all its dependencies).
#
# The committed .ml is a GENERATED source (like proofs/generated/*.v): it is
# checked in for a hermetic OCaml build that does not depend on a Coq toolchain,
# but is reproducible from the proofs by re-running this script. The build of
# proofs/CompileGuaranteeExtract.v (via `dune build --root . proofs`) also
# exercises the extraction, so drift is caught by CI.
#
# Usage:  scripts/tools/regen_compile_guarantee_extract.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

DEST_ML="latex-parse/src/compile_guarantee_extracted.ml"

# Build the proofs so the .vo dependencies of CompileGuaranteeExtract.v exist.
opam exec -- dune build --root . proofs

VODIR="$ROOT/_build/default/proofs"
GENDIR="$ROOT/_build/default/proofs/generated"

# Extraction emits its .ml/.mli into coqc's cwd, which dune's coq.theory stanza
# does not capture — so run coqc directly against the built theory in a temp dir.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp proofs/CompileGuaranteeExtract.v "$WORK/"
( cd "$WORK" && opam exec -- coqc \
    -R "$VODIR" LaTeXPerfectionist \
    -Q "$GENDIR" LaTeXPerfectionist.Generated \
    CompileGuaranteeExtract.v )

GEN_ML="$WORK/compile_guarantee_extracted.ml"
if [ ! -f "$GEN_ML" ]; then
  echo "ERROR: extraction did not produce compile_guarantee_extracted.ml" >&2
  exit 1
fi

HEADER='(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the capstone premise-checker
   [CompileGuaranteeBridge.project_wf_dec] and all its dependencies (data model
   + boolean sub-checkers). Regenerate with
   scripts/tools/regen_compile_guarantee_extract.sh from
   proofs/CompileGuaranteeExtract.v.

   [project_wf_dec] here is the PROVEN checker itself (not a hand mirror): the
   Coq lemma [project_wf_dec_sound] (Qed, 0 admits) proves a [true] verdict is
   sufficient for [PdflatexModel.pdflatex_compile_safe]. [Compile_evidence]
   executes this module for the [--compile-check] decision.

   nat is extracted to OCaml int (ExtrOcamlNatInt): label ids are 30-bit hashes,
   for which a Peano representation would be catastrophic. *)

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
