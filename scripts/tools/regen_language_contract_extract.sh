#!/usr/bin/env bash
# Regenerate the committed Coq→OCaml extraction of the proven tier classifier.
#
# Emits latex-parse/src/language_contract_extracted.ml from
# proofs/LanguageContractExtract.v (which extracts LanguageContract.classify +
# all its dependencies: tier / severity / feature / is_foreign /
# is_forbidden_core / any_foreign / any_forbidden_core).
#
# The committed .ml is a GENERATED source (like proofs/generated/*.v): it is
# checked in for a hermetic OCaml build that does not depend on a Coq toolchain,
# but is reproducible from the proofs by re-running this script. The build of
# proofs/LanguageContractExtract.v (via `dune build --root . proofs`) also
# exercises the extraction, so drift is caught by CI.
#
# Usage:  scripts/tools/regen_language_contract_extract.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

DEST_ML="latex-parse/src/language_contract_extracted.ml"

# Build the proofs so the .vo dependencies of LanguageContractExtract.v exist.
opam exec -- dune build --root . proofs

VODIR="$ROOT/_build/default/proofs"
GENDIR="$ROOT/_build/default/proofs/generated"

# Extraction emits its .ml/.mli into coqc's cwd, which dune's coq.theory stanza
# does not capture — so run coqc directly against the built theory in a temp dir.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp proofs/LanguageContractExtract.v "$WORK/"
( cd "$WORK" && opam exec -- coqc \
    -R "$VODIR" LaTeXPerfectionist \
    -Q "$GENDIR" LaTeXPerfectionist.Generated \
    LanguageContractExtract.v )

GEN_ML="$WORK/language_contract_extracted.ml"
if [ ! -f "$GEN_ML" ]; then
  echo "ERROR: extraction did not produce language_contract_extracted.ml" >&2
  exit 1
fi

# NOTE: the header comment below is PRE-WRAPPED to ocamlformat's fixpoint (the
# same line breaks `dune fmt` promotes). ocamlformat's comment reflow
# (wrap-comments=true) is not fully confluent — a differently-wrapped input can
# settle on a different stable state — so we feed it the already-canonical form
# to guarantee byte-identical, dune-fmt-clean output.
HEADER='(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the proven tier classifier
   [LanguageContract.classify] and all its dependencies (data model + boolean
   sub-checkers). Regenerate with
   scripts/tools/regen_language_contract_extract.sh from
   proofs/LanguageContractExtract.v.

   [classify] here is the PROVEN classifier itself (not a hand mirror): the Coq
   lemma [classify_lp_core_sound] (Qed, 0 admits) proves that an [LP_Core]
   verdict implies no forbidden-in-core feature is present. [Language_profile]
   executes this module for the tier DECISION (feature-list -> tier); only the
   bytes->feature-list step ([Unsupported_feature.detect]) stays trusted.

   nat is extracted to OCaml int (ExtrOcamlNatInt): feature ids are spec-level
   proxies, and classify performs no arithmetic on them. *)

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
