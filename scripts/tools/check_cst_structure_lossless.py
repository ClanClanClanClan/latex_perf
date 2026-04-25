#!/usr/bin/env python3
"""Gate #17 (v26.3 §3 item C): verify the CST structure-lossless
runtime test is wired into the build so `dune runtest` exercises
it on every CI run.

Beyond v26.2's byte-lossless invariant
([Cst.serialize (Cst_of_ast.of_source src) = src]), v26.3
introduces a stronger structure-lossless check on a curated subset:
re-parsing the serialized CST yields a structurally equal CST.

The actual runtime check lives in
[latex-parse/src/test_cst_structure_lossless.ml]; this gate
verifies the test source + dune stanza + corpus deps are all in
place so the pipeline can't accidentally detach.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

TEST_ML = REPO_ROOT / "latex-parse" / "src" / "test_cst_structure_lossless.ml"
DUNE = REPO_ROOT / "latex-parse" / "src" / "dune"
CORPORA_ROUNDTRIP = REPO_ROOT / "corpora" / "roundtrip"
CORPORA_V26_2_1 = REPO_ROOT / "corpora" / "fixtures" / "v26_2_1"


def fail(msg: str) -> int:
    print(f"[cst-structure-lossless-wired] FAIL: {msg}")
    return 1


def main() -> int:
    if not TEST_ML.exists():
        return fail(f"missing test source: {TEST_ML.relative_to(REPO_ROOT)}")
    if not DUNE.exists():
        return fail(f"missing dune file: {DUNE.relative_to(REPO_ROOT)}")
    text = DUNE.read_text()
    if "test_cst_structure_lossless" not in text:
        return fail(
            "latex-parse/src/dune has no stanza for "
            "test_cst_structure_lossless"
        )
    if "corpora/roundtrip" not in text:
        return fail(
            "test_cst_structure_lossless stanza missing "
            "`(deps (source_tree ../../corpora/roundtrip))`"
        )
    if "corpora/fixtures/v26_2_1" not in text:
        return fail(
            "test_cst_structure_lossless stanza missing the v26_2_1 fixtures dep"
        )
    if not CORPORA_ROUNDTRIP.is_dir():
        return fail(
            f"missing corpus dir: {CORPORA_ROUNDTRIP.relative_to(REPO_ROOT)}"
        )
    if not CORPORA_V26_2_1.is_dir():
        return fail(
            f"missing corpus dir: {CORPORA_V26_2_1.relative_to(REPO_ROOT)}"
        )
    print(
        "[cst-structure-lossless-wired] PASS: test + dune stanza + "
        "corpus deps in place."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
