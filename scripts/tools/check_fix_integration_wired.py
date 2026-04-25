#!/usr/bin/env python3
"""Gate #16 (v26.2.1 PR #5): verify the E2E fix-integration test is
present and wired into the build so `dune runtest` exercises the
fire → collect → apply → re-validate pipeline on every CI run.

The test lives in `latex-parse/src/test_rule_fix_integration.ml` with
a matching dune stanza declaring the corpus fixtures as deps. The
gate fails if either is missing — prevents accidental detachment of
the E2E pipeline from the default CI run.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

TEST_ML = REPO_ROOT / "latex-parse" / "src" / "test_rule_fix_integration.ml"
DUNE = REPO_ROOT / "latex-parse" / "src" / "dune"
FIXTURES_DIR = REPO_ROOT / "corpora" / "fixtures" / "v26_2_1"
EXPECTED_FIXTURES = {
    "struct_001_missing_docclass.tex",
    "struct_001_with_bom.tex",
    "typo_002_multi_dashes.tex",
    "typo_003_multi_dashes.tex",
    "typo_002_collect_all.tex",
    "clean_docclass.tex",
}


def fail(msg: str) -> int:
    print(f"[fix-integration-wired] FAIL: {msg}")
    return 1


def main() -> int:
    if not TEST_ML.exists():
        return fail(f"missing test source: {TEST_ML.relative_to(REPO_ROOT)}")
    if not DUNE.exists():
        return fail(f"missing dune file: {DUNE.relative_to(REPO_ROOT)}")
    dune_text = DUNE.read_text()
    if "test_rule_fix_integration" not in dune_text:
        return fail(
            "latex-parse/src/dune has no stanza for test_rule_fix_integration"
        )
    # Confirm the dune stanza declares the fixtures dir as a dep
    # (otherwise the test can't locate the files under _build).
    if "corpora/fixtures/v26_2_1" not in dune_text:
        return fail(
            "test_rule_fix_integration stanza missing "
            "`(deps (source_tree ../../corpora/fixtures/v26_2_1))`"
        )
    if not FIXTURES_DIR.is_dir():
        return fail(
            f"missing fixtures directory: {FIXTURES_DIR.relative_to(REPO_ROOT)}"
        )
    present = {p.name for p in FIXTURES_DIR.glob("*.tex")}
    missing = EXPECTED_FIXTURES - present
    if missing:
        return fail(
            "fixtures directory is missing files: "
            + ", ".join(sorted(missing))
        )
    print(
        f"[fix-integration-wired] PASS: test + dune stanza + "
        f"{len(EXPECTED_FIXTURES)} fixtures in place."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
