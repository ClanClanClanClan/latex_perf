#!/usr/bin/env python3
"""Gate (v26.2.1 PR #1): reject raw [Validators_common.result] record
literals in [latex-parse/src/validators_*.ml] and test files.

Rationale
---------
v26.2.1 introduced [Validators_common.mk_result] and
[mk_result_with_fix] helpers so that the new [fix : Cst_edit.t list
option] field is only produced in one place. New rules that construct
[result] values directly as record literals bypass the helper and will
fail to compile when future fields are added. This gate makes the
invariant machine-checked.

The gate scans every validator source and test file, detects any
4-field [{ id = ...; severity = ...; message = ...; count = ... }]
record literal (OCaml-aware on strings, char literals, quoted strings
and comments), and fails if one is found.

Escape hatch: none. If a helper is insufficient (e.g. because a new
field needs a non-[None] default), extend the helper signature instead
of bypassing it.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Reuse the OCaml-aware parser from the migration script.
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tools"))
from migrate_result_literals import (  # noqa: E402
    try_parse_result_literal,
    skip_string,
    skip_comment,
    try_skip_quoted_string,
    try_skip_char_literal,
)


def count_raw_literals(path: Path) -> list[tuple[int, str]]:
    """Return a list of (line_number, first_field_excerpt) for each raw
    result record literal found in [path]."""
    text = path.read_text()
    n = len(text)
    hits: list[tuple[int, str]] = []
    i = 0
    while i < n:
        c = text[i]
        if c == '"':
            i = skip_string(text, i)
        elif c == "'":
            ch = try_skip_char_literal(text, i)
            if ch is not None:
                i = ch
            else:
                i += 1
        elif text[i : i + 2] == "(*":
            i = skip_comment(text, i)
        elif c == "{":
            qs = try_skip_quoted_string(text, i)
            if qs is not None:
                i = qs
                continue
            parsed = try_parse_result_literal(text, i)
            if parsed is not None:
                end, _prefix, vals = parsed
                line = text.count("\n", 0, i) + 1
                hits.append((line, vals[0][:40]))
                i = end
            else:
                i += 1
        else:
            i += 1
    return hits


def main() -> int:
    src = REPO_ROOT / "latex-parse" / "src"
    targets = sorted(
        set(src.glob("validators*.ml"))
        | set(src.glob("test_validators*.ml"))
        | set(src.glob("test_chunk_store.ml"))
        | set(src.glob("test_edf_scheduler.ml"))
        | set(src.glob("test_evidence_scoring.ml"))
    )
    total_hits = 0
    for f in targets:
        hits = count_raw_literals(f)
        for line, excerpt in hits:
            rel = f.relative_to(REPO_ROOT).as_posix()
            print(
                f"[result-helpers] FAIL: {rel}:{line}: raw result "
                f"record literal (id={excerpt}); use "
                f"Validators_common.mk_result / mk_result_with_fix."
            )
            total_hits += 1
    if total_hits > 0:
        print(
            f"[result-helpers] FAIL: {total_hits} raw literal(s) remain. "
            f"Introduced in v26.2.1 PR #1; see "
            f"specs/v26/V26_2_1_PLAN.md §3 PR #1."
        )
        return 1
    print("[result-helpers] PASS: no raw result record literals.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
