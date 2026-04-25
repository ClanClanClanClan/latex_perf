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

The OCaml-aware parser was originally in
[scripts/tools/migrate_result_literals.py] (one-shot migration script,
deleted after PR #1 landed per plan §3 PR #1). It now lives inline
here so the gate is self-contained.

Escape hatch: none. If a helper is insufficient (e.g. because a new
field needs a non-[None] default), extend the helper signature instead
of bypassing it.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


# ── OCaml-aware parser (inline; see commit history for the migration
# script that originally hosted these). ───────────────────────────────


def skip_string(text: str, i: int) -> int:
    """[text[i]] must be '"'. Return index just past the closing
    unescaped quote (or end-of-text if unterminated)."""
    assert text[i] == '"'
    n = len(text)
    i += 1
    while i < n:
        c = text[i]
        if c == "\\" and i + 1 < n:
            i += 2
        elif c == '"':
            return i + 1
        else:
            i += 1
    return i


def skip_comment(text: str, i: int) -> int:
    """[text[i:i+2]] must be '(*'. Return index just past matching
    '*)'. Handles nested comments."""
    assert text[i : i + 2] == "(*"
    n = len(text)
    i += 2
    depth = 1
    while i + 1 < n:
        if text[i : i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i : i + 2] == "*)":
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    return n


def skip_ws_and_comments(text: str, i: int) -> int:
    n = len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text[i : i + 2] == "(*":
            i = skip_comment(text, i)
        else:
            break
    return i


_QSTR_OPEN = re.compile(r"\{([a-z_]*)\|")

_CHAR_LITERAL = re.compile(
    r"'(?:\\x[0-9a-fA-F]{1,2}|\\[0-9]{1,3}|\\.|[^'\\])'"
)


def try_skip_char_literal(text: str, i: int) -> int | None:
    m = _CHAR_LITERAL.match(text, i)
    return m.end() if m else None


def try_skip_quoted_string(text: str, i: int) -> int | None:
    m = _QSTR_OPEN.match(text, i)
    if not m:
        return None
    delim = m.group(1)
    close = "|" + delim + "}"
    end = text.find(close, m.end())
    if end < 0:
        return None
    return end + len(close)


def extract_value(text: str, i: int) -> tuple[int, str]:
    n = len(text)
    depth = 0
    start = i
    while i < n:
        c = text[i]
        if c == '"':
            i = skip_string(text, i)
        elif c == "'":
            ch = try_skip_char_literal(text, i)
            i = ch if ch is not None else i + 1
        elif text[i : i + 2] == "(*":
            i = skip_comment(text, i)
        elif c == "{":
            qs = try_skip_quoted_string(text, i)
            if qs is not None:
                i = qs
            else:
                depth += 1
                i += 1
        elif c in "([":
            depth += 1
            i += 1
        elif c in "})]":
            if depth == 0:
                return (i, text[start:i].strip())
            depth -= 1
            i += 1
        elif c == ";" and depth == 0:
            return (i, text[start:i].strip())
        else:
            i += 1
    return (i, text[start:i].strip())


FIELD_ORDER = ("id", "severity", "message", "count")


def try_parse_result_literal(text: str, start: int) -> int | None:
    """[text[start]] must be '{'. Return end index (just past '}') if
    a four-field result literal is recognised. Returns None
    otherwise. We only care about presence/position, not field
    values, so the return signature is simpler than the migration
    script's."""
    assert text[start] == "{"
    n = len(text)
    i = start + 1
    i = skip_ws_and_comments(text, i)
    for idx, expected in enumerate(FIELD_ORDER):
        if idx == 0:
            pattern = r"(?:[A-Z][a-zA-Z0-9_]*\.)*" + re.escape(expected) + r"\s*="
        else:
            pattern = re.escape(expected) + r"\s*="
        m = re.match(pattern, text[i:])
        if not m:
            return None
        i += m.end()
        i = skip_ws_and_comments(text, i)
        end, _value = extract_value(text, i)
        i = end
        if idx < len(FIELD_ORDER) - 1:
            if i >= n or text[i] != ";":
                return None
            i += 1
            i = skip_ws_and_comments(text, i)
    if i < n and text[i] == ";":
        i += 1
    i = skip_ws_and_comments(text, i)
    if i >= n or text[i] != "}":
        return None
    return i + 1


def count_raw_literals(path: Path) -> list[tuple[int, str]]:
    """Return [(line_number, first_chars_at_brace)] for each raw
    4-field result record literal found in [path]."""
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
            i = ch if ch is not None else i + 1
        elif text[i : i + 2] == "(*":
            i = skip_comment(text, i)
        elif c == "{":
            qs = try_skip_quoted_string(text, i)
            if qs is not None:
                i = qs
                continue
            end = try_parse_result_literal(text, i)
            if end is not None:
                line = text.count("\n", 0, i) + 1
                hits.append((line, text[i : i + 40].replace("\n", " ")))
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
                f"record literal at `{excerpt}`; use "
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
