#!/usr/bin/env python3
"""One-shot migration (v26.2.1 PR #1): rewrite every
[Validators_common.result] record literal to use the
[mk_result]/[mk_result_with_fix] helpers so the new [fix] field is
introduced without touching every callsite manually.

Pattern matched (whitespace/comments tolerated everywhere):

    { id = <expr>; severity = <expr>; message = <expr>; count = <expr>; }

Rewritten to:

    (mk_result ~id:(<expr>) ~severity:(<expr>) ~message:(<expr>) ~count:(<expr>))

After a full repo sweep, run `dune fmt --auto-promote` to normalise
formatting. The script itself is intentionally minimal and is DELETED
when PR #1 lands (see specs/v26/V26_2_1_PLAN.md §3 PR #1).

The parser is OCaml-aware on strings and nested comments — it does NOT
trip on semicolons inside quoted messages or `(* comments *)`.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def skip_string(text: str, i: int) -> int:
    """[text[i]] must be '"'. Return index just past the closing unescaped
    quote (or end-of-text if unterminated)."""
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


_QSTR_OPEN = re.compile(r"\{([a-z_]*)\|")

# OCaml character literal: 'c', '\n', '\xFF', '\065', etc.
# NOT a type variable ('a, 'foo).
_CHAR_LITERAL = re.compile(
    r"'(?:\\x[0-9a-fA-F]{1,2}|\\[0-9]{1,3}|\\.|[^'\\])'"
)


def try_skip_char_literal(text: str, i: int) -> int | None:
    """If [text[i:]] starts an OCaml character literal, return the index
    just past its closing quote. Otherwise None. Distinguishes from
    type variables (['a, 'foo])."""
    m = _CHAR_LITERAL.match(text, i)
    if not m:
        return None
    return m.end()


def try_skip_quoted_string(text: str, i: int) -> int | None:
    """If [text[i:]] starts an OCaml quoted-string literal
    [{delim|...|delim}], return the index just past it. Otherwise None.
    Quoted strings are opened with '{<delim>|' where <delim> is a
    (possibly empty) lowercase-id, and closed with '|<delim>}'."""
    m = _QSTR_OPEN.match(text, i)
    if not m:
        return None
    delim = m.group(1)
    close = "|" + delim + "}"
    end = text.find(close, m.end())
    if end < 0:
        return None
    return end + len(close)


def skip_comment(text: str, i: int) -> int:
    """[text[i:i+2]] must be '(*'. Return index just past the matching
    '*)'. Handles nested comments. Does NOT parse strings inside
    comments (OCaml comments are allowed to contain anything as long as
    nested comments + string-like constructs balance — we just track
    comment depth)."""
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


def extract_value(text: str, i: int) -> tuple[int, str]:
    """Extract an OCaml expression starting at [text[i]] until the next
    ';' or '}' at nesting depth 0. Respects string literals (both
    ["..."] and [{delim|...|delim}]), comments, and
    bracket/paren/brace nesting. Returns (end_index, value_string)
    where [text[end_index]] is the terminator."""
    n = len(text)
    depth = 0
    start = i
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


def try_parse_result_literal(
    text: str, start: int
) -> tuple[int, str, list[str]] | None:
    """[text[start]] must be '{'. Try to parse a four-field result
    literal in the required order id/severity/message/count. Returns
    (end_index_after_}, module_prefix, [id_val, sev_val, msg_val, cnt_val])
    or None if the record doesn't match the expected shape.
    [module_prefix] is e.g. "Validators_common." if the first field was
    qualified, or "" otherwise — callers use it to qualify the helper
    name in the replacement."""
    assert text[start] == "{"
    n = len(text)
    i = start + 1
    i = skip_ws_and_comments(text, i)
    values: list[str] = []
    prefix = ""
    for idx, expected in enumerate(FIELD_ORDER):
        # First field may be qualified: `Validators_common.id = ...` or
        # `Latex_parse_lib.Validators_common.id = ...`. Subsequent
        # fields are always bare (OCaml infers record type from first).
        if idx == 0:
            pattern = r"((?:[A-Z][a-zA-Z0-9_]*\.)*)" + re.escape(expected) + r"\s*="
            m = re.match(pattern, text[i:])
            if not m:
                return None
            prefix = m.group(1)
        else:
            pattern = re.escape(expected) + r"\s*="
            m = re.match(pattern, text[i:])
            if not m:
                return None
        i += m.end()
        i = skip_ws_and_comments(text, i)
        end, value = extract_value(text, i)
        values.append(value)
        i = end
        if idx < len(FIELD_ORDER) - 1:
            # Require ';' between fields
            if i >= n or text[i] != ";":
                return None
            i += 1
            i = skip_ws_and_comments(text, i)
    # Optional trailing ';' after count
    if i < n and text[i] == ";":
        i += 1
    i = skip_ws_and_comments(text, i)
    if i >= n or text[i] != "}":
        return None
    return (i + 1, prefix, values)


def migrate_file(path: Path, *, dry_run: bool = False) -> int:
    text = path.read_text()
    n = len(text)
    out: list[str] = []
    i = 0
    replacements = 0
    while i < n:
        c = text[i]
        if c == '"':
            end = skip_string(text, i)
            out.append(text[i:end])
            i = end
        elif c == "'":
            ch = try_skip_char_literal(text, i)
            if ch is not None:
                out.append(text[i:ch])
                i = ch
            else:
                out.append(c)
                i += 1
        elif text[i : i + 2] == "(*":
            end = skip_comment(text, i)
            out.append(text[i:end])
            i = end
        elif c == "{":
            qs = try_skip_quoted_string(text, i)
            if qs is not None:
                out.append(text[i:qs])
                i = qs
                continue
            parsed = try_parse_result_literal(text, i)
            if parsed is not None:
                end, prefix, vals = parsed
                id_v, sev_v, msg_v, cnt_v = vals
                replacement = (
                    f"({prefix}mk_result ~id:({id_v}) ~severity:({sev_v}) "
                    f"~message:({msg_v}) ~count:({cnt_v}))"
                )
                out.append(replacement)
                i = end
                replacements += 1
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    new_text = "".join(out)
    if replacements > 0 and not dry_run:
        path.write_text(new_text)
    return replacements


def main() -> int:
    src = REPO_ROOT / "latex-parse" / "src"
    # All validator files + tests that build result literals.
    # Intentionally broad — the parser only rewrites actual 4-field
    # result records; other `{...}` blocks are left untouched.
    targets = sorted(
        set(src.glob("validators*.ml"))
        | set(src.glob("test_validators*.ml"))
        | set(src.glob("test_chunk_store.ml"))
        | set(src.glob("test_edf_scheduler.ml"))
    )
    dry = "--dry" in sys.argv
    total = 0
    for f in targets:
        n = migrate_file(f, dry_run=dry)
        if n > 0:
            print(f"{f.relative_to(REPO_ROOT)}: {n} literals")
            total += n
    print(f"Total: {total} literals across {sum(1 for f in targets if f.exists())} files scanned")
    return 0


if __name__ == "__main__":
    sys.exit(main())
