#!/usr/bin/env python3
"""Synchronise [runtime_message] fields in `specs/rules/rules_v3.yaml`
with the actual runtime messages emitted by `validators_*.ml`.

Design rationale (v26.3.1+ catalogue↔runtime separation of concerns)
--------------------------------------------------------------------

`description` in `rules_v3.yaml` serves TWO masters: (a) human-
readable docs / IDE tooltips, (b) the validation contract that
`scripts/validate_messages.sh` checks against runtime emissions.

When the runtime message carries dynamic context (e.g.
`"Cross-file undefined reference(s): %s"`) the catalogue's prose
description (e.g. `"Undefined cross-file reference"`) is intentionally
the abstract form — making it useful for docs but causing
exact-match validation to fail for ~115 rules across the 600+ rule
set.

The future-proof fix:
- Keep `description` as the abstract human-readable form (no churn
  for downstream docs / IDE consumers).
- Add an OPTIONAL `runtime_message` field to rule entries when the
  runtime message differs from `description`.
- `scripts/validate_messages.sh` validates against
  `runtime_message` if present, else falls back to `description`.
- This script generates the `runtime_message` field for any rule
  whose runtime emission differs from the current description.
- Future runtime / docs changes can be made independently of each
  other; the validator gate catches drift either way.

Usage
-----

    python3 scripts/tools/sync_runtime_messages.py
        # Adds / updates / removes [runtime_message] fields in-place
        # so each rule's [runtime_message] (if present) matches the
        # current OCaml emission. Rules whose [description] already
        # matches runtime get no [runtime_message] field.

    python3 scripts/tools/sync_runtime_messages.py --check
        # Exit 1 if any rule's recorded [runtime_message] disagrees
        # with the actual runtime emission. No file edits.

The script is line-oriented (preserves comments and formatting) — it
inserts the new field after `description:` and before any other
field of the same rule entry.
"""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CATALOG = REPO / "specs" / "rules" / "rules_v3.yaml"
EXTRACTOR = REPO / "scripts" / "validate_messages.sh"


def decode_ocaml_escapes(s: str) -> str:
    """Decode OCaml string-literal escape sequences to their effective
    runtime bytes, then interpret the byte stream as UTF-8. OCaml's
    `\\xHH` is a RAW BYTE (not a Unicode codepoint), so a sequence
    like `\\xe2\\x80\\x93` is the 3-byte UTF-8 encoding of `–`
    (U+2013). A naive `chr(0xe2)` would give U+00E2 instead.

    We accumulate bytes in a bytearray then decode as UTF-8 at the
    end — matching what the OCaml runtime emits.

    Handles: \\\\ \\" \\xHH \\NNN (decimal triple) \\n \\t \\r .
    Order matters: \\\\ first so escaped backslashes don't mis-decode
    a following hex/octal sequence.
    """
    out = bytearray()
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c != "\\" or i + 1 >= n:
            out.extend(c.encode("utf-8")); i += 1; continue
        nxt = s[i + 1]
        if nxt == "\\":
            out.append(0x5c); i += 2
        elif nxt == '"':
            out.append(0x22); i += 2
        elif nxt == "n":
            out.append(0x0a); i += 2
        elif nxt == "t":
            out.append(0x09); i += 2
        elif nxt == "r":
            out.append(0x0d); i += 2
        elif nxt == "x" and i + 3 < n and re.match(r"[0-9a-fA-F]{2}", s[i+2:i+4]):
            out.append(int(s[i+2:i+4], 16)); i += 4
        elif nxt.isdigit() and i + 3 < n and s[i+2:i+4].isdigit():
            out.append(int(s[i+1:i+4], 10)); i += 4
        else:
            out.extend(c.encode("utf-8")); i += 1
    try:
        return out.decode("utf-8")
    except UnicodeDecodeError:
        return out.decode("latin-1")


def extract_runtime() -> dict[str, str]:
    """Re-implement the OCaml-aware message extractor in Python. Runs
    over every `validators_*.ml` and recovers (id, message) pairs.
    OCaml string escapes (`\\xHH`, `\\\\`, `\\"`, `\\n` etc.) are
    decoded to their effective runtime bytes so that different
    source-form choices converge. See decode_ocaml_escapes."""
    runtime = {}
    src_dir = REPO / "latex-parse" / "src"
    files = sorted(src_dir.glob("validators*.ml"))
    for f in files:
        text = f.read_text(errors="replace")
        cur_id = None
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            line = lines[i]
            m = re.search(r'(?:\bid\s*=|~id\s*:)\s*"([^"]+)"', line)
            if m:
                cur_id = m.group(1)
            if cur_id:
                # Same line: ~message:"..." or {|...|}
                m_qs = re.search(
                    r'(?:\bmessage\s*=|~message\s*:)\s*\{(\w*)\|(.+?)\|\1\}',
                    line,
                )
                m_dq = re.search(
                    r'(?:\bmessage\s*=|~message\s*:)\s*"((?:[^"\\]|\\.)*)"',
                    line,
                )
                m_cont = re.search(
                    r'(?:\bmessage\s*=|~message\s*:)\s*"(.*)\\\s*$',
                    line,
                )
                m_nl = re.search(
                    r'(?:\bmessage\s*=|~message\s*:)\s*$', line
                )
                if m_qs:
                    if cur_id not in runtime:
                        runtime[cur_id] = m_qs.group(2)
                    cur_id = None
                elif m_dq:
                    msg = decode_ocaml_escapes(m_dq.group(1))
                    if cur_id not in runtime:
                        runtime[cur_id] = msg
                    cur_id = None
                elif m_cont:
                    msg = m_cont.group(1)
                    while True:
                        i += 1
                        if i >= len(lines):
                            break
                        cont = lines[i].lstrip()
                        m_end = re.search(r'^(.*)"', cont)
                        if m_end:
                            msg += m_end.group(1)
                            break
                        cont = re.sub(r'\\\s*$', '', cont)
                        msg += cont
                    msg = decode_ocaml_escapes(msg)
                    if cur_id not in runtime:
                        runtime[cur_id] = msg
                    cur_id = None
                elif m_nl:
                    i += 1
                    if i >= len(lines):
                        break
                    nxt = lines[i]
                    m_qs2 = re.search(r'\{(\w*)\|(.+?)\|\1\}', nxt)
                    m_dq2 = re.search(r'"((?:[^"\\]|\\.)*)"', nxt)
                    m_cont2 = re.search(r'"(.*)\\\s*$', nxt)
                    if m_qs2:
                        if cur_id not in runtime:
                            runtime[cur_id] = m_qs2.group(2)
                        cur_id = None
                    elif m_dq2:
                        msg = decode_ocaml_escapes(m_dq2.group(1))
                        if cur_id not in runtime:
                            runtime[cur_id] = msg
                        cur_id = None
                    elif m_cont2:
                        msg = m_cont2.group(1)
                        while True:
                            i += 1
                            if i >= len(lines):
                                break
                            cont = lines[i].lstrip()
                            m_end = re.search(r'^(.*)"', cont)
                            if m_end:
                                msg += m_end.group(1)
                                break
                            cont = re.sub(r'\\\s*$', '', cont)
                            msg += cont
                        msg = decode_ocaml_escapes(msg)
                        if cur_id not in runtime:
                            runtime[cur_id] = msg
                        cur_id = None
            i += 1
    return runtime


def yaml_escape(s: str) -> str:
    """Escape a string so it can be a YAML double-quoted scalar."""
    return s.replace("\\", "\\\\").replace('"', '\\"')


def parse_catalogue(text: str) -> list[dict]:
    """Return list of rule entries with line ranges. Each entry is
    {id, description, runtime_message (or None), start_line,
    description_line, runtime_message_line (or None), end_line}."""
    rules = []
    lines = text.split("\n")
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = re.match(r'^- id:\s*"([^"]+)"\s*$', line)
        if not m:
            i += 1
            continue
        entry = {
            "id": m.group(1),
            "description": None,
            "runtime_message": None,
            "start_line": i,
            "description_line": None,
            "runtime_message_line": None,
        }
        i += 1
        while i < n:
            ln = lines[i]
            if ln.startswith("- ") or (ln.startswith("# ") and not ln.startswith("# ----")):
                # Next entry or section break
                break
            # Description: support both "..." and '...' YAML scalars.
            md_dq = re.match(r'^\s+description:\s*"((?:[^"\\]|\\.)*)"\s*$', ln)
            md_sq = re.match(r"^\s+description:\s*'((?:[^'\\]|\\.|'')*)'\s*$", ln)
            if md_dq:
                entry["description"] = md_dq.group(1).replace("\\\\", "\\").replace('\\"', '"')
                entry["description_line"] = i
            elif md_sq:
                # YAML single-quoted: '' = literal '
                entry["description"] = md_sq.group(1).replace("''", "'")
                entry["description_line"] = i
            mr = re.match(r'^\s+runtime_message:\s*"((?:[^"\\]|\\.)*)"\s*$', ln)
            if mr:
                entry["runtime_message"] = mr.group(1).replace("\\\\", "\\").replace('\\"', '"')
                entry["runtime_message_line"] = i
            i += 1
        entry["end_line"] = i
        rules.append(entry)
    return rules


def main() -> int:
    check_only = "--check" in sys.argv
    runtime = extract_runtime()
    text = CATALOG.read_text()
    rules = parse_catalogue(text)
    lines = text.split("\n")
    edits: list[tuple[int, str, str]] = []  # (line_index, op, new_line)
    needs_field = 0
    needs_update = 0
    needs_remove = 0
    matched = 0
    skipped_no_runtime = 0

    for rule in rules:
        rid = rule["id"]
        rt = runtime.get(rid)
        if rt is None:
            skipped_no_runtime += 1
            continue
        desc = rule["description"]
        cur_field = rule["runtime_message"]
        if rt == desc:
            # description suffices; runtime_message field unnecessary
            if cur_field is not None:
                # Remove stale runtime_message line
                edits.append((rule["runtime_message_line"], "delete", ""))
                needs_remove += 1
            else:
                matched += 1
        else:
            # Need a runtime_message field
            new_line = f'  runtime_message: "{yaml_escape(rt)}"'
            if cur_field is None:
                # Insert after description_line
                if rule["description_line"] is None:
                    print(f"WARN: rule {rid} has no description line; skipping")
                    continue
                edits.append((rule["description_line"], "insert_after", new_line))
                needs_field += 1
            elif cur_field != rt:
                edits.append((rule["runtime_message_line"], "replace", new_line))
                needs_update += 1
            else:
                matched += 1

    summary = (
        f"runtime: {len(runtime)} rules, catalogue: {len(rules)} rules, "
        f"new field: {needs_field}, updated: {needs_update}, "
        f"removed-stale: {needs_remove}, already-matching: {matched}, "
        f"runtime-not-found: {skipped_no_runtime}"
    )

    if check_only:
        if needs_field or needs_update or needs_remove:
            print(f"[runtime-msg-sync] FAIL: {summary}")
            print(f"[runtime-msg-sync] Run without --check to apply edits.")
            return 1
        print(f"[runtime-msg-sync] PASS: {summary}")
        return 0

    if not edits:
        print(f"[runtime-msg-sync] no edits needed: {summary}")
        return 0

    # Apply edits in REVERSE line order so indices stay valid.
    edits.sort(key=lambda e: -e[0])
    for line_idx, op, new_line in edits:
        if op == "delete":
            del lines[line_idx]
        elif op == "insert_after":
            lines.insert(line_idx + 1, new_line)
        elif op == "replace":
            lines[line_idx] = new_line

    new_text = "\n".join(lines)
    if not new_text.endswith("\n"):
        new_text += "\n"
    backup = CATALOG.with_suffix(".yaml.bak")
    shutil.copyfile(CATALOG, backup)
    CATALOG.write_text(new_text)
    print(f"[runtime-msg-sync] applied: {summary}")
    print(f"[runtime-msg-sync] backup at {backup.relative_to(REPO)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
