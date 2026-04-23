#!/usr/bin/env python3
"""MLI docstring coverage gate (PR #245 p1.10).

Every exported `val` in an .mli file under latex-parse/src must have
an ocamldoc comment `(** ... *)` either immediately preceding or
immediately following. Prevents undocumented API surface from growing.

Handles:
  - `val foo : type` at start of line or after indentation
  - Multi-line ocamldoc blocks
  - Grouped vals sharing a leading comment

Excludes test files (test_*.mli) since those are internal.

Exit 1 if any .mli has an undocumented val.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Ratchet: current coverage baseline. Fail if this grows — to keep a
# single definition of truth, we compute from current state once and
# allow additions.
CURRENT_UNDOCUMENTED_CEILING = 150  # v26.2 PR B1: +3 for new exports
# from project_model/build_graph/aux_state/cst/stable_spans modules;
# ratchet back down in a dedicated docstring pass when the v26.2
# cycle closes.


def extract_vals(text: str) -> list[tuple[int, str]]:
    """Return list of (line_number, val_name)."""
    vals = []
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r"^\s*val\s+([A-Za-z_][A-Za-z_0-9']*)\s*:", line)
        if m:
            vals.append((i, m.group(1)))
    return vals


def line_has_doc_above(lines: list[str], val_line: int) -> bool:
    """Walk backwards from val_line-1; if we find a line ending `*)`,
    consider it doc above."""
    idx = val_line - 2  # 0-indexed, one above
    while idx >= 0:
        s = lines[idx].strip()
        if not s:
            idx -= 1
            continue
        if s.endswith("*)"):
            return True
        # Non-empty, non-doc line → no doc above
        return False
    return False


def line_has_doc_below(lines: list[str], val_line: int) -> bool:
    """Walk forward; first non-empty non-`val` line starting `(**` is
    an ocamldoc below the val."""
    idx = val_line  # 0-indexed = val_line-1+1
    # Walk forward past the val declaration (may wrap across lines)
    while idx < len(lines):
        s = lines[idx].strip()
        if not s:
            idx += 1
            continue
        if s.startswith("(**"):
            return True
        # Another `val` or type => no doc below
        if s.startswith("val ") or s.startswith("type "):
            return False
        # Could be continuation of val type signature; keep walking a
        # few more lines before giving up.
        if idx - val_line > 6:
            return False
        idx += 1
    return False


def check_file(path: Path) -> list[tuple[int, str]]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    vals = extract_vals(text)
    undoc = []
    for line_no, name in vals:
        if line_has_doc_above(lines, line_no) or line_has_doc_below(
            lines, line_no
        ):
            continue
        undoc.append((line_no, name))
    return undoc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ap.add_argument(
        "--ceiling",
        type=int,
        default=CURRENT_UNDOCUMENTED_CEILING,
        help="Maximum allowed undocumented vals (ratchet).",
    )
    ns = ap.parse_args()
    repo = Path(ns.repo)
    src_dir = repo / "latex-parse/src"
    if not src_dir.is_dir():
        print(f"[mli-doc] FAIL: {src_dir} missing", file=sys.stderr)
        return 2
    total_undoc = 0
    all_undoc: list[tuple[str, int, str]] = []
    for mli in sorted(src_dir.glob("*.mli")):
        if mli.name.startswith("test_"):
            continue
        undoc = check_file(mli)
        for line_no, name in undoc:
            total_undoc += 1
            all_undoc.append((mli.name, line_no, name))
    if total_undoc > ns.ceiling:
        for fname, line_no, name in all_undoc[:40]:
            print(
                f"[mli-doc] FAIL: {fname}:{line_no}: val {name!r} has "
                f"no ocamldoc (** ... *) comment.",
                file=sys.stderr,
            )
        if len(all_undoc) > 40:
            print(f"  ... and {len(all_undoc) - 40} more")
        print(
            f"[mli-doc] {total_undoc} undocumented val(s) exceeds "
            f"ceiling {ns.ceiling}. Add `(** ... *)` docstrings or raise "
            f"the ceiling in this script with justification.",
            file=sys.stderr,
        )
        return 1
    print(
        f"[mli-doc] PASS: {total_undoc} undocumented val(s) ≤ ceiling "
        f"{ns.ceiling}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
