#!/usr/bin/env python3
"""Gate: no document may claim the AUTO-FIX channel is *proven* safe.

Why this exists. Until v27.1.63 the repo said, in four separate places, that
`--apply-fixes` applies "proven-safe" / "proven byte-safe" / "always safe"
auto-fixes. Nothing in proofs/ justified any of it:

    $ grep -rlniE 'fix_guard|apply_fixes' proofs/
    (nothing)

The Cst_edit theorems that do exist are about the edit APPLIER under a
non-overlap hypothesis; they say nothing about whether the bytes a producer
chose to rewrite were safe to rewrite. Meanwhile the fixer was demonstrably
corrupting documents: corpora/apply_fixes/manifest.json recorded rows where
--apply-fixes took a compiling document to a non-compiling one while
--compile-check reported READY on both sides.

What IS true is empirical and should be said that way: Fix_guard withholds edits
landing in load-bearing byte ranges, and the round-trip corpus measures the
residual against real pdflatex. "Guard-gated", not "proven".

The banned vocabulary is deliberately narrow -- words that assert a PROOF, plus
the two absolutes. Weaker empirical phrasing ("corruption-free" about one
specific mechanical swap) is left alone; this gate is about the word "proven",
not about confidence in general.

A hit only fails when the sentence is actually ABOUT the auto-fix channel
(SCOPE) and is not talking about the review-only candidate channel (EXEMPT),
which genuinely never mutates a document.

Exit 1 on any violation.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

BANNED = re.compile(
    r"proven[-\s]?(byte[-\s]?)?safe|provably[-\s]?safe|verified[-\s]?safe"
    r"|guaranteed[-\s]?safe|always safe|safe everywhere",
    re.I)

SCOPE = re.compile(r"--apply-fixes|auto[-\s]?fix|bucket[-\s]?A|fix[-\s]producer", re.I)

# Deliberately NARROW, and matched on the OFFENDING LINE ONLY.
#
# An earlier version matched bare "candidate"/"surfaced" across a +/-2 line
# window and caught 1 of 4 restored claims: these documents discuss both channels
# in adjacent lines, and ROADMAP:18 names "124 candidates" in a COUNT on the very
# same line as its claim about applying fixes. A window-scoped exemption reads
# every one of those as "this sentence is about candidates" and goes quiet.
#
# So the exemption must be a phrase that actually SCOPES the claim to the
# review-only channel, not merely a mention of it.
EXEMPT = re.compile(
    r"never auto[-\s]?appl|review[-\s]only|surfaced only|candidate channel"
    r"|not auto[-\s]?appl", re.I)

# Historical release notes and archives are a RECORD of what was believed at the
# time. Rewriting them would be dishonest in the other direction, and editing
# CHANGELOG risks check_release_integrity.
SKIP_PARTS = ("CHANGELOG.md", "/archive/", "docs/archive/", "proofs/archive/")

SCAN_SUFFIXES = (".md",)
SCAN_ROOTS = ("README.md", "docs", "specs")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    files: list[Path] = []
    for root in SCAN_ROOTS:
        p = repo / root
        if p.is_file():
            files.append(p)
        elif p.is_dir():
            files.extend(q for q in p.rglob("*") if q.suffix in SCAN_SUFFIXES)
    files = [f for f in files if not any(s in str(f) for s in SKIP_PARTS)]

    # Non-vacuity. A gate that silently scans nothing reports PASS forever; this
    # repo shipped one that did exactly that for 185 days.
    if len(files) < 20:
        print(f"FAIL: scanned only {len(files)} document(s) — refusing to pass "
              f"vacuously. Check SCAN_ROOTS.", file=sys.stderr)
        return 1

    findings: list[str] = []
    for f in sorted(files):
        lines = f.read_text(errors="replace").split("\n")
        for i, line in enumerate(lines):
            m = BANNED.search(line)
            if not m:
                continue
            # SCOPE may be established by nearby context (a heading, the line
            # above), but EXEMPT must be on the offending line itself -- see the
            # note on EXEMPT for why a windowed exemption silences real hits.
            window = "\n".join(lines[max(0, i - 2): i + 3])
            if not SCOPE.search(window) or EXEMPT.search(line):
                continue
            findings.append(
                f"{f.relative_to(repo)}:{i + 1}: {m.group(0)!r} — "
                f"the auto-fix channel is guard-gated, not proven. "
                f"Nothing in proofs/ constrains it.\n      {line.strip()[:120]}")

    if findings:
        print(f"[fix-safety-language] FAIL: {len(findings)} unproven safety "
              f"claim(s) about the auto-fix channel", file=sys.stderr)
        for x in findings:
            print(f"  - {x}", file=sys.stderr)
        return 1

    print(f"[fix-safety-language] PASS: {len(files)} documents carry no "
          f"proof-claim about the auto-fix channel")
    return 0


if __name__ == "__main__":
    sys.exit(main())
