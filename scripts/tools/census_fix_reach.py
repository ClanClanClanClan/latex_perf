#!/usr/bin/env python3
"""Census: how many real papers does each EDIT CLASS of the fixer touch?

WHY THIS EXISTS (OPEN-100, C-66).

OPEN-100's rule was "before writing any producer guard, state what makes it a
CLASS fix". That rule is necessary and it is not sufficient, and this script is
the missing half.

On 2026-09-20 the seven breaks in the untouched offset-2300 window were
bisected down to a genuine, provable class defect: ENC-015 rewrites U+00B5
MICRO SIGN to U+03BC GREEK SMALL MU, taking a document pdflatex compiles to one
it refuses -- NFKC is a relation on Unicode, typesettability is a relation on
LaTeX, and the rule assumed they were the same relation. A choke-point guard
was written, measured 4/4 against ENC-015's whole table, unit-tested, and shown
to repair the real paper end to end.

Then a grep over the corpus: the micro sign occurs in 14 of 2961 packages.
0.5%. The other three needles occur in ZERO. Expected effect on a 40-paper
window: 0.2 papers. The fix is correct and cannot move the rate.

That is C-57 again -- "fixing the papers in front of you is not the same
activity as reducing the rate" -- reached this time through a CORRECT class
fix. Being a real class says nothing about how big the class is. Reach is a
grep; the fix was an hour; verifying it on a window would have been three.
Cheapest first, always.

WHAT THIS MEASURES. Runs the default `--apply-fixes` over a deterministic slice
of the real corpus, diffs each file, and classifies every changed line by the
SHAPE of the edit, reporting paper-level reach (how many documents a class
touches at all) and line volume. Paper-level reach is the number that predicts
whether fixing a class can move a per-paper break rate; line volume is what
predicts blast radius inside a document.

CLI ONLY -- no pdflatex. Minutes, not hours. Run it BEFORE building a guard.

First run, offset 2400, 120 papers, none previously used for anything:

    whitespace-only                  116 papers  96.7%   22551 lines
    tie-inserted (space -> ~)         99 papers  82.5%    2693 lines
    non-ASCII substitution            88 papers  73.3%     522 lines
    math script reorder/edit          80 papers  66.7%    1341 lines
    negative-thinspace \\! DELETED      3 papers   2.5%      19 lines

117 of 120 papers are edited at all, and the out-of-sample break rate is 18.4%.
With every candidate break class at 66-97% reach, the breaks are not coming
from rare classes. The largest class by volume is whitespace normalisation,
which carries no user value and is not risk-free: it reflows macro definition
bodies (watched doing so to `\\@thanks` internals in 2506.16293v1, the paper
whose break is `! Double superscript.`).
"""
from __future__ import annotations

import argparse
import collections
import difflib
import hashlib
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

NORM = re.compile(r"\s+")


def classify(o: str, n: str) -> str:
    """Name the SHAPE of one changed line. Shapes, never rule ids.

    A rule id would tell us who made the edit; the shape tells us what kind of
    bet it is. Rule ids also drift, and the mapping from an applied byte edit
    back to its producer is not recorded in the artefact at all.
    """
    if NORM.sub(" ", o).strip() == NORM.sub(" ", n).strip():
        return "whitespace-only"
    sm = difflib.SequenceMatcher(None, o, n, autojunk=False)
    tags = set()
    for t, a1, a2, b1, b2 in sm.get_opcodes():
        if t == "equal":
            continue
        a, b = o[a1:a2], n[b1:b2]
        if a == " " and b == "~":
            tags.add("tie-inserted (space -> ~)")
        elif "\\!" in a and not b:
            tags.add("negative-thinspace \\! DELETED")
        elif re.search(r"[\^_]\{", a) or re.search(r"[\^_]\{", b):
            tags.add("math script reorder/edit")
        elif b != a and any(ord(c) > 127 for c in b):
            tags.add("non-ASCII substitution")
        elif a and not b:
            tags.add("deletion")
        elif b and not a:
            tags.add("insertion")
        else:
            tags.add("other replace")
    return ", ".join(sorted(tags)) if tags else "other"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--repo", default=".")
    ap.add_argument("--offset", type=int, default=2400)
    ap.add_argument("--n", type=int, default=120)
    ap.add_argument("--timeout", type=int, default=60)
    ns = ap.parse_args()

    repo = pathlib.Path(ns.repo).resolve()
    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    if not cli.is_file():
        print(f"[fix-reach] FATAL: {cli} not built", file=sys.stderr)
        return 2
    if not ns.corpus_root:
        print("[fix-reach] FATAL: no --corpus-root and LP_REAL_CORPUS unset. "
              "The corpus is not in this repo; see corpora/real_roots/README.md",
              file=sys.stderr)
        return 2
    root = pathlib.Path(ns.corpus_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[fix-reach] FATAL: {root} does not exist", file=sys.stderr)
        return 2

    # The corpus ordering, so a slice is reproducible and comparable to the
    # apply-fixes windows (which use the same rule).
    pkgs = sorted((p for p in root.iterdir() if p.is_dir()),
                  key=lambda p: hashlib.sha256(p.name.encode()).hexdigest())
    sample = pkgs[ns.offset:ns.offset + ns.n]
    if len(sample) < ns.n:
        print(f"[fix-reach] FATAL: frame has {len(pkgs)} packages; offset "
              f"{ns.offset} + n {ns.n} overruns it", file=sys.stderr)
        return 2

    papers: collections.Counter = collections.Counter()
    lines: collections.Counter = collections.Counter()
    touched = 0
    for pkg in sample:
        seen = set()
        # NEVER edit the corpus in place: it is the thing being measured, and
        # the manifest hashes it.
        with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
            work = pathlib.Path(td) / "w"
            shutil.copytree(pkg, work)
            for tex in sorted(work.rglob("*.tex")):
                try:
                    before = tex.read_bytes()
                except OSError:
                    continue
                try:
                    # --apply-fixes-all: this instrument measures the FULL fixer (every rule's
                    # fix), which is what the unqualified --apply-fixes meant before the
                    # OPEN-105 allow-list made it apply only Fix_policy.default_allowlist.
                    p = subprocess.run([str(cli), "--apply-fixes-all", str(tex)],
                                       capture_output=True, timeout=ns.timeout)
                except subprocess.TimeoutExpired:
                    raise RuntimeError(f"fixer timed out on {tex}")
                if p.returncode not in (0, 1):
                    # A crash is not "no edits": it would undercount reach.
                    raise RuntimeError(
                        f"fixer crashed (exit {p.returncode}) on {tex}: "
                        f"{p.stderr[-300:]!r}")
                # BYTES, never text=True: real papers carry latin-1 and strict
                # decoding raises mid-sweep (C-9 family).
                if not (p.returncode in (0, 1) and p.stdout
                        and p.stdout != before):
                    continue
                b = before.decode("utf-8", "replace").splitlines()
                a = p.stdout.decode("utf-8", "replace").splitlines()
                sm = difflib.SequenceMatcher(None, b, a, autojunk=False)
                for t, i1, i2, j1, j2 in sm.get_opcodes():
                    if t != "replace":
                        continue
                    for ob, oa in zip(b[i1:i2], a[j1:j2]):
                        c = classify(ob, oa)
                        lines[c] += 1
                        seen.add(c)
        if seen:
            touched += 1
        for c in seen:
            papers[c] += 1

    n = len(sample)
    print(f"[fix-reach] sample: {n} papers at offset {ns.offset}; "
          f"{touched} ({100*touched/n:.1f}%) edited at all\n")
    print(f"{'edit class':46s} {'papers':>7s} {'reach':>8s} {'lines':>9s}")
    print("-" * 74)
    for c, k in papers.most_common():
        print(f"{c[:46]:46s} {k:7d} {100*k/n:7.1f}% {lines[c]:9d}")
    print("\n[fix-reach] Paper-level reach bounds what fixing a class can do to "
          "a per-paper break rate. A class at 0.5% cannot move 18.4%, however "
          "real it is (C-66).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
