#!/usr/bin/env python3
"""The TeX install canary of tex-oracle.yml, through the ONE oracle (OPEN-128).

WHY. A missing .sty grades identically to the intended fatal (strong-fatal),
so an under-provisioned image would let fixtures report `ok` while testing
nothing; the canary proves the install compiles the corpus feature set BEFORE
anything is graded (R7-INFRA-2; OPEN-040/C-38 for the tree names). It used to
be a `docker run --rm -i "$TEX_IMAGE" bash -s` heredoc in the workflow: a
second way of starting the image, with the image's defaults (no read-only
root, no fixed clock, root user). ADR-015 E15 (owner, 2026-10-06) makes the
oracle's launch definition the ONLY one, and check_oracle_pin.py refuses a
workflow step that starts the image itself; so the canary runs its documents
through `_oracle.get_oracle()` like every grader, and reads the image's files
through `image_command`.

Checks, each a FAILURE (exit 1) when it does not hold:
  * canary.tex (inputenc, T1 fontenc, amsmath/amssymb, graphicx, hyperref,
    listings, tikz) compiles: rc 0 AND a PDF pdfTeX wrote (one graded pass,
    -halt-on-error);
  * kpsewhich finds every package file of PACKAGES in the image;
  * every Texmf_tree_allowlist name of TREE_NAMES compiles through a preamble
    \\input with no local copy, one document per name (the pictex family
    interacts, so they are not combined).
Exit 2 = the oracle is unavailable (an infrastructure failure, never a pass).
Prints "canary OK" on success: the workflow greps for it.

Run: python3 scripts/tools/oracle_canary.py
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

CANARY = r"""\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,graphicx,hyperref,listings,tikz}
\begin{document}
Caf\'e \`a \c{c} $\alpha^2$
\begin{tikzpicture}\draw (0,0)--(1,1);\end{tikzpicture}
\end{document}
"""
# fontspec/polyglossia matter: six false-READY fixtures ARE package-loading
# tricks, and a missing .sty grades strong-fatal -- identical to the intended
# fatal -- so without these they would pass while testing nothing.
PACKAGES = ("tikz.sty", "hyperref.sty", "amsmath.sty", "listings.sty",
            "inputenc.sty", "fontspec.sty", "polyglossia.sty", "pdftex.map")
# OPEN-040/C-38: the TREE is part of the oracle pin.
TREE_NAMES = ("xy", "xypic", "amssym.def", "epsf", "epsf.sty", "colordvi",
              "pictexwd.tex", "prepictex", "postpictex", "pdf-trans")
TIMEOUT = 300


def compiles(o, tex: str, what: str) -> tuple[bool, str]:
    with o.tempdir(prefix="lp-canary-") as td:
        d = Path(td)
        (d / "t.tex").write_text(tex, encoding="utf-8")
        r = o.run_pass(d, "t.tex", o.tex_env(), TIMEOUT)
        log = _oracle.job_output(d, "t.tex", ".log")
        tail = log.read_text(errors="replace")[-1500:] if log.is_file() else ""
    if r.timed_out:
        return False, f"{what}: timed out"
    return r.compiles, f"{what}: rc {r.rc}, pdf {r.pdf}\n{tail}"


def main() -> int:
    try:
        o = _oracle.get_oracle()
    except _oracle.OracleError as e:
        print(f"[canary] FATAL: the oracle is unavailable: {e}", file=sys.stderr)
        return 2
    print(f"[canary] oracle: {o.banner} ({_oracle.IMAGE}, {o.provenance()['arch']}, "
          f"clock {_oracle.PROTOCOL_CLOCK})")
    fails = []
    try:
        ok, msg = compiles(o, CANARY, "canary.tex")
        if not ok:
            fails.append("CANARY FAILED - the pinned image cannot compile the "
                         "corpus feature set: " + msg)
        for f in PACKAGES:
            rc, out, err = o.image_command(["kpsewhich", f])
            if rc != 0 or not out.strip():
                fails.append(f"MISSING: {f} (kpsewhich rc {rc})")
        for n in TREE_NAMES:
            ok, msg = compiles(o, "\\documentclass{article}\n\\input %s\n"
                               "\\begin{document}\nx\n\\end{document}\n" % n,
                               f"tree name {n}")
            if not ok:
                fails.append(f"TREE MISSING/BROKEN: {n}: {msg}")
    except _oracle.OracleError as e:
        print(f"[canary] FATAL: the oracle failed (not a canary result): {e}",
              file=sys.stderr)
        return 2
    if fails:
        for f in fails:
            print(f"[canary] {f}", file=sys.stderr)
        return 1
    print("canary OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
