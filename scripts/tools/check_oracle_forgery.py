#!/usr/bin/env python3
"""check_oracle_forgery.py -- the REAL pdfTeX cannot be made to grade a
document that wrote the oracle's own evidence (C-99, OPEN-118 review rounds
3 and 4).

check_oracle_infra_grading.py is pure: its engine and supervisor are fakes,
and its real-supervisor checks run on Linux only. Neither can see the
backend where review round 4's gap lived: the container oracle on a Mac,
whose work root is virtiofs over a case- and Unicode-insensitive APFS, so
DOC.log IS doc.log. This gate runs real documents through the real oracle
(`get_oracle()`: the native backend inside the pinned image in CI, the
container backend on a developer's Mac), so each forgery below is refused
on the backend it targets:

  forge_log      \\openout of its own \\jobname.log while pdfTeX holds it, a
                 forged "Output written" line past the real log's end, a
                 13-byte fake PDF (round 3, H1)
  forge_link     the same through a symlink shipped with the source
  forge_case     the same under a case variant (DOC.log / Doc.pdf, a new
                 variant each pass), then \\batchmode (round 4, HIGH)
  forge_term     a forged terminal report, pdfTeX's silenced by \\batchmode
and the genuine shapes still grade exactly:
  ok             a page ships                         -> compiles
  nopages        rc 0, "No pages of output."          -> not compiles
  synctex        \\synctex=1, a page ships             -> compiles (round 4)
  batchok        \\batchmode, a page ships             -> compiles

A refusal is an OracleError (ungradable, never graded). Needs the oracle
(docker + the pinned image, or LP_ORACLE_IN_IMAGE); without it the gate
exits 0 with a SKIP line unless REQUIRE_PDFLATEX=1.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

PAD = (r"\count255=0 \loop \immediate\write6{padding line \the\count255 "
       r"....................................}\advance\count255 1 "
       r"\ifnum\count255<3000 \repeat" "\n")
FORGED = r"\immediate\write6{Output written on \jobname.pdf (1 page, 1234 bytes).}" "\n"

DOCS = {
    "forge_log": r"""\documentclass{article}
\begin{document}
\immediate\openout5=\jobname.pdf \immediate\write5{PDF-1.5 fake}\immediate\closeout5
\immediate\openout6=\jobname.log
""" + PAD + FORGED + r"""\end{document}
""",
    "forge_link": r"""\documentclass{article}
\begin{document}
\immediate\openout5=\jobname.pdf \immediate\write5{PDF-1.5 fake}\immediate\closeout5
\immediate\openout6=evil.txt
""" + PAD + FORGED + r"""\end{document}
""",
    "forge_case": r"""\documentclass{article}
\begin{document}
\InputIfFileExists{cnt.tex}{}{\def\lppass{0}}
\ifcase\lppass \def\lpl{DOC.log}\def\lpp{Doc.pdf}\or \def\lpl{DOc.log}\def\lpp{DOc.pdf}\else \def\lpl{DoC.log}\def\lpp{DoC.pdf}\fi
\count255=\lppass \advance\count255 1
\immediate\openout4=cnt.tex \immediate\write4{\noexpand\def\noexpand\lppass{\the\count255}}\immediate\closeout4
\immediate\openout5=\lpp \immediate\write5{PDF-1.5 fake}\immediate\closeout5
\immediate\openout6=\lpl
""" + PAD + FORGED + r"""\batchmode
\end{document}
""",
    "forge_term": r"""\documentclass{article}
\begin{document}
\immediate\write16{Output written on \jobname.pdf (1 page, 1234 bytes).}
\immediate\write16{Transcript written on \jobname.log.}
\batchmode
\end{document}
""",
    "ok": r"""\documentclass{article}
\begin{document}
hello
\end{document}
""",
    "nopages": r"""\documentclass{article}
\begin{document}
\end{document}
""",
    "synctex": r"""\synctex=1
\documentclass{article}
\begin{document}
hello
\end{document}
""",
    "batchok": r"""\documentclass{article}
\begin{document}
hello\batchmode
\end{document}
""",
}
# (verdict wanted): "refused", or the value of OracleRun.compiles
WANT = {"forge_log": "refused", "forge_link": "refused", "forge_case": "refused",
        "forge_term": "refused", "ok": True, "nopages": False, "synctex": True,
        "batchok": True}


def grade(o, name: str) -> object:
    with o.tempdir(prefix="lp-forgery-") as td:
        td = Path(td)
        work = td / "w"
        work.mkdir()
        (work / "doc.tex").write_text(DOCS[name])
        if name == "forge_link":
            os.symlink("doc.log", work / "evil.txt")
        try:
            return o.run_to_fixpoint(work, "doc.tex", o.tex_env(td), 180).compiles
        except _oracle.OracleError as e:
            if isinstance(e, _oracle.OracleUnavailable):
                raise
            return "refused"


def main() -> int:
    ok, why = _oracle.availability()
    if not ok:
        if os.environ.get("REQUIRE_PDFLATEX") == "1":
            print(f"[oracle-forgery] FAIL: no oracle: {why}", file=sys.stderr)
            return 2
        print(f"[oracle-forgery] SKIP: no oracle ({why})")
        return 0
    o = _oracle.get_oracle()
    bad = []
    for name in DOCS:
        got = grade(o, name)
        print(f"[oracle-forgery] {o.backend:9s} {name:11s} -> {got!r} "
              f"(want {WANT[name]!r})")
        if got != WANT[name]:
            bad.append(f"{name}: got {got!r}, want {WANT[name]!r}")
    if bad:
        print("[oracle-forgery] FAIL: the real oracle graded a forgery or "
              "mis-graded a genuine document:", file=sys.stderr)
        for b in bad:
            print(f"  - {b}", file=sys.stderr)
        return 1
    print(f"[oracle-forgery] OK: {len(DOCS)} documents on the {o.backend} backend; "
          f"every forgery of the evidence refused, every genuine shape graded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
