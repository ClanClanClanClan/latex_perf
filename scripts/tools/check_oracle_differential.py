#!/usr/bin/env python3
"""check_oracle_differential.py -- the oracle's semantics EQUAL the pinned
pdfTeX's wherever that engine is deterministic, and the oracle REFUSES where
it is not (C-196, revised rule of 2026-11-04; the third review of 4574c940).

WHY. The shim fixes what a run can observe of its host. The second review's
H2 fix serialised pipes, which made the oracle's schedule deterministic and
DIFFERENT from pdfTeX's: MEASURED by the third review against the unshimmed
pinned engine, sigpipe.tex gave rc 0 there and rc 1 in the oracle,
sigpipe2.tex rc 1 and rc 0 (a false READY), and a flush before \\write18 made
\\pdffilesize{\\jobname.log} 1900 where the engine gives 0. A differential
against the engine itself is the only test of that class.

METHOD. Each document is run N times through the REFERENCE (the same launch
definition and environment, no LD_PRELOAD: `ContainerOracle.reference_pass`,
never a grade) and once through the oracle (`run_pdflatex`, one pass). If the
reference is deterministic across its N runs, the oracle must give the SAME
rc, PDF verdict and log; if it is not, the oracle must REFUSE the run as
nondeterministic. Never a different grade.

  sigpipe / sigpipe2   a pipe child (bibtex, an endless .bst loop of output)
                       that TeX stops reading: the engine SIGPIPEs it, so it
                       never writes its .bbl marker
  infbst               a .bst whose output never ends: compiles in the engine
  wpipe                a "w" pipe to a child that ignores its input
  w18size              \\pdffilesize{\\jobname.log} after \\write18 and a pipe
  raceflip_fast        TeX polls a PDF a pipe child is writing (racy in the
                       engine: the oracle must refuse)

`--repo DIR` runs DIR's oracle (it FAILS at 4574c940). Needs docker and the
pinned image (SKIP without them unless REQUIRE_PDFLATEX=1).
"""
from __future__ import annotations

import argparse
import importlib
import importlib.util
import os
import re
import sys
from pathlib import Path

N_REF = 3
SIGPIPE_BST = r"""ENTRY {} {} {}
INTEGERS { i }
FUNCTION {loop}
{ #0 'i :=
  { i #200000 < }
  { "yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy" top$  i #1 + 'i := }
  while$
  "\def\lpmarker{1}" write$ newline$
}
READ
EXECUTE {loop}
"""
INF_BST = r"""ENTRY {} {} {}
FUNCTION {loop}
{ { #1 } { "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz" top$ } while$ }
READ
EXECUTE {loop}
"""
LPINF = {"lpinf.aux": "\\citation{*}\n\\bibstyle{lpinf}\n\\bibdata{lpinf}\n",
         "lpinf.bib": "@misc{a, title={t}}\n"}
SIGPIPE_BODY = r"""\documentclass{article}
\begin{document}
\typeout{LPSZ before=[\pdffilesize{\jobname.log}]}
\immediate\write18{kpsewhich article.cls}
\typeout{LPSZ after-write18=[\pdffilesize{\jobname.log}]}
\immediate\openin1=|"bibtex lpinf"\relax
\read1 to\lpx
\immediate\closein1
\typeout{LPSZ after-pipe=[\pdffilesize{\jobname.log}]}
\typeout{LPBBL size=[\pdffilesize{lpinf.bbl}]}
\IfFileExists{lpinf.bbl}{\input{lpinf.bbl}}{}
%s
x
\end{document}
"""
FAST_EPS = "\n".join([
    "%!PS-Adobe-3.0 EPSF-3.0", "%%BoundingBox: 0 0 300 120",
    "/Courier findfont 8 scalefont setfont",
    "10 100 moveto (fast) show", "showpage", ""])

DOCS = {
    "sigpipe": (SIGPIPE_BODY % r"\ifdefined\lpmarker \errmessage{LPMARK the pipe child ran to completion}\else\typeout{LPMARK child was cut by SIGPIPE}\fi",
                dict(LPINF, **{"lpinf.bst": SIGPIPE_BST})),
    "sigpipe2": (SIGPIPE_BODY % r"\ifdefined\lpmarker \typeout{LPMARK ran to completion}\else\errmessage{LPMARK child was cut by SIGPIPE}\fi",
                 dict(LPINF, **{"lpinf.bst": SIGPIPE_BST})),
    "infbst": (r"""\documentclass{article}
\begin{document}
\immediate\openin1=|"bibtex lpinf"\relax
\read1 to\lpx
\immediate\closein1
\typeout{LPINF read one line}
x
\end{document}
""", dict(LPINF, **{"lpinf.bst": INF_BST})),
    "wpipe": (r"""\documentclass{article}
\newcount\lpi
\begin{document}
\immediate\openout5=|"kpsewhich article.cls"
\lpi=0
\loop \immediate\write5{yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy}\advance\lpi1 \ifnum\lpi<20000 \repeat
\immediate\closeout5
\typeout{LPW survived the writes}
x
\end{document}
""", {}),
    "w18size": (r"""\documentclass{article}
\begin{document}
\typeout{LPSZ before=[\pdffilesize{\jobname.log}]}
\immediate\write18{kpsewhich article.cls}
\typeout{LPSZ after-write18=[\pdffilesize{\jobname.log}]}
\immediate\openin1=|"kpsewhich article.cls"\relax
\read1 to\lpx
\immediate\closein1
\typeout{LPSZ after-pipe=[\pdffilesize{\jobname.log}]}
x
\end{document}
""", {}),
    "raceflip_fast": (r"""\documentclass{article}
\newcount\lpi \newcount\lpj \newif\iflpgo
\begin{document}
\immediate\openin1=|"repstopdf lpt.eps"\relax
\lpj=0
\loop
  \lpi=0 {\loop\advance\lpi1 \ifnum\lpi<2000 \repeat}%
  \advance\lpj1
  \lpgotrue
  \ifnum0\pdffilesize{lpt.pdf}>0 \lpgofalse\fi
  \ifnum\lpj>100000 \lpgofalse\fi
\iflpgo \repeat
\typeout{LPFLIP polls-until-gs-done=[\the\lpj]}
x
\immediate\closein1
\end{document}
""", {"lpt.eps": FAST_EPS}),
}
ARGS = ["-interaction=nonstopmode", "doc.tex"]


def setup(work: Path, src: str, extra: dict) -> None:
    work.mkdir(parents=True)
    (work / "doc.tex").write_text(src)
    for f, text in extra.items():
        (work / f).write_text(text)


def outcome_ref(rmod, o, name: str) -> dict:
    src, extra = DOCS[name]
    with o.tempdir(prefix="lp-diff-ref-") as td:
        work = Path(td) / "w"
        setup(work, src, extra)
        r = o.reference_pass(work, ARGS, 240)
        pdf = rmod.pdf_written(work, ARGS, r["stdout"])
        return {"rc": r["rc"], "pdf": pdf, "log": r["log"], "timed_out": r["timed_out"]}


def outcome_oracle(om, o, name: str) -> dict:
    src, extra = DOCS[name]
    with o.tempdir(prefix="lp-diff-orc-") as td:
        work = Path(td) / "w"
        setup(work, src, extra)
        try:
            r = o.run_pdflatex(work, ARGS, o.tex_env(td), 240)
        except om.OracleError as e:
            if isinstance(e, om.OracleUnavailable):
                raise
            return {"refused": str(e)}
        rc, _, to = r
        log = work / "doc.log"
        return {"rc": rc, "pdf": om.pdf_written(work, ["doc.tex"], r.stdout),
                "log": log.read_bytes() if log.is_file() else b"", "timed_out": to}


def lp_lines(log: bytes) -> list[str]:
    return [ln for ln in log.decode("latin-1").splitlines()
            if re.match(r"^(! )?LP[A-Z]+", ln)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=str(Path(__file__).resolve().parent.parent.parent))
    ap.add_argument("--only", action="append", default=[])
    args = ap.parse_args()
    sys.path.insert(0, str(Path(args.repo).resolve() / "scripts" / "tools"))
    om = importlib.import_module("_oracle")
    print(f"[oracle-differential] oracle module: {om.__file__}")
    ok, why = om.availability()
    if not ok:
        if os.environ.get("REQUIRE_PDFLATEX") == "1":
            print(f"[oracle-differential] FAIL: no oracle: {why}", file=sys.stderr)
            return 2
        print(f"[oracle-differential] SKIP: no oracle ({why})")
        return 0
    o = om.get_oracle()
    if not hasattr(o, "reference_pass"):
        # an older tree: use this tree's reference (the engine is the same)
        here = Path(__file__).resolve().parent
        sys.path.insert(0, str(here))
        spec = importlib.util.spec_from_file_location("_oracle_ref", here / "_oracle.py")
        ref_mod = importlib.util.module_from_spec(spec)
        sys.modules["_oracle_ref"] = ref_mod
        spec.loader.exec_module(ref_mod)
        ref = ref_mod.get_oracle()
    else:
        ref, ref_mod = o, om
    bad, n = [], 0
    for name in DOCS:
        if args.only and name not in args.only:
            continue
        n += 1
        refs = [outcome_ref(ref_mod, ref, name) for _ in range(N_REF)]
        det = all((r["rc"], r["pdf"], r["log"]) == (refs[0]["rc"], refs[0]["pdf"], refs[0]["log"])
                  for r in refs)
        got = outcome_oracle(om, o, name)
        rshape = (f"rc={[r['rc'] for r in refs]} pdf={[r['pdf'] for r in refs]} "
                  f"deterministic={det}")
        if "refused" in got:
            gshape = "REFUSED: " + got["refused"][:100]
        else:
            gshape = f"rc={got['rc']} pdf={got['pdf']} timed_out={got['timed_out']}"
        print(f"[oracle-differential] {name:14s} engine {rshape} | oracle {gshape}")
        if det:
            if "refused" in got:
                bad.append(f"{name}: the engine is deterministic ({rshape}) but the "
                           f"oracle refused it: {got['refused'][:160]}")
            elif (got["rc"], got["pdf"]) != (refs[0]["rc"], refs[0]["pdf"]) \
                    or got["log"] != refs[0]["log"]:
                diff = sorted(set(lp_lines(got["log"])) ^ set(lp_lines(refs[0]["log"])))
                bad.append(f"{name}: a DIFFERENT GRADE from the pinned engine: engine "
                           f"rc {refs[0]['rc']} pdf {refs[0]['pdf']}, oracle rc "
                           f"{got['rc']} pdf {got['pdf']}; log lines that differ: {diff[:4]}")
        else:
            if "refused" not in got or "nondeterministic" not in got["refused"]:
                bad.append(f"{name}: the engine is racy ({rshape}) but the oracle "
                           f"graded it ({gshape}); it must refuse")
    if bad:
        print("[oracle-differential] FAIL:", file=sys.stderr)
        for b in bad:
            print(f"  - {b}", file=sys.stderr)
        return 1
    print(f"[oracle-differential] OK: {n} documents; where the pinned engine is "
          f"deterministic over {N_REF} runs the oracle gave the same rc, verdict "
          f"and log, and where it is racy the oracle refused")
    return 0


if __name__ == "__main__":
    sys.exit(main())
