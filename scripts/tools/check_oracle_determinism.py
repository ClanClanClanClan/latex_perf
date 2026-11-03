#!/usr/bin/env python3
"""check_oracle_determinism.py -- a document graded twice by the REAL oracle
gives byte-identical evidence, and cannot open the shim's bookkeeping or the
host state behind the commands restricted \\write18 may start (OPEN-128,
C-133..C-135).

WHY. ADR-015 E10 says every run-dependent input of a graded run is fixed.
The review of 0400f74a (2026-11-03) MEASURED that it was not: the shim's
proof-of-loading marks were files named by pid in /tmp/lp/.shim, /tmp was a
root of the shim's file-system view and openin_any=p allows absolute reads,
so a document saw, with \\pdffilesize, a set of pids that differed between
five identical runs, and that after a java child (texosquery-jre8) depended
on the container's CPU count (C-133, C-134). check_oracle_infra_grading.py
is pure and cannot see that; this gate runs real documents through the real
oracle (`get_oracle()`), on a developer's Mac and on CI's arm64 runner.

THE DOCUMENTS (each graded TWICE, each in a fresh work directory):
  pid_probe     the C-133 probe: a texosquery-jre8 child (the JVM) and a
                kpsewhich child, then \\pdffilesize / \\pdfmdfivesum /
                \\IfFileExists of every bookkeeping path of the oracle under
                test (and of SHIM_MARK_DIR/<n> for n = 1..PIDS) -> every
                probe must come back EMPTY (requirement BOOK)
  jvm           texosquery-jre8's date, OS version, CPU-sensitive output
                read back through a pipe into the log
  interpreters  C-135: each shell_escape_command run by a /usr/bin
                interpreter, pointed at /proc/uptime, /proc/self/stat,
                /etc/hostname and /etc/resolv.conf -> each must REFUSE
                (requirement INTERP; the refusal shape per command is in
                INTERP_REFUSED)
For every document, both runs' rc, PDF verdict, .log bytes and .pdf bytes
must be IDENTICAL (requirement TWICE).

It FAILS on 0400f74a (BOOK: the pid marks are readable; TWICE: often) and
must PASS at the tip; `--repo DIR` grades with DIR's scripts/tools/_oracle.py
(and DIR's pinned shim), so both can be shown from one copy of this gate.
Needs the oracle (docker + the pinned image); without it the gate exits 0
with a SKIP line unless REQUIRE_PDFLATEX=1.
"""
from __future__ import annotations

import argparse
import importlib
import os
import re
import sys
import zlib
from pathlib import Path

PIDS = 300

# The /usr/bin-interpreter commands of the image's shell_escape_commands
# (C-135) and the TARGETS a document must not read through them.
INTERP_COMMANDS = ("latexminted", "memoize-extract.py", "memoize-extract.pl",
                   "repstopdf", "texosquery-jre8")
TARGETS = ("/proc/uptime", "/proc/self/stat", "/etc/hostname", "/etc/resolv.conf")

# What the targets' content looks like (a leak), whatever the command printed.
LEAK = {"/proc/uptime": r"^\s*\d+\.\d+ \d+\.\d+\s*$",
        "/proc/self/stat": r"^\d+ \(\S+\) [A-Z] \d+",
        "/etc/hostname": r"lp-oracle",
        "/etc/resolv.conf": r"nameserver|^search |^options "}

PROBE_MACROS = r"""\makeatletter
\def\lpprobe#1{\immediate\openin1=|"#1"\relax
 \ifeof1 \typeout{LPPIPE[#1]=<eof>}\else
 \loop\unless\ifeof1 \readline1 to\lpx \typeout{LPPIPE[#1]=[\lpx]}\repeat\fi
 \immediate\closein1}
\def\lpfile#1{\IfFileExists{#1}{\def\lpo{open}}{\def\lpo{}}%
 \typeout{LPBOOK[#1]=[\pdffilesize{#1}][\pdfmdfivesum file{#1}][\lpo]}}
\makeatother
"""


def pid_probe(paths: list[str]) -> str:
    files = "\n".join(r"\lpfile{%s}" % p for p in paths)
    return (r"\documentclass{article}" "\n" + PROBE_MACROS + r"""\begin{document}
\immediate\write18{texosquery-jre8 -n}
\immediate\write18{kpsewhich -var-value=HOME}
""" + files + "\n" + r"""x
\end{document}
""")


JVM = r"""\documentclass{article}
""" + PROBE_MACROS + r"""\begin{document}
\lpprobe{texosquery-jre8 -n}
\lpprobe{texosquery-jre8 -M}
\lpprobe{texosquery-jre8 -r}
\lpprobe{texosquery-jre8 -a}
\lpprobe{texosquery-jre8 -o}
\lpprobe{texosquery-jre8 -N}
\typeout{LPSEED[\the\pdfrandomseed][\the\pdfelapsedtime][\pdffilemoddate{\jobname.tex}][\pdfcreationdate]}
x
\end{document}
"""

EPS = "\n".join([
    "%!PS-Adobe-3.0 EPSF-3.0", "%%BoundingBox: 0 0 300 120",
    "/Courier findfont 8 scalefont setfont",
    "10 100 moveto (U=) show usertime 20 string cvs show",
    "10 90 moveto (R=) show realtime 20 string cvs show"] + [
    f"10 {80 - 10 * i} moveto {{ ({t}) (r) file 200 string readline pop pop "
    f"(READ) }} stopped {{ (DENIED) }} if show"
    for i, t in enumerate(TARGETS)] + ["showpage", ""])


def interpreters() -> str:
    pipes = []
    for t in TARGETS:
        pipes += [f"texosquery-jre8 -s {t}", f"texosquery-jre8 -d {t}",
                  f"texosquery-jre8 -p {t}",
                  f"memoize-extract.py -k -P {t} lpmz.mmz",
                  f"memoize-extract.pl -k -P {t} lpmz.mmz"]
    pipes += [f"texosquery-jre8 -i , {d}" for d in ("/proc", "/etc", "/proc/self", "/lp")]
    body = "\n".join(r"\lpprobe{%s}" % p for p in pipes)
    minted = "\n".join(r"\lpminted{%s}" % t for t in TARGETS)
    return (r"\documentclass{article}" "\n" r"\usepackage{minted}" "\n" + PROBE_MACROS
            + r"""\makeatletter
\def\lpminted#1{\begingroup\let\PackageError\lpminterr
 \def\FV@Error##1##2{\typeout{LPFV[##1]}}\inputminted{text}{#1}\endgroup}
\def\lpminterr#1#2#3{{\def\MessageBreak{ }\typeout{LPMINTED[#2]}}}
\makeatother
\begin{document}
""" + body + "\n" + r"""\lpprobe{repstopdf lpt.eps}
\IfFileExists{lpt.pdf}{\typeout{LPEPS[made]}}{\typeout{LPEPS[none]}}
""" + minted + "\n" + r"""x
\end{document}
""")


def docs(oracle_mod) -> dict:
    book = list(getattr(oracle_mod, "BOOKKEEPING_PATHS", ()))
    mark = oracle_mod.SHIM_MARK_DIR
    legacy = ["/tmp/lp/.shim", "/tmp/lp/.fs-denied", "/tmp/lp/.clock"]
    paths = list(dict.fromkeys(book + [mark, oracle_mod.FS_LOG, oracle_mod.CLOCK_LOG,
                                       mark + "/engine", mark + "/children"]
                               + legacy + [f"{mark}/{n}" for n in range(1, PIDS + 1)]
                               + [f"/tmp/lp/.shim/{n}" for n in range(1, PIDS + 1)]))
    return {"pid_probe": (pid_probe(paths), {}),
            "jvm": (JVM, {}),
            "interpreters": (interpreters(), {"lpt.eps": EPS, "lpmz.mmz": ""})}


def grade(o, name: str, src: str, extra: dict) -> dict:
    with o.tempdir(prefix="lp-determinism-") as td:
        work = Path(td) / "w"
        work.mkdir()
        (work / "doc.tex").write_text(src)
        for f, text in extra.items():
            (work / f).write_text(text)
        r = o.run_to_fixpoint(work, "doc.tex", o.tex_env(td), 300)
        out = {"rc": r.rc, "compiles": r.compiles, "timeout": r.timed_out}
        for ext in (".log", ".pdf"):
            p = work / ("doc" + ext)
            out[ext] = p.read_bytes() if p.exists() else None
        eps = work / "lpt.pdf"
        out["eps_pdf"] = eps.read_bytes() if eps.exists() else None
        return out


def pdf_text(data: bytes | None) -> bytes:
    if not data:
        return b""
    chunks = []
    for m in re.finditer(rb"stream\r?\n(.*?)endstream", data, re.S):
        try:
            chunks.append(zlib.decompress(m.group(1)))
        except zlib.error:
            chunks.append(m.group(1))
    return b"\n".join(chunks)


def unwrap(log: bytes | None) -> str:
    """The log with pdfTeX's line wrapping undone: a line of exactly
    max_print_line (79) characters continues on the next."""
    out, cur = [], ""
    for ln in (log or b"").decode("latin-1").split("\n"):
        cur += ln
        if len(ln) != 79:
            out.append(cur)
            cur = ""
    if cur:
        out.append(cur)
    return "\n".join(out)


def lines(log: bytes | None, tag: str) -> list[str]:
    return re.findall(r"^" + tag + r"\[(.*)$", unwrap(log), re.M)


def check_book(run: dict) -> list[str]:
    bad = []
    seen = lines(run[".log"], "LPBOOK")
    if len(seen) < PIDS:   # a probe that ran nothing is not a pass
        bad.append(f"BOOK: only {len(seen)} bookkeeping probes reached the log "
                   f"(want >= {PIDS})")
    for ln in seen:
        m = re.fullmatch(r"(.*?)\]=\[(.*?)\]\[(.*?)\]\[(.*?)\]", ln)
        if m is None or any(m.group(k) for k in (2, 3, 4)):
            bad.append(f"BOOK: a document read the oracle's bookkeeping: {ln[:160]}")
    return bad


def check_interp(run: dict) -> list[str]:
    bad = []
    pipes = lines(run[".log"], "LPPIPE")
    if len(pipes) < 4 * len(TARGETS):
        bad.append(f"INTERP: only {len(pipes)} interpreter probes reached the log")
    for ln in pipes:
        cmd, _, val = ln.partition("]=")
        v = val.replace("^^M", "").strip("[]")
        leak = [k for k, rx in LEAK.items() if re.search(rx, v)]
        if leak:
            bad.append(f"INTERP: {cmd} returned host content ({leak}): {v[:120]!r}")
        elif cmd.startswith("texosquery") and v not in ("", "<eof>"):
            # texosquery's documented refusal: "An empty string is printed if
            # the requested information is unavailable or not permitted."
            bad.append(f"INTERP: {cmd} returned {v[:120]!r}, not its refusal (empty)")
    flat = (run[".log"] or b"").decode("latin-1").replace("\n", "")
    refused = [t for t in TARGETS if f'prohibited location: "{t}"' in flat]
    if len(refused) != len(TARGETS):
        bad.append(f"INTERP: latexminted refused {len(refused)} of {len(TARGETS)} "
                   f"targets ({refused})")
    eps = pdf_text(run["eps_pdf"])
    if not run["eps_pdf"]:
        bad.append("INTERP: repstopdf produced no PDF, so gs's refusal is unmeasured")
    elif eps.count(b"(DENIED)") != len(TARGETS) or b"(READ)" in eps:
        bad.append(f"INTERP: gs under repstopdf read a refused target "
                   f"({eps.count(b'(DENIED)')} DENIED of {len(TARGETS)})")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dump", default=None,
                    help="write each run's log to this directory")
    ap.add_argument("--repo", default=str(Path(__file__).resolve().parent.parent.parent),
                    help="grade with this tree's scripts/tools/_oracle.py")
    args = ap.parse_args()
    sys.path.insert(0, str(Path(args.repo).resolve() / "scripts" / "tools"))
    oracle_mod = importlib.import_module("_oracle")
    print(f"[oracle-determinism] oracle module: {oracle_mod.__file__}")
    ok, why = oracle_mod.availability()
    if not ok:
        if os.environ.get("REQUIRE_PDFLATEX") == "1":
            print(f"[oracle-determinism] FAIL: no oracle: {why}", file=sys.stderr)
            return 2
        print(f"[oracle-determinism] SKIP: no oracle ({why})")
        return 0
    o = oracle_mod.get_oracle()
    bad = []
    for name, (src, extra) in docs(oracle_mod).items():
        try:
            a, b = grade(o, name, src, extra), grade(o, name, src, extra)
        except oracle_mod.OracleError as e:
            if isinstance(e, oracle_mod.OracleUnavailable):
                raise
            bad.append(f"{name}: the oracle refused the document: {str(e)[:200]}")
            continue
        if args.dump:
            Path(args.dump).mkdir(parents=True, exist_ok=True)
            for tag, r in (("a", a), ("b", b)):
                (Path(args.dump) / f"{name}.{tag}.log").write_bytes(r[".log"] or b"")
        diff = [k for k in ("rc", "compiles", "timeout", ".log", ".pdf", "eps_pdf")
                if a[k] != b[k]]
        print(f"[oracle-determinism] {name:12s} rc={a['rc']},{b['rc']} "
              f"compiles={a['compiles']},{b['compiles']} differ={diff}")
        if a["timeout"] or b["timeout"]:
            bad.append(f"{name}: a run timed out (a rerun, not a verdict)")
        if diff:
            bad.append(f"TWICE: {name}: two identical runs differ in {diff}")
            if ".log" in diff:
                la = (a[".log"] or b"").decode("latin-1").splitlines()
                lb = (b[".log"] or b"").decode("latin-1").splitlines()
                first = next((i for i, (x, y) in enumerate(zip(la, lb)) if x != y),
                             min(len(la), len(lb)))
                bad.append(f"  first differing log line {first + 1}: "
                           f"{la[first:first + 1]} vs {lb[first:first + 1]}")
        if name == "pid_probe":
            bad += [f"{name}: {x}" for x in check_book(a) + check_book(b)][:12]
        if name == "interpreters":
            bad += [f"{name}: {x}" for x in check_interp(a)][:20]
    if bad:
        print("[oracle-determinism] FAIL: a graded run observed something that is "
              "not fixed by the protocol:", file=sys.stderr)
        for x in bad:
            print(f"  - {x}", file=sys.stderr)
        return 1
    print(f"[oracle-determinism] OK: 3 documents graded twice each with "
          f"byte-identical rc, verdict, log and PDF; no bookkeeping path "
          f"readable ({PIDS}+ probes); every /usr/bin-interpreter command "
          f"({', '.join(INTERP_COMMANDS)}) refused {len(TARGETS)} host targets")
    return 0


if __name__ == "__main__":
    sys.exit(main())
