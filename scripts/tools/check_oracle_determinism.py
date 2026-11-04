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
  gs_sandbox, minted, memoize_pl, memoize_py, texosquery
                C-138: what each /usr/bin child's OWN sandbox lets it observe
                (gs -dSAFER: its TMPDIR, whose mkstemp64 names were random;
                latexminted's and memoize's outputs; java's listings)
For every document, both runs' rc, PDF verdict, .log bytes, .pdf bytes and
EVERY file the run leaves in its directory must be IDENTICAL (TWICE).
HOST VARIANTS (C-139, review LOW-3): pid_probe and jvm graded again under a
different --cpuset-cpus and --memory (must be REFUSED by the in-container
readback, C-139 (a)), another --user (C-185) and another work-root path:
identical to the baseline byte for byte, or refused.

It FAILS on 0400f74a (BOOK: the pid marks are readable; TWICE: often) and
must PASS at the tip; `--repo DIR` grades with DIR's scripts/tools/_oracle.py
(and DIR's pinned shim), so both can be shown from one copy of this gate.
Needs the oracle (docker + the pinned image); without it the gate exits 0
with a SKIP line unless REQUIRE_PDFLATEX=1.
"""
from __future__ import annotations

import argparse
import hashlib
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


# C-138 (review of 52b81823, HIGH-1): what gs's OWN sandbox permits under
# repstopdf's -dSAFER -- enumerating its TMPDIR (where its mkstemp64 names
# were random), /tmp, the bookkeeping, the cwd; a temp file; reads of the
# bookkeeping, /proc, /sys; getenv; rrand, vmstatus, realtime, usertime --
# printed into lpt.pdf, which the document hashes. The review's probe, kept.
GS_SANDBOX_EPS = """%!PS-Adobe-3.0 EPSF-3.0
%%BoundingBox: 0 0 500 400
/concatstrings { exch dup length 2 index length add string dup dup 4 2 roll copy length 4 -1 roll putinterval } bind def
/Courier findfont 7 scalefont setfont
/y 390 def
/L { 10 y moveto show /y y 9 sub def } def
/S { 300 string cvs } def
(rrand=) rrand S concatstrings L
(vm=) vmstatus 3 1 roll S ( ) concatstrings exch S concatstrings exch S concatstrings concatstrings L
{ (tmpA) () (w) .tempfile closefile (TEMPFILE=) exch concatstrings L } stopped { (TEMPFILE denied) L } if
{ (/tmp/lp/tmp/*) { dup length string copy (TMP:) exch concatstrings L } 300 string filenameforall } stopped { (enumTMP denied) L } if
{ (/tmp/*) { dup length string copy (T:) exch concatstrings L } 300 string filenameforall } stopped { (enumT denied) L } if
{ (/tmp/lp/*) { dup length string copy (TL:) exch concatstrings L } 300 string filenameforall } stopped { (enumTL denied) L } if
{ (/lp/book/shim/*) { dup length string copy (B:) exch concatstrings L } 300 string filenameforall } stopped { (enumB denied) L } if
{ (*) { dup length string copy (CWD:) exch concatstrings L } 300 string filenameforall } stopped { (enumCWD denied) L } if
{ (/lp/book/shim/children) (r) file 200 string readstring pop (CH=) exch concatstrings L } stopped { (children DENIED) L } if
{ (/lp/book/shim/children) status { (CHST=) exch S concatstrings L pop pop pop } { (CHST none) L } ifelse } stopped { (status DENIED) L } if
{ (/proc/self/stat) status { (PST=) exch S concatstrings L pop pop pop } { (PST none) L } ifelse } stopped { (pst DENIED) L } if
{ (/sys/devices/system/cpu/online) (r) file 200 string readline pop (CPU=) exch concatstrings L } stopped { (cpu DENIED) L } if
{ (/proc/meminfo) (r) file 200 string readline pop (MEM=) exch concatstrings L } stopped { (mem DENIED) L } if
{ (HOME) getenv { (HOME=) exch concatstrings L } { (HOME none) L } ifelse } stopped { (getenv DENIED) L } if
{ (TMPDIR) getenv { (TMPDIR=) exch concatstrings L } { (TMPDIR none) L } ifelse } stopped { (getenv2 DENIED) L } if
(rt=) realtime S concatstrings L
(ut=) usertime S concatstrings L
showpage
"""

# Each /usr/bin child's own sandbox, exercised the way a document can: its
# outputs land in the run directory, and EVERY file the run leaves there is
# compared between the two runs (TWICE), not only the log and the PDF.
SANDBOX_DOCS = {
    "gs_sandbox": (r"""\documentclass{article}
\begin{document}
\immediate\write18{repstopdf lpt.eps}
\IfFileExists{lpt.pdf}{\typeout{LPEPS[made][\pdfmdfivesum file{lpt.pdf}]}}{\typeout{LPEPS[none]}}
x
\end{document}
""", {"lpt.eps": GS_SANDBOX_EPS}),
    "minted": (r"""\documentclass{article}
\usepackage{minted}
\begin{document}
\begin{minted}{python}
import tempfile, os
print(tempfile.gettempdir(), os.getuid())
\end{minted}
\inputminted{text}{lpsrc.txt}
\end{document}
""", {"lpsrc.txt": "one\ntwo\n"}),
    # memoize 1.4.1 (the pinned image) fails on `extract=` as a package
    # option ("Illegal parameter number"), and refuses a second `extract`:
    # perl is its default; memoize-extract.py is run by hand on a record.
    "memoize_pl": (r"""\documentclass{article}
\usepackage{memoize}
\begin{document}
\mmz{\fbox{memoized}}
\end{document}
""", {}),
    "memoize_py": (r"""\documentclass{article}
\begin{document}
\immediate\write18{memoize-extract.py -F latex -P lpm.pdf lpm}
\IfFileExists{lpm.mmz.log}{\typeout{LPMMZ[\pdfmdfivesum file{lpm.mmz.log}]}}{\typeout{LPMMZ[none]}}
x
\end{document}
""", {"lpm.mmz": "\\mmzNewExtern{lpm.memo.dir/X-1.pdf}{1}{10pt}{10pt}{0pt}\n",
      "lpm.pdf": "%PDF-1.4\n%%EOF\n"}),
    "texosquery": (r"""\documentclass{article}
""" + PROBE_MACROS + r"""\begin{document}
\lpprobe{texosquery-jre8 -i , .}
\lpprobe{texosquery-jre8 -ir , .}
\lpprobe{texosquery-jre8 -i , . date}
\lpprobe{l3sys-query ls}
\lpprobe{l3sys-query ls --sort date}
\lpprobe{texosquery-jre8 -i , /tmp/lp/tmp}
\lpprobe{texosquery-jre8 -c}
\lpprobe{texosquery-jre8 -m}
\lpprobe{texosquery-jre8 -t}
\lpprobe{texosquery-jre8 -M}
x
\end{document}
""", {f"f_{w}.txt": w + "\n" for w in
      ("zeta", "alpha", "mike", "bravo", "yankee", "charlie", "xray", "delta")}),
}


# The review of 82638518's reproducers, kept (H1, H2).
# fs_meta (H1, C-195): a directory's size and the other stat fields through
#   texosquery (java) and TeX: 1344 on APFS/virtiofs, 4096 on ext4, 840 on
#   tmpfs before C-195. Required: every directory reports 4096.
FS_META_TEX = r"""\documentclass{article}
\makeatletter
\def\lpprobe#1{\immediate\openin1=|"#1"\relax
 \ifeof1 \typeout{LPPIPE[#1]=<eof>}\else
 \loop\unless\ifeof1 \readline1 to\lpx \typeout{LPPIPE[#1]=[\lpx]}\repeat\fi
 \immediate\closein1}
\makeatother
\begin{document}
\lpprobe{texosquery-jre8 -s .}
\lpprobe{texosquery-jre8 -s sub}
\lpprobe{texosquery-jre8 -s sub/f1}
\lpprobe{texosquery-jre8 -s doc.tex}
\lpprobe{texosquery-jre8 -i , . size}
\lpprobe{texosquery-jre8 -id , .}
\lpprobe{texosquery-jre8 -i , sub}
\lpprobe{texosquery-jre8 -m}
\lpprobe{texosquery-jre8 -t}
\lpprobe{texosquery-jre8 -c}
\lpprobe{texosquery-jre8 -d sub}
\lpprobe{texosquery-jre8 -o -r -a}
\lpprobe{texosquery-jre8 -L -cs}
\lpprobe{l3sys-query ls --type d}
\typeout{LPTEX[\pdffilesize{sub}][\pdffilemoddate{sub}][\pdffilesize{sub/f1}]}
x
\end{document}
"""
# raceflip (H2, C-196): TeX polls the size of the PDF a pipe child (repstopdf
#   -> gs) is writing; with a concurrent child the count depended on
#   scheduling (rc 0,0,1,0,0). Required: the child had finished when popen
#   returned (one poll).
RACEFLIP_TEX = r"""\documentclass{article}
\newcount\lpi \newcount\lpj \newif\iflpgo
\begin{document}
\immediate\openin1=|"repstopdf lpt.eps"\relax
\lpj=0
\loop
  \lpi=0 {\loop\advance\lpi1 \ifnum\lpi<2000 \repeat}%
  \advance\lpj1
  \lpgotrue
  \ifnum0\pdffilesize{lpt.pdf}>7000 \lpgofalse\fi
  \ifnum\lpj>100000 \lpgofalse\fi
\iflpgo \repeat
\typeout{LPFLIP polls-until-gs-done=[\the\lpj]}
\ifnum\lpj>48 \errmessage{LPFLIP slow}\fi
x
\immediate\closein1
\end{document}
"""
# orphan2 (H2, C-196): a pipe child still running when the engine exits left
#   a 0-byte lpt.pdf that the NEXT pass read. Required: the next pass sees
#   the finished file.
ORPHAN2_TEX = r"""\documentclass{article}
\begin{document}
\IfFileExists{lpt.pdf}{\typeout{LPORPHAN[prev=\pdffilesize{lpt.pdf}]}}{\typeout{LPORPHAN[prev=none]}}
\immediate\openin1=|"repstopdf lpt.eps"\relax
x
\end{document}
"""
ORPHAN2_EPS = """%!PS-Adobe-3.0 EPSF-3.0
%%BoundingBox: 0 0 100 100
0 1 40000000 { pop } for
/Courier findfont 8 scalefont setfont 10 50 moveto (slow) show
showpage
"""
SEMANTICS_DOCS = {
    "fs_meta": (FS_META_TEX, {"sub/f%d" % i: "%d\n" % i for i in range(1, 41)}),
    "raceflip": (RACEFLIP_TEX, {"lpt.eps": GS_SANDBOX_EPS}),
    "orphan2": (ORPHAN2_TEX, {"lpt.eps": ORPHAN2_EPS}),
}


def check_semantics(name: str, run: dict) -> list[str]:
    log = unwrap(run[".log"])
    bad = []
    if name == "fs_meta":
        sizes = re.findall(r"^LPPIPE\[texosquery-jre8 -s (\.|sub)\]=\[([0-9]+)", log, re.M)
        if len(sizes) != 2 or any(v != "4096" for _, v in sizes):
            bad.append(f"C-195: a directory's size is the file system's, not 4096: {sizes}")
    if name == "raceflip":
        m = re.findall(r"LPFLIP polls-until-gs-done=\[([0-9]+)\]", log)
        if m != ["1"]:
            bad.append(f"C-196: the pipe child was still running when TeX read its "
                       f"output (polls {m}; the defined schedule gives 1)")
    if name == "orphan2":
        final = run["files"].get("lpt.pdf")
        m = re.findall(r"LPORPHAN\[prev=([^\]]*)\]", log)
        size = run.get("sizes", {}).get("lpt.pdf")
        if not size or m != [str(size)]:
            bad.append(f"C-196: the last pass read an unfinished lpt.pdf (it saw "
                       f"{m}, the finished file has {size} bytes; digest {str(final)[:12]})")
    return bad


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
            "interpreters": (interpreters(), {"lpt.eps": EPS, "lpmz.mmz": ""}),
            **SANDBOX_DOCS, **SEMANTICS_DOCS}


def grade(o, name: str, src: str, extra: dict, sub: str = "w") -> dict:
    with o.tempdir(prefix="lp-determinism-") as td:
        work = Path(td) / sub
        work.mkdir(parents=True)
        if sub != "w":   # a variant: another path, maybe another user
            for d in [work, *work.parents]:
                if d == Path(td):
                    break
                d.chmod(0o777)
        (work / "doc.tex").write_text(src)
        for f, text in extra.items():
            (work / f).parent.mkdir(parents=True, exist_ok=True)
            (work / f).write_text(text)
        r = o.run_to_fixpoint(work, "doc.tex", o.tex_env(td), 300)
        out = {"rc": r.rc, "compiles": r.compiles, "timeout": r.timed_out}
        for ext in (".log", ".pdf"):
            p = work / ("doc" + ext)
            out[ext] = p.read_bytes() if p.exists() else None
        eps = work / "lpt.pdf"
        out["eps_pdf"] = eps.read_bytes() if eps.exists() else None
        out["files"] = {str(f.relative_to(work)): hashlib.sha256(f.read_bytes()).hexdigest()
                        for f in sorted(work.rglob("*")) if f.is_file()}
        out["sizes"] = {str(f.relative_to(work)): f.stat().st_size
                        for f in sorted(work.rglob("*")) if f.is_file()}
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


# LOW-3 of the review of 52b81823: two runs on one host under one pin cannot
# see host dependence. Each VARIANT changes one host-side condition the pins
# and the shim are meant to neutralise, by editing the launch argv of THIS
# process's oracle only; its result must be the baseline's, byte for byte, or
# a refusal naming `want_refusal`.
VARIANTS = (
    ("cpuset 0-2", lambda a: _set(a, "--cpuset-cpus", "0-2"), "C-139 (a)"),
    ("memory 1g", lambda a: _set(_set(a, "--memory", "1g"), "--memory-swap", "1g"), "C-139 (a)"),
    ("user 1234:1234", lambda a: _set(a, "--user", "1234:1234"), None),
    ("deeper work-root path", None, None),
    # C-195 (review of 82638518, H1): the run directory on ANOTHER file system
    # -- a tmpfs volume instead of the bind mount (virtiofs over APFS on a
    # Mac, the runner's ext4 in CI) -- must give identical output.
    ("tmpfs work root", "TMPFS", None),
)
# (no document that makes a subdirectory: under another --user its files
# would not be removable by the host user on a Linux runner)
VARIANT_DOCS = ("pid_probe", "jvm", "fs_meta")


def _set(argv: list, flag: str, value: str) -> list:
    argv = list(argv)
    if flag in argv:
        argv[argv.index(flag) + 1] = value
    else:   # an oracle that does not pin it (0400f74a): add it
        argv[1:1] = [flag, value]
    return argv


def _tmpfs_launch(oracle_mod, o, orig_launch):
    """o._launch with the run directory on a TMPFS inside the engine's own
    container: the host's run directory is bind-mounted at /lp/host instead,
    copied onto the tmpfs before the run and back after it (in the same
    container: a tmpfs does not outlive it). The job's evidence files are
    cleared on the host first, as the supervisor clears them in the run."""

    def launch(name, argv, timeout):
        if "--entrypoint" not in argv or argv[argv.index("--entrypoint") + 1] != "sh":
            return orig_launch(name, argv, timeout)
        argv = list(argv)
        k = next(i for i in range(len(argv) - 1) if argv[i] == "-v"
                 and argv[i + 1].endswith(":" + oracle_mod.RUN_DIR))
        host = argv[k + 1].rsplit(":", 1)[0]
        argv[k:k + 2] = ["-v", f"{host}:/lp/host", "--tmpfs",
                         f"{oracle_mod.RUN_DIR}:rw,nosuid,nodev,size=256m,mode=1777"]
        c = argv.index("-c", argv.index(oracle_mod.IMAGE))
        argv[c + 1] = ("cp -R /lp/host/. " + oracle_mod.RUN_DIR + "/ || exit 3; "
                       + argv[c + 1] + "; cp -R " + oracle_mod.RUN_DIR + "/. /lp/host/")
        for ext in (".log", ".pdf", ".fls", ".fmt"):
            f = Path(host) / ("doc" + ext)
            if f.is_file():
                f.unlink()
        return orig_launch(name, argv, timeout)

    return launch, (lambda: None)


def host_variants(oracle_mod, o, all_docs: dict, base: dict) -> list[str]:
    bad = []
    orig = oracle_mod.launch_argv
    for label, edit, want_refusal in VARIANTS:
        cleanup = None
        if edit == "TMPFS":
            launch, cleanup = _tmpfs_launch(oracle_mod, o, o._launch)
            o._launch = launch
            edit = None
            sub = "w"
        else:
            sub = None
        if edit is not None:
            def patched(*a, _edit=edit, **k):
                argv = orig(*a, **k)
                return _edit(argv) if k.get("entry", (None,))[0] == "sh" else argv
            oracle_mod.launch_argv = patched
        try:
            for name in VARIANT_DOCS:
                if name not in base:
                    continue
                src, extra = all_docs[name]
                where = sub or ("v a/deeper/w" if edit is None else "w")
                try:
                    got = grade(o, name, src, extra, sub=where)
                except oracle_mod.OracleError as e:
                    if isinstance(e, oracle_mod.OracleUnavailable):
                        raise
                    ok = want_refusal is not None and want_refusal in str(e)
                    print(f"[oracle-determinism] variant {label:22s} {name:10s} "
                          f"refused ({'expected' if ok else 'UNEXPECTED'}): {str(e)[:120]}")
                    if not ok:
                        bad.append(f"VARIANT {label}: {name} refused: {str(e)[:200]}")
                    continue
                diff = [k for k in ("rc", "compiles", ".log", ".pdf", "files")
                        if got[k] != base[name][k]]
                print(f"[oracle-determinism] variant {label:22s} {name:10s} "
                      f"graded, differ={diff}")
                if want_refusal is not None:
                    bad.append(f"VARIANT {label}: {name} was GRADED; the pins must "
                               f"refuse it ({want_refusal})")
                elif diff:
                    bad.append(f"VARIANT {label}: {name} differs from the baseline "
                               f"in {diff}")
        finally:
            oracle_mod.launch_argv = orig
            if cleanup is not None:
                o.__dict__.pop("_launch", None)
                cleanup()
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
    base = {}
    all_docs = docs(oracle_mod)
    for name, (src, extra) in all_docs.items():
        try:
            a, b = grade(o, name, src, extra), grade(o, name, src, extra)
        except oracle_mod.OracleError as e:
            if isinstance(e, oracle_mod.OracleUnavailable):
                raise
            bad.append(f"{name}: the oracle refused the document: {str(e)[:200]}")
            continue
        base[name] = a
        if args.dump:
            Path(args.dump).mkdir(parents=True, exist_ok=True)
            for tag, r in (("a", a), ("b", b)):
                (Path(args.dump) / f"{name}.{tag}.log").write_bytes(r[".log"] or b"")
        diff = [k for k in ("rc", "compiles", "timeout", ".log", ".pdf", "eps_pdf")
                if a[k] != b[k]]
        if a["files"] != b["files"]:
            diff.append("files:" + ",".join(sorted(
                k for k in set(a["files"]) | set(b["files"])
                if a["files"].get(k) != b["files"].get(k)))[:200])
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
        if name in SEMANTICS_DOCS:
            bad += [f"{name}: {x}" for x in check_semantics(name, a) + check_semantics(name, b)]
    bad += host_variants(oracle_mod, o, all_docs, base)
    if bad:
        print("[oracle-determinism] FAIL: a graded run observed something that is "
              "not fixed by the protocol:", file=sys.stderr)
        for x in bad:
            print(f"  - {x}", file=sys.stderr)
        return 1
    print(f"[oracle-determinism] OK: {len(all_docs)} documents graded twice each with "
          f"byte-identical rc, verdict, log, PDF and run-directory files; "
          f"{len(VARIANTS)} host variants identical or refused; no bookkeeping path "
          f"readable ({PIDS}+ probes); every /usr/bin-interpreter command "
          f"({', '.join(INTERP_COMMANDS)}) refused {len(TARGETS)} host targets")
    return 0


if __name__ == "__main__":
    sys.exit(main())
