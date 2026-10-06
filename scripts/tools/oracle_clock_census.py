#!/usr/bin/env python3
"""OPEN-128 (1): the CLASS CENSUS of the run-dependent inputs a graded run can observe.

WHY. ADR-015 E10 (owner, 2026-10-05): grading runs with EVERY run-dependent
input fixed. "Every" is a claim about a class, and C-102/C-103 record what
happens when a census of one member is taken for a census of the class
(check_strict_kernel.py's R-CLOCK listed \\year/\\month/\\day/\\time,
\\pdfrandomseed, \\pdfelapsedtime and \\pdffilemoddate, and nothing else). So
the class is enumerated FROM THE ENGINE, not from a list of names:

  * pdfTeX's interface to its environment is the set of C library functions
    it imports (a dynamically linked binary can reach the kernel only through
    them: it imports no `syscall`, MEASURED). `imports` below reads the pinned
    binary's dynamic symbol table out of the image (through the oracle's
    image_command; ELF parsed here) and EVERY imported symbol must carry a
    class in IMPORT_CLASS, or this tool FAILS: a new import cannot be
    unclassified. The classes that read something outside the document's
    bytes are the census rows (CENSUS).
  * The processes pdfTeX starts (restricted \\write18, `\\input|"..."`, mktex*)
    are a second interface: what they print reaches TeX. Their inputs are
    rows too, through the commands the image allows (shell_escape_commands).
  * Each row ends in one of: FIXED by the oracle (and how), PROVEN not
    observable (and why), or EXCLUDED (and the reason).

THE OBSERVATION. Each row that a document can observe has a census document
(DOCS) that prints what it observes as `[LPC:key=value]` lines. The tool
grades each document TWICE through the oracle (`get_oracle().run_to_fixpoint`,
the protocol), in two different run directories, at two times at least
GAP_S seconds apart (so the real clock's \\time would differ), and records
the grade (rc, PDF, passes) and every observed value; a row is shown FIXED
when both grades and all values agree. With `--before CHECKOUT` it also runs
each document twice (one pass) through the oracle of an older checkout (the
`_oracle.py pdflatex` shim of that commit, its own work root) and records
those values: they show that each document really observes a run-dependent
input under the old protocol, so "fixed" is not vacuous.

Writes corpora/oracle_baseline/clock_census.json (a GRADED artefact of
check_oracle_pin: its oracle block names the grading code, stamped at the
run's start). Usage:
  python3 scripts/tools/oracle_clock_census.py --before ../main-checkout \\
      --out corpora/oracle_baseline/clock_census.json
  python3 scripts/tools/oracle_clock_census.py --imports-only
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

GRADER_FILES = ("scripts/tools/oracle_clock_census.py",)
SCHEMA = "lp-oracle-clock-census/1"
GAP_S = 65
TIMEOUT = 300

# ---------------------------------------------------------------- the class
# Every symbol the pinned pdfTeX imports (MEASURED from its .dynsym, 157
# symbols in the aarch64 image), with the class of input it reads. "pure":
# a function of its arguments and of state the run itself created (memory,
# strings, math, the streams of files it opened); the other classes are
# census rows.
_PURE = """
_ITM_deregisterTMCloneTable _ITM_registerTMCloneTable __cxa_finalize
__gmon_start__ __libc_start_main __assert_fail abort exit _exit
__errno_location __isoc99_sscanf sprintf snprintf vsnprintf vsprintf vfprintf
fprintf printf puts putc putchar fputc fputs fwrite fflush fread fgetc getc
ungetc __uflow feof ferror fileno flockfile funlockfile setvbuf fseek fseeko
ftell ftello lseek64 read write close dup fcntl pipe __pthread_key_create
pthread_mutex_lock pthread_mutex_unlock pthread_once _setjmp longjmp calloc
malloc realloc free acos asin atan atan2 cos sin sincos sqrt log log10 pow
modf frexp strtod memchr memcmp memcpy memmove memset strcat strchr strcmp
strcpy strcspn strlen strncat strncmp strncpy strrchr strstr strtok strtol
strtoull stpcpy strcasecmp strncasecmp strerror qsort getopt_long_only optarg
optind regcomp regerror regexec regfree dl_iterate_phdr perror stderr stdin
stdout __ctype_b_loc __ctype_toupper_loc isalnum isalpha islower isspace
isupper isxdigit tolower toupper
""".split()
IMPORT_CLASS = {s: "pure" for s in _PURE}
IMPORT_CLASS.update({
    "time": "clock", "gettimeofday": "clock", "localtime": "timezone",
    "localtime_r": "timezone", "gmtime": "timezone", "strftime": "timezone",
    "__xstat": "file-metadata", "__lxstat": "file-metadata",
    "access": "file-system", "fopen": "file-system", "open": "file-system",
    "opendir": "directory-order", "readdir": "directory-order",
    "closedir": "directory-order", "mkdir": "file-system",
    "remove": "file-system", "rename": "file-system",
    "readlink": "executable-path", "getcwd": "cwd",
    "getenv": "environment", "putenv": "environment",
    "getpid": "pid", "getuid": "user", "getpwuid": "user", "getpwnam": "user",
    "socket": "network", "connect": "network",
    "fork": "children", "execvp": "children", "system": "children",
    "popen": "children", "pclose": "children", "wait": "children",
    "signal": "signals", "sigaction": "signals", "sigaddset": "signals",
    "sigemptyset": "signals", "sleep": "signals",
    "__getauxval": "cpu",
})

# The census: one row per class of run-dependent input (and the ones the
# processes pdfTeX starts add). status: fixed | proven | excluded.
CENSUS = [
    {"id": "clock", "status": "fixed",
     "input": "the wall clock: time(2) and gettimeofday(2)",
     "observed_by": "\\year, \\month, \\day, \\time (texmfmp.c dateandtime: "
                    "time(NULL) unless FORCE_SOURCE_DATE=1 and SOURCE_DATE_EPOCH "
                    "are set), \\pdfcreationdate and the PDF /ID (initstarttime: "
                    "SOURCE_DATE_EPOCH, else time(NULL)), \\pdfrandomseed's "
                    "initial value and so \\pdfuniformdeviate/\\pdfnormaldeviate "
                    "(get_seconds_and_micros: gettimeofday), \\pdfelapsedtime "
                    "and \\pdfresettimer (gettimeofday)",
     "how": "clock_vars(PROTOCOL_CLOCK): SOURCE_DATE_EPOCH=E, FORCE_SOURCE_DATE=1; "
            "the shim (LP_CLOCK_EPOCH=E): gettimeofday/time/clock_gettime(REALTIME) "
            "return E plus one microsecond per read, per process",
     "docs": ["c-date", "c-seed"]},
    {"id": "timezone", "status": "fixed",
     "input": "the time zone: localtime(3) reads TZ and /etc/localtime",
     "observed_by": "\\time/\\day when not forced (localtime), \\pdffilemoddate "
                    "and \\pdfcreationdate's offset (makepdftime)",
     "how": "TZ is not in the engine's environment (an allow-list, engine_env); "
            "/etc/localtime is the image's (-> Etc/UTC, read-only root); with "
            "FORCE_SOURCE_DATE=1 dateandtime uses gmtime",
     "docs": ["c-date", "c-filemoddate"]},
    {"id": "file-metadata", "status": "fixed",
     "input": "file times and sizes: __xstat/__lxstat (st_mtime, st_size)",
     "observed_by": "\\pdffilemoddate (st_mtime: of a source file, of a file the "
                    "run itself wrote, of a TeX tree file), \\pdffilesize "
                    "(st_size; of a file outside the run's view: /proc, /etc)",
     "how": "the shim reports st_atime = st_mtime = st_ctime = E for every "
            "stat-family call; a file outside the TeX file-system view does not "
            "exist (FS_ROOTS); st_size of a file in the view is its content's",
     "docs": ["c-filemoddate", "c-abs-read"]},
    {"id": "file-system", "status": "fixed",
     "input": "what the file system holds outside the document: fopen/open/access",
     "observed_by": "\\input, \\openin, \\pdffiledump, \\pdfmdfivesum file, "
                    "\\pdffilesize of an absolute or ../ path: MEASURED before "
                    "OPEN-128 under openin_any=p, /proc/uptime (the machine's "
                    "uptime: the real clock), /proc/self/stat (pid, CPU times), "
                    "/etc/hostname, /etc/hosts, /etc/resolv.conf (docker's "
                    "per-container files), /dev/urandom",
     "how": "the shim's file-system view: a TeX Live program opens, stats, lists "
            "and changes only paths inside FS_ROOTS (the run directory, the run's "
            "fresh /tmp, the TeX tree) and /dev/null; metadata of the image's own "
            "read-only files is allowed, of /proc, /sys, /dev, docker's files and "
            "/sbin/docker-init not",
     "docs": ["c-abs-read"]},
    {"id": "directory-order", "status": "fixed",
     "input": "the order of a directory's entries: opendir/readdir",
     "observed_by": "kpathsea's directory scans; `l3sys-query ls` (a TeX Live "
                    "program in restricted \\write18) prints it, and its "
                    "`--sort date` keeps it for ties of equal times",
     "how": "the shim returns every directory's entries sorted by name in a TeX "
            "Live program",
     "docs": ["c-dirorder"]},
    {"id": "cwd", "status": "fixed",
     "input": "the run directory's absolute path: getcwd(3)",
     "observed_by": "`l3sys-query pwd`; the absolute input paths of a SyncTeX "
                    "file and of a -recorder file list (its PWD line) a later pass "
                    "can \\input; "
                    "before OPEN-128 also `kpsewhich -var-value=TMPDIR` (the "
                    "private trees were under the run's temporary directory)",
     "how": "every run's directory is bind-mounted at the fixed RUN_DIR (/lp/run), "
            "its private trees and TMPDIR live at fixed paths on its fresh tmpfs",
     "docs": ["c-cwd", "c-children"]},
    {"id": "environment", "status": "fixed",
     "input": "the process environment: getenv(3)",
     "observed_by": "kpathsea reads ANY variable named after a configuration key "
                    "(C-91); `kpsewhich -var-value=NAME` in restricted \\write18 "
                    "prints any variable, e.g. HOSTNAME, TMPDIR, TEXMFVAR",
     "how": "the engine's environment is EXACTLY engine_env(...): IMAGE_ENV plus "
            "the oracle's own fixed values (ORACLE_TEX_VARS, FIXED_RUN_VARS, the "
            "clock), passed verbatim by the supervisor (not even docker's "
            "HOSTNAME)",
     "docs": ["c-children"]},
    {"id": "executable-path", "status": "fixed",
     "input": "readlink(/proc/self/exe): kpathsea's SELFAUTOLOC",
     "observed_by": "kpathsea's search paths (TEXMFCNF ...)",
     "how": "the image's path of the binary (read-only, digest-pinned)",
     "docs": []},
    {"id": "pid", "status": "fixed",
     "input": "the process id: getpid(2)",
     "observed_by": "only the -recorder's temporary file list, named after the "
                    "pid (texmfmp.c recorder_start) and renamed to the job's; "
                    "graders do not pass "
                    "-recorder, and a document cannot set it",
     "how": "every run is a fresh container: a fresh pid namespace, so the engine's "
            "pid is the same in every run (MEASURED: the supervisor reports it, "
            "engine_pid)",
     "docs": ["c-date"]},
    {"id": "user", "status": "proven",
     "input": "the user id and the password database: getuid, getpwuid, getpwnam",
     "observed_by": "kpathsea's ~ expansion: `~` reads HOME first (always /tmp), "
                    "`~name` reads the IMAGE's /etc/passwd (getpwnam)",
     "how": "not observable as a value: no primitive or restricted command prints "
            "the uid; the uid is the host user's (501 on the laptop, the runner's "
            "on CI): a PLATFORM residual recorded in platform_residuals.json",
     "docs": ["c-children"]},
    {"id": "network", "status": "fixed",
     "input": "the network: socket/connect",
     "observed_by": "pdfTeX connects only for -ipc (not on the graded argv "
                    "allow-list); a restricted \\write18 command could",
     "how": "--network none in the launch definition",
     "docs": []},
    {"id": "children", "status": "fixed",
     "input": "what the processes pdfTeX starts print: restricted \\write18, "
              "`\\input|\"cmd\"`, mktex*",
     "observed_by": "shell_escape_commands of the image (bibtex, bibtex8, "
                    "extractbb, gregorio, kpsewhich, l3sys-query, latexminted, "
                    "makeindex, memoize-extract.pl/.py, repstopdf, r-mpost, "
                    "texosquery-jre8): texosquery prints the date (-n) and the "
                    "kernel (-r), l3sys-query the cwd and listings, kpsewhich the "
                    "environment and the existence of any path",
     "how": "children inherit the environment, the clock and the shim (LD_PRELOAD "
            "survives exec); the shim fixes their clock, file times, uname "
            "release/version, and, for TeX Live programs, the file-system view and "
            "directory order; PYTHONHASHSEED/PERL_HASH_SEED/PERL_PERTURB_KEYS fix "
            "the hash order of the Python and Perl ones; the host name is fixed "
            "(--hostname)",
     "docs": ["c-children", "c-dirorder"]},
    {"id": "kpathsea-cache", "status": "fixed",
     "input": "kpathsea's state across runs: ls-R databases, fonts made by "
              "mktexpk, configuration in TEXMFCONFIG",
     "observed_by": "which file \\input or \\font finds; whether a font is "
                    "generated (the run's output)",
     "how": "the image's ls-R (read-only); TEXMFHOME/TEXMFVAR/TEXMFCONFIG private "
            "to each run on its fresh tmpfs (FIXED_TREES): a font mktexpk makes is "
            "made again by the next pass, identically",
     "docs": ["c-mktex"]},
    {"id": "signals", "status": "proven",
     "input": "signals and sleep",
     "observed_by": "nothing a document reads: the run's own timeout (a timeout is "
                    "never a grade)",
     "how": "a run killed by the protocol's timeout or the memory ceiling is "
            "ungraded (rc 124/137)",
     "docs": []},
    {"id": "cpu", "status": "excluded",
     "input": "the CPU: __getauxval (hardware capabilities), its speed, the "
              "number of CPUs (no import; java's availableProcessors)",
     "observed_by": "nothing a document reads through a primitive; the speed "
                    "decides whether a long run meets the timeout",
     "how": "EXCLUDED: the architecture is fixed (aarch64, ADR-015 E2), and a "
            "timeout is never a grade; the CPU model and speed differ between the "
            "laptop and the CI runner (platform_residuals.json)",
     "docs": []},
    {"id": "random-device", "status": "excluded",
     "input": "/dev/urandom and getrandom in the processes pdfTeX starts",
     "observed_by": "pdfTeX itself cannot read it (the file-system view refuses "
                    "/dev); a child could seed something it prints",
     "how": "EXCLUDED: no restricted command of the image prints a value drawn "
            "from it (bibtex, makeindex, kpsewhich, l3sys-query: deterministic; "
            "texosquery prints no random value; latexminted/memoize: hash seeds "
            "fixed); not measured exhaustively",
     "docs": []},
    {"id": "file-system-semantics", "status": "excluded",
     "input": "the work root's file system: case- and Unicode-normalisation-"
              "insensitive names (APFS through virtiofs on a Mac) vs case-"
              "sensitive ext4 (the CI runner); directory sizes and link counts",
     "observed_by": "\\input{Foo} finding foo.tex on the laptop only; NFD/NFC "
                    "names",
     "how": "EXCLUDED here and MEASURED as a platform residual (OPEN-128 (8), "
            "platform_residuals.json): the owner chooses O3.2 (grades of record "
            "from CI only) or O3.3 (a VM-local Linux work root)",
     "docs": []},
]

DOCS = {
    "c-date": r"""\documentclass{article}
\begin{document}
\typeout{[LPC:year=\the\year]}\typeout{[LPC:month=\the\month]}
\typeout{[LPC:day=\the\day]}\typeout{[LPC:time=\the\time]}
\typeout{[LPC:creationdate=\pdfcreationdate]}
\typeout{[LPC:today=\today]}
x
\end{document}
""",
    "c-seed": r"""\documentclass{article}
\begin{document}
\typeout{[LPC:seed=\the\pdfrandomseed]}
\typeout{[LPC:uniform=\pdfuniformdeviate 1000000]}
\typeout{[LPC:normal=\pdfnormaldeviate]}
\typeout{[LPC:elapsed=\the\pdfelapsedtime]}
\pdfresettimer\typeout{[LPC:elapsed-after-reset=\the\pdfelapsedtime]}
x
\end{document}
""",
    "c-filemoddate": r"""\documentclass{article}
\begin{document}
\typeout{[LPC:moddate-source=\pdffilemoddate{\jobname.tex}]}
\typeout{[LPC:moddate-tree=\pdffilemoddate{article.cls}]}
\immediate\openout9=lpc-written.txt \immediate\write9{x}\immediate\closeout9
\typeout{[LPC:moddate-written=\pdffilemoddate{lpc-written.txt}]}
\def\lpcext{aux}\typeout{[LPC:moddate-aux=\pdffilemoddate{\jobname.\lpcext}]}
\typeout{[LPC:size-source=\pdffilesize{\jobname.tex}]}
x
\end{document}
""",
    "c-abs-read": r"""\documentclass{article}
\begin{document}
\typeout{[LPC:dump-uptime=\pdffiledump offset 0 length 16 {/proc/uptime}]}
\typeout{[LPC:md5-procstat=\pdfmdfivesum file{/proc/self/stat}]}
\typeout{[LPC:md5-version=\pdfmdfivesum file{/proc/version}]}
\typeout{[LPC:md5-cpuinfo=\pdfmdfivesum file{/proc/cpuinfo}]}
\typeout{[LPC:size-meminfo=\pdffilesize{/proc/meminfo}]}
\typeout{[LPC:md5-hostname=\pdfmdfivesum file{/etc/hostname}]}
\typeout{[LPC:md5-hosts=\pdfmdfivesum file{/etc/hosts}]}
\typeout{[LPC:md5-resolv=\pdfmdfivesum file{/etc/resolv.conf}]}
\typeout{[LPC:size-dockerinit=\pdffilesize{/sbin/docker-init}]}
\typeout{[LPC:dump-urandom=\pdffiledump offset 0 length 8 {/dev/urandom}]}
\typeout{[LPC:md5-parent=\pdfmdfivesum file{../../etc/hostname}]}
\newread\lpcr
\openin\lpcr=/proc/uptime
\ifeof\lpcr\typeout{[LPC:openin-uptime=refused]}\else
\read\lpcr to\lpcl\typeout{[LPC:openin-uptime=\lpcl]}\closein\lpcr\fi
x
\end{document}
""",
    "c-children": r"""\documentclass{article}
\makeatletter
\def\lpcq#1#2{\begingroup\everyeof{\noexpand}\endlinechar=-1
  \catcode`\%=12 \catcode`\#=12 \catcode`\_=12 \catcode`\~=12
  \catcode`\$=12 \catcode`\&=12 \catcode`\^=12 \catcode`\\=12
  \edef\lpcx{\@@input|"#2" }\immediate\write16{[LPC:#1=\detokenize\expandafter{\lpcx}]}\endgroup}
\makeatother
\begin{document}
\lpcq{kpse-hostname}{kpsewhich -var-value=HOSTNAME}
\lpcq{kpse-tmpdir}{kpsewhich -var-value=TMPDIR}
\lpcq{kpse-texmfvar}{kpsewhich -var-value=TEXMFVAR}
\lpcq{kpse-home}{kpsewhich -var-value=HOME}
\lpcq{kpse-pwd}{kpsewhich -var-value=PWD}
\lpcq{kpse-user}{kpsewhich -var-value=USER}
\lpcq{kpse-sde}{kpsewhich -var-value=SOURCE_DATE_EPOCH}
\lpcq{kpse-proc-uptime}{kpsewhich /proc/uptime}
\lpcq{kpse-sys-virtio}{kpsewhich /sys/bus/virtio}
\lpcq{l3-pwd}{l3sys-query pwd}
\lpcq{tosq-now}{texosquery-jre8 -n}
\lpcq{tosq-osname}{texosquery-jre8 -o}
\lpcq{tosq-osversion}{texosquery-jre8 -r}
\lpcq{tosq-osarch}{texosquery-jre8 -a}
x
\end{document}
""",
    "c-dirorder": r"""\documentclass{article}
\makeatletter
\def\lpcq#1#2{\begingroup\everyeof{\noexpand}\endlinechar=`\,
  \catcode`\%=12 \catcode`\#=12 \catcode`\_=12 \catcode`\~=12
  \catcode`\$=12 \catcode`\&=12 \catcode`\^=12 \catcode`\\=12
  \edef\lpcx{\@@input|"#2" }\immediate\write16{[LPC:#1=\detokenize\expandafter{\lpcx}]}\endgroup}
\makeatother
\begin{document}
\immediate\openout9=lpc-zeta.txt \immediate\write9{z}\immediate\closeout9
\immediate\openout9=lpc-alpha.txt \immediate\write9{a}\immediate\closeout9
\immediate\openout9=lpc-mid.txt \immediate\write9{m}\immediate\closeout9
\lpcq{l3-ls-date}{l3sys-query ls --sort date --pattern ^lpc}
\lpcq{l3-ls-name}{l3sys-query ls --pattern ^lpc}
x
\end{document}
""",
    "c-cwd": r"""\documentclass{article}
\makeatletter
\def\lpcq#1#2{\begingroup\everyeof{\noexpand}\endlinechar=-1
  \catcode`\%=12 \catcode`\#=12 \catcode`\_=12 \catcode`\~=12
  \catcode`\$=12 \catcode`\&=12 \catcode`\^=12 \catcode`\\=12
  \edef\lpcx{\@@input|"#2" }\immediate\write16{[LPC:#1=\detokenize\expandafter{\lpcx}]}\endgroup}
\makeatother
\begin{document}
\lpcq{pwd}{l3sys-query pwd}
\lpcq{kpse-self}{kpsewhich \jobname.tex}
x
\end{document}
""",
    "c-mktex": r"""\documentclass{article}
\makeatletter
\def\lpcq#1#2{\begingroup\everyeof{\noexpand}\endlinechar=-1
  \catcode`\%=12 \catcode`\#=12 \catcode`\_=12 \catcode`\~=12
  \catcode`\$=12 \catcode`\&=12 \catcode`\^=12 \catcode`\\=12
  \edef\lpcx{\@@input|"#2" }\immediate\write16{[LPC:#1=\detokenize\expandafter{\lpcx}]}\endgroup}
\makeatother
\begin{document}
\font\lpcbbm=bbm10 {\lpcbbm A}\clearpage
\lpcq{pk-after-shipout}{kpsewhich bbm10.600pk}
x
\end{document}
""",
}
LPC = re.compile(r"\[LPC:([A-Za-z0-9-]+)=(.*?)\]")


# ------------------------------------------------------------- the imports
def elf_undefined_dynsyms(data: bytes) -> list[str]:
    """The undefined symbols of an ELF64 little-endian object's .dynsym."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError("not an ELF64 little-endian file")
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", data, 0x3A)
    secs = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize)
            for i in range(shnum)]
    dynsym = [s for s in secs if s[1] == 11]  # SHT_DYNSYM
    if len(dynsym) != 1:
        raise ValueError("no single .dynsym")
    _, _, _, _, off, size, link, _, _, entsize = dynsym[0]
    stroff = secs[link][4]
    out = set()
    for k in range(1, size // entsize):
        name, info, other, shndx, value, sz = struct.unpack_from(
            "<IBBHQQ", data, off + k * entsize)
        if shndx != 0:
            continue                    # defined here
        end = data.index(b"\0", stroff + name)
        nm = data[stroff + name:end].decode()
        if nm:
            out.add(nm)
    return sorted(out)


def engine_imports(o) -> dict:
    rc, path, err = o.image_command(
        ["readlink", "-f", f"{_oracle.TEXMF_ROOT}/2026/bin/aarch64-linux/"
                           f"{_oracle.ENGINE_PDFTEX}"])
    if rc != 0:
        raise _oracle.OracleError(f"cannot locate pdftex: {err[:200]!r}")
    path = path.decode().strip()
    rc, data, err = o.image_command(["cat", path])
    if rc != 0:
        raise _oracle.OracleError(f"cannot read {path}: {err[:200]!r}")
    syms = elf_undefined_dynsyms(data)
    return {"binary": path, "sha256": hashlib.sha256(data).hexdigest(),
            "symbols": {s: IMPORT_CLASS.get(s) for s in syms},
            "imports_syscall": "syscall" in syms,
            "imports_clock_gettime": "clock_gettime" in syms,
            "imports_uname": "uname" in syms or "gethostname" in syms}


# -------------------------------------------------------------- the grades
def grade(o, name: str, tex: str) -> dict:
    """One protocol grade (run_to_fixpoint) of a census document, in a fresh
    run directory, plus one more pass for the supervisor's evidence."""
    with o.tempdir(prefix=f"lp-census-{name}-") as td:
        d = Path(td) / "w"
        d.mkdir()
        (d / f"{name}.tex").write_text(tex, encoding="utf-8")
        t0 = time.time()
        r = o.run_to_fixpoint(d, f"{name}.tex", o.tex_env(), TIMEOUT)
        log = _oracle.job_output(d, f"{name}.tex", ".log")
        text = log.read_text(errors="replace") if log.is_file() else ""
        ev_run = o.run_pdflatex(d, ["-interaction=nonstopmode", f"{name}.tex"],
                                o.tex_env(), TIMEOUT)
        ev = getattr(ev_run, "evidence", {}) or {}
        return {"dir": str(Path(td).name), "at": int(t0),
                "rc": r.rc, "pdf": r.pdf, "passes": r.passes,
                "timed_out": r.timed_out,
                "values": dict(LPC.findall("".join(
                    ln for ln in text.split("\n")))) if text else {},
                "engine_pid": ev.get("engine_pid"),
                "fs_denied": ev.get("fs_denied", [0])[0] if ev.get("fs_denied") else 0}


def before_values(checkout: Path, name: str, tex: str, workroot: Path) -> dict:
    """One pass of the document through the OLDER checkout's oracle shim
    (`_oracle.py pdflatex`, its own long-lived container and work root):
    the values a document observed under the protocol before OPEN-128."""
    workroot.mkdir(parents=True, exist_ok=True)
    d = Path(tempfile.mkdtemp(prefix=f"lp-census-before-{name}-", dir=workroot))
    try:
        (d / f"{name}.tex").write_text(tex, encoding="utf-8")
        env = dict(os.environ, LP_ORACLE_WORKROOT=str(workroot))
        env.pop("LP_ORACLE_IN_IMAGE", None)
        p = subprocess.run([sys.executable, str(checkout / "scripts/tools/_oracle.py"),
                            "pdflatex", "--timeout", str(TIMEOUT),
                            "-interaction=nonstopmode", f"{name}.tex"],
                           cwd=d, env=env, capture_output=True, timeout=TIMEOUT + 120)
        log = _oracle.job_output(d, f"{name}.tex", ".log")
        text = log.read_text(errors="replace") if log.is_file() else ""
        return {"at": int(time.time()), "rc": p.returncode,
                "values": dict(LPC.findall(text.replace("\n", "")))}
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--out", default="corpora/oracle_baseline/clock_census.json")
    ap.add_argument("--before", default=None,
                    help="a checkout of the older oracle (e.g. origin/main before "
                         "OPEN-128) to run each document through, for the control")
    ap.add_argument("--before-workroot",
                    default=str(Path.home() / ".cache" / "lp-o128" / "census-before"))
    ap.add_argument("--gap", type=int, default=GAP_S)
    ap.add_argument("--imports-only", action="store_true")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    try:
        stamp = _oracle.RunStamp(GRADER_FILES, repo)
        o = _oracle.get_oracle()
        imp = engine_imports(o)
    except _oracle.OracleError as e:
        print(f"[census] FATAL: {e}", file=sys.stderr)
        return 2
    unclassified = sorted(s for s, c in imp["symbols"].items() if c is None)
    stale = sorted(set(IMPORT_CLASS) - set(imp["symbols"]))
    print(f"[census] pdfTeX imports {len(imp['symbols'])} symbols; "
          f"unclassified {unclassified}; classified but not imported {stale}")
    rows_ids = {r["id"] for r in CENSUS}
    missing_rows = sorted({c for c in imp["symbols"].values()
                           if c not in (None, "pure") and c not in rows_ids})
    if unclassified or missing_rows:
        print(f"[census] FAIL: every import needs a class and every class a "
              f"census row (unclassified {unclassified}, classes without a row "
              f"{missing_rows})", file=sys.stderr)
        return 1
    if ns.imports_only:
        return 0
    docs = {}
    first = {}
    for name, tex in DOCS.items():
        first[name] = grade(o, name, tex)
        print(f"[census] {name} run 1: rc {first[name]['rc']} pdf "
              f"{first[name]['pdf']} {first[name]['values']}", flush=True)
    print(f"[census] waiting {ns.gap} s before the second grades", flush=True)
    time.sleep(ns.gap)
    for name, tex in DOCS.items():
        second = grade(o, name, tex)
        a, b = first[name], second
        same = all(a[k] == b[k] for k in ("rc", "pdf", "passes", "values",
                                           "engine_pid"))
        docs[name] = {"sha256": hashlib.sha256(tex.encode()).hexdigest(),
                      "tex": tex, "runs": [a, b], "fixed": same}
        print(f"[census] {name} run 2: rc {b['rc']} pdf {b['pdf']} -> "
              f"{'SAME' if same else 'DIFFERS'}", flush=True)
    if ns.before:
        ck = Path(ns.before).resolve()
        for name, tex in DOCS.items():
            b1 = before_values(ck, name, tex, Path(ns.before_workroot))
            time.sleep(ns.gap)
            b2 = before_values(ck, name, tex, Path(ns.before_workroot))
            moved = sorted(k for k in set(b1["values"]) | set(b2["values"])
                           if b1["values"].get(k) != b2["values"].get(k)
                           or b1["values"].get(k) != docs[name]["runs"][0]["values"].get(k))
            docs[name]["before"] = {"commit": subprocess.run(
                ["git", "-C", str(ck), "rev-parse", "HEAD"], capture_output=True,
                text=True).stdout.strip(), "runs": [b1, b2],
                "keys_run_dependent_before": moved}
            print(f"[census] {name} before: keys that differ between the two "
                  f"old runs or from the fixed value: {moved}", flush=True)
    why = stamp.check()
    if why:
        print(f"[census] FATAL: {why}", file=sys.stderr)
        return 2
    out = {
        "schema": SCHEMA,
        "generator": "scripts/tools/oracle_clock_census.py",
        "measured_at_sha": stamp.head,
        "oracle": stamp.oracle_block(o),
        "method": ("each document graded twice through the oracle (run_to_fixpoint, "
                   f"the protocol), in two run directories, {ns.gap} s apart; a "
                   "row's documents show it FIXED when the two grades and every "
                   "[LPC:...] value agree; `before` runs each document twice, one "
                   "pass, through the oracle of the given older checkout"),
        "engine_imports": imp,
        "census": CENSUS,
        "documents": docs,
        "summary": {"documents": len(docs),
                    "fixed": sum(1 for d in docs.values() if d["fixed"]),
                    "rows": {s: sum(1 for r in CENSUS if r["status"] == s)
                             for s in ("fixed", "proven", "excluded")}},
    }
    p = repo / ns.out
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=1, sort_keys=False) + "\n")
    print(f"[census] wrote {ns.out}: {out['summary']}")
    return 0 if out["summary"]["fixed"] == len(docs) else 1


if __name__ == "__main__":
    sys.exit(main())
