#!/usr/bin/env python3
"""Gate: an oracle that did not run pdfTeX is NEVER graded as a pdflatex result.

WHY (OPEN-118, adversarial review round 2, 2026-09-27). The first fix for
"infrastructure failures are graded" recognised an oracle failure by its SHAPE:
rc 125-127, or a non-zero rc with "Error response from daemon" on stderr. That
is a blacklist, and it missed a realistic shape. MEASURED with a docker wrapper
that sends `docker exec` to a dead socket (colima restarting, the VM gone): the
docker CLI prints "failed to connect to the docker API ..." and exits 1, and
  - the `_oracle.py pdflatex` shim exited 1 (a pdflatex failure, not 125);
  - `run_to_fixpoint` returned OracleRun(rc=1, pdf=False): a graded FAILS in
    diff_real_roots, gen_apply_fixes_real_differential, gen_strict_battery and
    regrade_sample;
  - check_apply_fixes_roundtrip.pdflatex_ok returned False ("fails");
  - false_ready_oracle.sh, with only its -halt-on-error passes lost, exited 0
    with 66 `ok` rows although no halt-protocol pdflatex had run.

The rule is now a whitelist (see `_oracle.PDFTEX_BANNER`): a run's rc counts
only with POSITIVE PROOF that pdfTeX produced it -- pdfTeX's banner in that
run's own output, and (container) the rc reported by a shell INSIDE the
container on a per-run nonce line rather than the docker client's rc.

Round 3 (2026-09-27): proof that pdfTeX RAN is not proof its rc is the
DOCUMENT's. MEASURED: with the work root full, pdfTeX prints its banner, fails
on its own output ("I can't write on file `t.log'", "fwrite() failed") and
exits 1, which every grader graded FAILS. So a run is also refused when the
work root is below a free-space floor (before and after the run) or pdfTeX
could not write its own output; a document's own \\openout refusal is still
graded. Known residuals are listed in OPEN-118 (OOM-as-timeout, clock, VM disk).

C-91 (2026-09-28): ONE grading environment. `grading_env` drives every entry
point (run_pdflatex, the shim on the container and native backends,
check_apply_fixes_roundtrip.pdflatex_ok) under a HOSTILE host environment and
reads back what reached the engine: exactly ORACLE_TEX_VARS, a private
TEXMFHOME/TEXMFVAR, no other TeX variable; `_oracle.sh` must route both
backends through the shim; image_command must start no engine by any route.
Review round 4: those checks named the variables that must NOT reach the
engine, and a host `openout_any_pdflatex=a` (a kpathsea form nobody listed)
flipped a grade on the native backend. They now assert what MAY reach it --
the image's own environment (`_oracle.IMAGE_ENV`) plus the run's TeX
variables -- and the container backend must refuse a container whose own
environment is not the image's.

C-93 (2026-09-29): a PRIVATE TMPDIR per run. MEASURED: a restricted-\\write18
repstopdf -> Ghostscript conversion killed by the protocol's timeout left
/tmp/gs_* in the long-lived container, and check_state then refused every
later session (java under texosquery-jre8 touched /tmp/hsperfdata_root on
every run). Every run now gets TMPDIR=TMP=TEMP=<run dir>/lp-tmp and a
JAVA_TOOL_OPTIONS naming it; the checks read back that the engine got them,
that the directory existed before it started, that a TMPDIR which is not the
run's own is refused, and that the container backend refuses one outside the
work root.

C-95 (2026-09-29): each run's evidence is its own. A stale PDF (or log, .fls,
.fmt) from an earlier pass or run was read as the current one's by three
copies of the pass loop (run_to_fixpoint, false_ready_oracle.sh through the
shim, gen_contract.py through run_engine). The per-run primitive now clears
them; the checks drive each entry point with stale outputs present.

C-97 (2026-09-29): the long-lived container reaps (--init), is bounded
(--pids-limit), is replaced when an older oracle started it without them,
and no run starts beside a leaked process (a zombie or an orphan of PID 1):
MEASURED, leaked processes made a fork inside \\write18 fail silently and a
compiling document grade rc 1.

This gate is PURE (no docker, no TeX): it drives the real grading code with
FAKE docker/engine executables that reproduce each failure shape, including the
re-reviewer's dead-socket one, and asserts each is refused, while a genuine
pdfTeX failure (banner present, rc 1) is still graded. Its kill-tests in
check_gate_selftests.py revert each proof check and must make it fail.

Run: python3 scripts/tools/check_oracle_infra_grading.py --repo .
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

DEAD_MSG = ("failed to connect to the docker API at unix:///nonexistent.sock; "
            "check if the path is correct and if the daemon is running: dial "
            "unix /nonexistent.sock: connect: no such file or directory")

# A fake `docker`. It answers `exec ... rm ...` with success and every run
# `exec ... sh -c SCRIPT sh NONCE TIMEOUT ARGS...` according to FAKE_MODE (one
# mode per call, consumed from a comma-separated FAKE_PLAN via FAKE_COUNT):
#   ok        banner on stdout, nonce line rc=0
#   fail      banner + a TeX error on stdout, nonce line rc=1 (a REAL failure)
#   dead      nothing on stdout, DEAD_MSG on stderr, exit 1 (the measured shape)
#   daemonerr "Error response from daemon: No such container", exit 1
#   cut       banner on stdout, then the stream is lost: no nonce line, exit 1
#   nobanner  nothing on stdout, nonce line rc=1 (something else exited 1)
#   timeout   nonce line rc=124
#   fwrite    banner, then pdfTeX failing to write its PDF, nonce line rc=1
#             (the MEASURED disk-full shape, OPEN-118 review round 3)
#   cantlog   banner, then "! I can't write on file `t.log'.", nonce rc=1
#   openout   banner, then the DOCUMENT's own \openout refused under
#             openout_any=p ("I can't write on file `../x.tex'"), nonce rc=1:
#             a real document failure, must still be graded
FAKE_DOCKER = r'''#!/usr/bin/env python3
import os, sys
a = sys.argv[1:]
if os.environ.get("FAKE_STDIN"):   # what the docker client got on stdin
    open(os.environ["FAKE_STDIN"], "wb").write(sys.stdin.buffer.read())
if os.environ.get("FAKE_ARGV"):
    open(os.environ["FAKE_ARGV"], "w").write("\0".join(a))
    # C-93: did the run's private TMPDIR exist when the engine would start?
    t = [x[7:] for x in a if x.startswith("TMPDIR=")]
    open(os.environ["FAKE_ARGV"] + ".tmpdir", "w").write(
        "1" if t and os.path.isdir(t[0]) else "0")
if os.environ.get("FAKE_CALLS"):        # _ensure_container's docker calls
    open(os.environ["FAKE_CALLS"], "a").write(" ".join(a) + "\n")
st = os.environ.get("FAKE_STATE")
if a[:1] == ["version"]:
    print("27.0"); sys.exit(0)
if a[:2] == ["image", "inspect"] or a[:1] == ["start"]:
    sys.exit(0)
if a[:2] == ["rm", "-f"]:
    if st: open(st, "w").write("absent")
    sys.exit(0)
if a[:2] == ["run", "-d"]:
    if st: open(st, "w").write("present")
    sys.exit(0)
if a[:1] == ["inspect"] and "--format" in a and st:
    present = open(st).read() == "present"
    f = a[a.index("--format") + 1]
    if not present:
        sys.exit(1)
    if f.startswith("{{.State.Running}} {{.Config.Image}}"):
        print(os.environ["FAKE_INSPECT"]); sys.exit(0)
    if f == "{{.State.Running}}":
        print("true"); sys.exit(0)
    if f.startswith("{{.HostConfig.Init}}"):
        print(os.environ.get("FAKE_HOSTCFG", "true 4096")); sys.exit(0)
if a[:1] == ["inspect"] and len(a) == 2 and st:
    sys.exit(0 if open(st).read() == "present" else 1)
if a[:1] == ["exec"] and "cat" in a and st:   # the mount probe
    sys.stdout.write(open(a[-1]).read()); sys.exit(0)
if a[-2:] == ["env", "-0"]:            # the container's own environment
    sys.stdout.write(open(os.environ["FAKE_CENV"]).read()); sys.exit(0)
if a[:1] == ["inspect"] and "{{.Created}}" in a:   # check_state's reference
    print("2026-09-27T06:39:58.151938648Z"); sys.exit(0)
if a[:1] == ["exec"] and "find" in a and "-newerct" in a:  # check_state's scan
    sys.stdout.write(os.environ.get("FAKE_FIND", "d /tmp\n")); sys.exit(0)
if a[:1] == ["exec"] and "python3" not in a and "-c" in a \
        and "kpsewhich -var-value" in a[a.index("-c") + 1]:
    sys.stdout.write(os.environ.get(      # check_texmf_trees
        "FAKE_TREES", "D /tmp/texmf\nD /tmp/.texlive2026/texmf-var\n"
        "D /tmp/.texlive2026/texmf-config\n")); sys.exit(0)
if a[:1] == ["exec"] and "python3" in a:  # the tree fingerprint snippet
    sys.stdout.write(os.environ.get("FAKE_FP", "{}")); sys.exit(0)
if a[:1] == ["exec"] and "-c" not in a:
    sys.exit(0)                       # `exec NAME rm -f -- ...`
plan = os.environ["FAKE_PLAN"].split(",")
cf = os.environ["FAKE_COUNT"]
n = int(open(cf).read()) if os.path.exists(cf) else 0
open(cf, "w").write(str(n + 1))
mode = plan[min(n, len(plan) - 1)]
i = a.index("-c")
nonce = a[i + 3]
banner = "This is pdfTeX, Version 3.141592653-2.6-1.40.29 (TeX Live 2026)\n"
def rcline(rc):
    # the run supervisor's evidence line (C-99), then the in-container rc line
    evid = os.environ.get("FAKE_EVID", '{"alias": [], "cw": {}, "err": "", "overflow": 0}')
    if evid != "OMIT":   # OMIT: a supervisor that died before reporting
        sys.stderr.write("\n%s_EVID=%s\n" % (nonce, evid))
    sys.stderr.write("\n%s=%d\n" % (nonce, rc))
if mode == "ok":
    sys.stdout.write(banner + "Output written on t.pdf (1 page).\n"); rcline(0)
elif mode == "fail":
    sys.stdout.write(banner + "! Undefined control sequence.\n"); rcline(1)
elif mode == "dead":
    sys.stderr.write("%s\n" % os.environ["DEAD_MSG"]); sys.exit(1)
elif mode == "daemonerr":
    sys.stderr.write("Error response from daemon: No such container\n"); sys.exit(1)
elif mode == "cut":
    sys.stdout.write(banner); sys.exit(1)
elif mode == "nobanner":
    rcline(1)
elif mode == "timeout":
    rcline(124)
elif mode == "fwrite":
    sys.stdout.write(banner + "!pdfTeX error: pdflatex (file t.pdf): fwrite() failed\n"); rcline(1)
elif mode == "cantlog":
    sys.stdout.write(banner + "! I can't write on file `t.log'.\n"); rcline(1)
elif mode == "openout":
    sys.stdout.write(banner + "! I can't write on file `../x.tex'.\n"); rcline(1)
elif mode == "leak":       # the in-container leak check refused (C-97)
    sys.stderr.write("\n%s_LEAK=301:gs:Z \n" % nonce)
elif mode in ("batchforge", "termtail", "batchok", "errforge", "termonly", "synctex"):
    # batchforge: the terminal carries a FORGED report, the log pdfTeX's real
    # "No pages of output." (\\batchmode silenced it on the terminal);
    # termtail: text after the terminal's report; batchok: a page shipped,
    # the terminal silent (\\batchmode), the log reports it; errforge: a page
    # shipped after the document printed a forged "! ..." error line;
    # termonly: the terminal reports a page, the log carries no report at
    # all; synctex: a page shipped with \\synctex=1 (pdfTeX's own SyncTeX
    # line on the terminal between its report and the transcript line).
    cwd = a[a.index("-w") + 1]
    job = a[-1].rsplit("/", 1)[-1].rpartition(".")[0]
    real = ("No pages of output." if mode == "batchforge"
            else "Output written on %s.pdf (1 page, 999 bytes)." % job)
    if mode != "batchforge":
        open(os.path.join(cwd, job + ".pdf"), "w").write("%PDF-1.5 x\n")
    open(os.path.join(cwd, job + ".log"), "w").write(
        banner + "! Undefined control sequence.\nl.3 \\foo\n"
        + ("" if mode == "termonly" else real
           + "\nPDF statistics:\n 3 PDF objects out of 1000\n\n"))
    term = {"batchforge": "Output written on %s.pdf (1 page, 9 bytes).\n"
                          "Transcript written on %s.log.\n" % (job, job),
            "termtail": real + "\nTranscript written on %s.log.\nMORE\n" % job,
            "batchok": "",
            "termonly": real + "\nTranscript written on %s.log.\n" % job,
            "synctex": real + "\nSyncTeX written on %s.synctex.gz.\n"
                       "Transcript written on %s.log.\n" % (job, job),
            "errforge": "! Undefined control sequence.\n" + real
                        + "\nTranscript written on %s.log.\n" % job}[mode]
    sys.stdout.write(banner + term); rcline(0)
elif mode == "infraforge":
    # C-99 review round 3 (c): the document \message'd a lookalike of an
    # "infrastructure" error, then failed genuinely (halt, no PDF). Its
    # forged line is the log's FIRST "!" line, on the terminal too.
    cwd = a[a.index("-w") + 1]
    job = a[-1].rsplit("/", 1)[-1].rpartition(".")[0]
    body = (banner + "! Package pdftex.def Error: File `x-eps-converted-to.pdf' "
            "not found: using draft setting.\n! Undefined control sequence.\n"
            "l.6 \\undefinedcs\n!  ==> Fatal error occurred, no output PDF "
            "file produced!\n")
    open(os.path.join(cwd, job + ".log"), "w").write(body)
    sys.stdout.write(body + "Transcript written on %s.log.\n" % job); rcline(1)
elif mode in ("okpdf", "nopages", "forge"):
    # okpdf: pdfTeX ships a page (writes <job>.pdf, reports it in <job>.log);
    # nopages: rc 0, "No pages of output." (aux oscillation, C-95);
    # forge: the DOCUMENT wrote <job>.pdf itself (\openout), pdfTeX shipped
    # no page (C-97 review round 2). The job name as pdfTeX forms it:
    # quotes removed, directory dropped, the LAST extension stripped.
    cwd = a[a.index("-w") + 1]
    name = a[-1].replace('"', "").rsplit("/", 1)[-1]
    job = name.rpartition(".")[0] if "." in name else name
    final = ("Output written on %s.pdf (1 page, 999 bytes)." % job
             if mode == "okpdf" else "No pages of output.")
    if mode != "nopages":
        open(os.path.join(cwd, job + ".pdf"), "w").write("%PDF-1.5 x\n")
    open(os.path.join(cwd, job + ".log"), "w").write(
        banner + "Output written on %s.pdf (1 page, 9 bytes).\n" % job  # forged
        + final + "\nPDF statistics:\n 3 PDF objects out of 1000\n\n")
    sys.stdout.write(banner + final + "\n"); rcline(0)
'''

# A fake ENGINE for the shell grader's run_pdflatex: modes as above, stdout only.
FAKE_ENGINE = r'''#!/bin/bash
n=$(( $(cat "$FAKE_COUNT" 2>/dev/null || echo 0) + 1 )); echo $n > "$FAKE_COUNT"
IFS=, read -ra plan <<<"$FAKE_PLAN"
i=$(( n - 1 )); [ $i -ge ${#plan[@]} ] && i=$(( ${#plan[@]} - 1 ))
case "${plan[$i]}" in
  ok)   echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"; exit 0 ;;
  fail) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"; echo "! Undefined"; exit 1 ;;
  dead) echo "$DEAD_MSG" >&2; exit 1 ;;
  fwrite) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
          echo "!pdfTeX error: pdflatex (file t.pdf): fwrite() failed"; exit 1 ;;
  openout) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
          echo "! I can't write on file \`../x.tex'."; exit 1 ;;
  batchforge)    # C-99: a forged terminal report, pdfTeX's real one silenced
    echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
    j="${!#}"; j="${j%.*}"; echo x > "$j.pdf"
    echo "Output written on $j.pdf (1 page, 9 bytes)."; echo "Transcript written on $j.log."
    printf 'This is pdfTeX\nNo pages of output.\nPDF statistics:\n 3 objects\n' > "$j.log"
    exit 0 ;;
  okpdf|forge)   # okpdf: pdfTeX ships a page; forge: the document wrote t.pdf
    echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
    j="${!#}"; j="${j%.*}"; echo x > "$j.pdf"
    if [ "${plan[$i]}" = okpdf ]; then f="Output written on $j.pdf (1 page, 9 bytes)."
    else f="No pages of output."; fi
    printf 'This is pdfTeX\nOutput written on %s.pdf (1 page, 1 bytes).\n%s\nPDF statistics:\n 3 objects\n' "$j" "$f" > "$j.log"
    exit 0 ;;
  *)    exit 1 ;;
esac
'''


# Host variables kpathsea reads although no oracle code names them: the
# `VAR_progname` / `VAR.progname` forms of a configuration key, shell_escape,
# the configuration and format search paths. MEASURED by the round-4 review:
# on the native backend `openout_any_pdflatex=a` flipped a grade and
# `shell_escape=t` turned \write18 on, while the old checks (which named only
# the `_ENV_FORWARD` variables) passed. The checks below do not enumerate what
# must NOT reach the engine; they assert what MAY (an allow-list), so a
# variable nobody thought of fails them too.
KPATHSEA_HOSTILE = {"openout_any_pdflatex": "a", "openin_any_pdflatex": "a",
                    "openout_any.pdflatex": "a", "shell_escape": "t",
                    "shell_escape_pdflatex": "t", "TEXMFCNF": "/nonexistent/cnf",
                    "TEXFORMATS": "/nonexistent/fmt", "SOURCE_DATE_EPOCH.pdflatex": "5"}
# What /bin/sh adds to the environment of the fake engine's own shell.
_SH_OWN = {"PWD", "OLDPWD", "SHLVL", "_"}


# The native backend runs `python3 -I -c SUPERVISOR NONCE NAMES ENGINE ARGS`
# (C-99). The gate is pure and the host may have no inotify: a fake python3
# on the fake PATH runs the engine and reports clean evidence.
FAKE_SUPERVISOR = """#!/bin/sh
shift 3
n=$1; shift 2
"$@"; rc=$?
printf '\\n%s_EVID={"alias": [], "cw": {}, "err": "", "overflow": 0}\\n' "$n" >&2
exit $rc
"""


def fake_supervisor(bindir: Path) -> None:
    f = Path(bindir) / "python3"
    f.write_text(FAKE_SUPERVISOR)
    f.chmod(0o755)


# ONLY THE ORACLE NAMES AN ENGINE'S OUTPUTS (C-95/C-99, review round 3, M2).
# Inverted from a pattern list (which the review evaded 4 ways: `stem+'.pdf'`
# without spaces, `with_suffix('.pdf')` in single quotes, `rsplit`, a shell
# `${base%.*}.pdf`) to an allow-list: in EVERY tracked file that is an oracle
# client -- a Python module importing _oracle, or importing (transitively) a
# module that does; a shell script sourcing _oracle.sh or running _oracle.py
# -- an engine-output extension (.pdf .log .fls .aux) may appear ONLY
#   * as the extension argument of `job_output(...)` (Python), or right after
#     `$job`/`${job}`, the name `oracle_job` returned (shell); or
#   * on a line of OUTPUT_NAME_ALLOW below, each with the reason it is not a
#     run's evidence.
# Docstrings and comments are not code and are skipped. And each GRADER must
# take its PDF verdict from the oracle (OracleRun.pdf/.compiles, whose only
# source is _oracle.pdf_written, or pdf_written/oracle_pdf_written itself):
# PDF_VERDICT_SOURCE below. Not closed against deliberate obfuscation (".p" +
# "df"); it closes the shapes a maintainer writes by accident.
_EXT = re.compile(r"\.(pdf|log|fls|aux)\b", re.I)
ORACLE_API_FILES = {
    "scripts/tools/_oracle.py": "the oracle itself",
    "scripts/tools/_oracle.sh": "the oracle's shell helpers",
    "scripts/tools/check_oracle_infra_grading.py": "this gate: fakes and fixtures",
    "scripts/tools/check_oracle_pin.py": "a gate: engine-call fixtures",
    "scripts/tools/check_oracle_forgery.py": "a gate: forgery fixtures (TeX source)",
    "scripts/tools/check_gen_contract_parsers.py": "a gate: recorded log fixtures",
    "scripts/tools/check_gate_selftests.py": "the kill-test harness",
}
# (file, the stripped source line): why the literal is not a run's evidence
OUTPUT_NAME_ALLOW = {
    ("scripts/tools/gen_contract.py", '_NOT_JOB_WRITTEN = {".tex", ".log", ".fls", ".pdf"}'):
        "extensions EXCLUDED from the job-written set, not a name read",
    ("scripts/tools/gen_contract.py", '"lazy_files": "first-run .fls INPUT files minus those of the same "'):
        "prose in a recorded field",
    ("scripts/tools/check_oracle_equivalence.py", "INNER = r\'\'\'"):
        "the in-image driver's source, which itself calls job_output",
}
PDF_VERDICT_SOURCE = {
    "scripts/tools/diff_real_roots.py": r"\brun\.pdf\b",
    "scripts/tools/gen_apply_fixes_real_differential.py": r"\brun1\.compiles\b",
    "scripts/tools/gen_strict_battery.py": r"\brun\.pdf\b",
    "scripts/tools/_strict_s0.py": r"\br\.pdf\b",
    "scripts/tools/check_oracle_equivalence.py": r"\bra\.pdf\b",
    "scripts/tools/oracle_baseline_classify.py": r"\brun\.pdf\b",
    "scripts/tools/regrade_sample.py": r"\br\.pdf\b",
    "scripts/tools/audit_fix_meaning.py": r"\brun\.compiles\b",
    "scripts/tools/confirm_fix_policy.py": r"\brun\.compiles\b",
    "scripts/tools/check_apply_fixes_roundtrip.py": r"\brun\.compiles\b",
    "scripts/tools/gen_contract.py": r"_oracle\.pdf_written\(",
    "scripts/tools/false_ready_oracle.sh": r"\boracle_pdf_written \"",
    "scripts/tools/diff_compile_check.sh": r"\boracle_pdf_written \"",
}


def _tracked(repo: Path) -> list[str]:
    try:
        out = subprocess.run(["git", "-C", str(repo), "ls-files"], capture_output=True,
                             text=True, timeout=60)
        if out.returncode == 0 and out.stdout.strip():
            return out.stdout.split("\n")
    except (OSError, subprocess.TimeoutExpired):
        pass
    return [str(q.relative_to(repo)) for q in repo.rglob("*")
            if q.is_file() and ".git" not in q.parts]


def oracle_clients(repo: Path) -> tuple[set, set]:
    files = [f for f in _tracked(repo) if f]
    py = {f: (repo / f).read_text(errors="replace") for f in files
          if f.endswith(".py") and (repo / f).is_file()}
    sh = {f: (repo / f).read_text(errors="replace") for f in files
          if f.endswith((".sh", ".bash")) and (repo / f).is_file()}

    def imports(text, mod):
        return re.search(rf"^\s*(import\s+{re.escape(mod)}\b|from\s+{re.escape(mod)}\s+import\b)",
                         text, re.M)
    clients = {f for f, t in py.items() if imports(t, "_oracle")}
    grew = True
    while grew:
        grew = False
        mods = {Path(f).stem for f in clients}
        for f, t in py.items():
            if f not in clients and any(imports(t, m) for m in mods):
                clients.add(f)
                grew = True
    shc = {f for f, t in sh.items() if "_oracle.sh" in t or "_oracle.py" in t}
    return clients, shc


def output_names_findings(repo: Path) -> list[str]:
    import ast
    clients, shc = oracle_clients(repo)
    hits = []
    used = set()
    for f in sorted(clients | shc):
        if f in ORACLE_API_FILES:
            continue
        text = (repo / f).read_text(errors="replace")
        lines = text.splitlines()
        if f in clients:
            tree = ast.parse(text)
            skip = set()
            for n in ast.walk(tree):
                if isinstance(n, (ast.Module, ast.ClassDef, ast.FunctionDef,
                                  ast.AsyncFunctionDef)) and n.body:
                    b = n.body[0]
                    if isinstance(b, ast.Expr) and isinstance(b.value, ast.Constant):
                        skip.add(id(b.value))
                if isinstance(n, ast.Call):
                    fn = n.func
                    name = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", "")
                    if name == "job_output" and len(n.args) == 3:
                        skip.add(id(n.args[2]))
            for n in ast.walk(tree):
                if (isinstance(n, ast.Constant) and isinstance(n.value, (str, bytes))
                        and id(n) not in skip):
                    v = n.value if isinstance(n.value, str) else n.value.decode("latin-1")
                    line = lines[n.lineno - 1].strip()
                    if _EXT.search(v):
                        if (f, line) in OUTPUT_NAME_ALLOW:
                            used.add((f, line))
                        else:
                            hits.append(f"{f}:{n.lineno}: {line[:90]}")
        else:
            for k, ln in enumerate(lines, 1):
                if ln.lstrip().startswith("#"):
                    continue
                code = re.sub(r"\$\{?job\}?\.(pdf|log|fls|aux)\b", "", ln)
                if _EXT.search(code):
                    if (f, ln.strip()) in OUTPUT_NAME_ALLOW:
                        used.add((f, ln.strip()))
                    else:
                        hits.append(f"{f}:{k}: {ln.strip()[:90]}")
    # A STALE allow-list entry is itself a finding (review round 4): it
    # would silently re-admit the same literal if it came back.
    for f, line in sorted(set(OUTPUT_NAME_ALLOW) - used):
        hits.append(f"{f}: OUTPUT_NAME_ALLOW entry matches no line: {line[:80]}")
    for f, rx in PDF_VERDICT_SOURCE.items():
        t = (repo / f).read_text(errors="replace") if (repo / f).is_file() else ""
        if not re.search(rx, t):
            hits.append(f"{f}: takes no PDF verdict from the oracle ({rx})")
    return sorted(set(hits))


def not_allowed(got: dict, tex_keys) -> list[str]:
    """Keys of an engine's environment that are neither the image's own
    (IMAGE_ENV, with its values) nor one of the run's TeX variables."""
    bad = [k for k in got if k not in _SH_OWN and k not in tex_keys
           and k not in _oracle.IMAGE_ENV]
    bad += [f"{k}={got[k]!r}" for k in _oracle.IMAGE_ENV
            if k in got and k != "PATH" and got[k] != _oracle.IMAGE_ENV[k]]
    return sorted(bad)


class Checker:
    def __init__(self, repo: Path, td: Path):
        self.repo, self.td = repo, td
        self.failures: list[str] = []
        self.n = 0
        self.fake = td / "fake-docker"
        self.fake.write_text(FAKE_DOCKER)
        self.fake.chmod(0o755)
        self.count = td / "count"
        self.workroot = (td / "work").resolve()
        self.workroot.mkdir()
        # The file arguments the fakes run must exist (check_file_argument, M1).
        # (t.TEX and t.Tex too: CI's file system is case-SENSITIVE, a Mac's
        # is not, so on a Mac they are t.tex itself.)
        for f in ("t.tex", "t.ltx", "a.b.tex", "x.tex", "t.TEX", "t.Tex"):
            (self.workroot / f).write_text("\\relax\n")
        os.environ["DEAD_MSG"] = DEAD_MSG
        os.environ["FAKE_COUNT"] = str(self.count)

    def expect(self, label: str, ok: bool, detail: str = "") -> None:
        self.n += 1
        if not ok:
            self.failures.append(f"{label}{': ' + detail if detail else ''}")

    def oracle(self, plan: str):
        """A ContainerOracle wired to the fake docker, without the docker
        handshake of __init__ (nothing here may need a daemon)."""
        self.count.unlink(missing_ok=True)
        os.environ["FAKE_PLAN"] = plan
        o = _oracle.ContainerOracle.__new__(_oracle.ContainerOracle)
        _oracle._Base.__init__(o)
        o.docker, o.workroot, o.name = str(self.fake), self.workroot, "lp-oracle-fake"
        _oracle._ORACLE = o
        # The session's full state scan is tested on its own (argv_and_state);
        # here the fake stands for a container already scanned.
        _oracle._STATE_CHECKED = True
        return o

    def tv(self) -> dict:
        """A graded run's private TEXMFHOME/TEXMFVAR (required since C-91)
        with the protocol's variables: what tex_env gives a grader."""
        return _oracle.oracle_tex_vars(self.workroot / "tx")

    def run_pdflatex(self, plan: str):
        o = self.oracle(plan)
        try:
            return o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                                  self.tv(), 60), None
        except _oracle.OracleError as e:
            return None, e

    # ---------------------------------------------------------------- python
    def python_graders(self) -> None:
        for mode in ("dead", "daemonerr", "cut", "nobanner", "leak"):
            got, err = self.run_pdflatex(mode)
            self.expect(f"ContainerOracle.run_pdflatex grades a '{mode}' run "
                        f"(no proof pdfTeX ran) instead of raising OracleError",
                        err is not None, f"returned {got!r}")
        got, err = self.run_pdflatex("fail")
        self.expect("a GENUINE pdfTeX failure (banner, in-container rc 1) is no "
                    "longer graded rc 1", err is None and got is not None
                    and got[0] == 1 and got[2] is False, f"{got!r} {err!r}")
        got, err = self.run_pdflatex("ok")
        self.expect("a genuine pdfTeX success is not graded rc 0",
                    err is None and got is not None and got[0] == 0, f"{got!r} {err!r}")
        got, err = self.run_pdflatex("timeout")
        self.expect("an in-container timeout (rc 124) is not reported as timed out",
                    err is None and got is not None and got[2] is True, f"{got!r} {err!r}")

        # OPEN-118 review round 3: proof pdfTeX ran is not proof its rc is the
        # document's. pdfTeX failing to write its OWN output (the measured
        # disk-full shape) is refused; the document's own \openout refusal is
        # still a grade.
        for mode in ("fwrite", "cantlog"):
            got, err = self.run_pdflatex(mode)
            self.expect(f"ContainerOracle.run_pdflatex grades a '{mode}' run "
                        f"(pdfTeX could not write its own output: disk full) "
                        f"instead of raising OracleError", err is not None,
                        f"returned {got!r}")
        got, err = self.run_pdflatex("openout")
        self.expect("a document's own \\openout refused under openout_any=p "
                    "(banner, rc 1) is no longer graded rc 1",
                    err is None and got is not None and got[0] == 1,
                    f"{got!r} {err!r}")
        # The free-space floor, BEFORE the run: nothing may even start.
        saved = os.environ.get("LP_ORACLE_MIN_FREE_MB")
        os.environ["LP_ORACLE_MIN_FREE_MB"] = str(10 ** 12)
        try:
            got, err = self.run_pdflatex("ok")
            self.expect("ContainerOracle.run_pdflatex runs (and grades) with "
                        "the work root below the free-space floor",
                        err is not None and not self.count.exists(),
                        f"returned {got!r}, engine started: {self.count.exists()}")
        finally:
            if saved is None:
                os.environ.pop("LP_ORACLE_MIN_FREE_MB", None)
            else:
                os.environ["LP_ORACLE_MIN_FREE_MB"] = saved
        # ... and AFTER it: space that runs out DURING a run.
        real_free = _oracle._free_bytes
        seq = iter([10 ** 15, 0])
        _oracle._free_bytes = lambda _d: next(seq, 0)
        try:
            got, err = self.run_pdflatex("ok")
            self.expect("ContainerOracle.run_pdflatex grades a run after which "
                        "the work root is below the free-space floor",
                        err is not None, f"returned {got!r}")
        finally:
            _oracle._free_bytes = real_free

        # The multi-pass protocol: pass 1 a real failure, pass 2 the daemon lost.
        for plan in ("fail,dead", "ok,dead", "dead"):
            o = self.oracle(plan)
            try:
                r = o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
                self.expect(f"run_to_fixpoint graded plan '{plan}' (a pass with "
                            f"no proof pdfTeX ran) as {r!r}", False)
            except _oracle.OracleError:
                self.expect("-", True)

        # C-95: each pass's evidence is its own. Pass 1 ships a page, the
        # confirming pass exits 0 with "No pages of output." -- the PDF on
        # disk is pass 1's, and must not make the run `compiles`. Also a PDF
        # left in the work directory by an EARLIER run (gen_apply_fixes_real's
        # run1 reuses run0's directory) must not count for a later one.
        # C-97 review round 2: pdfTeX's job name is the ONE name for clearing
        # and reading, whatever the extension (doc.TEX -> doc.pdf), and the
        # PDF verdict is pdfTeX's own report: a document-written .pdf is not.
        for top in ("t.TEX", "t.ltx", "a.b.tex", "t.Tex"):
            for plan, want in (("okpdf", True), ("okpdf,nopages", False),
                               ("forge", False), ("okpdf,forge", False)):
                o = self.oracle(plan)
                try:
                    r = o.run_to_fixpoint(self.workroot, top, self.tv(), 60)
                    got = r.compiles
                except _oracle.OracleError as e:
                    got = f"OracleError {e}"
                self.expect(f"run_to_fixpoint of {top!r} under plan '{plan}' graded "
                            f"compiles={got}, expected {want} (pdfTeX's job name / "
                            f"its own PDF report, C-95/C-97)", got is want)
                for f in self.workroot.iterdir():
                    if f.suffix in (".pdf", ".log") :
                        f.unlink()
        # MEASURED in the pinned image, for every argument shape the oracle
        # ACCEPTS (check_file_argument refuses the rest, below).
        measured = {"a.b.tex": "a.b", "doc.ltx": "doc", "doc.TEX": "doc",
                    "Doc.TeX": "Doc", "d/in.tex": "in", "sub.dir.x.tex": "sub.dir.x",
                    "doc.tex.tex": "doc.tex", "doc.pdf.tex": "doc.pdf"}
        got = {k: _oracle.pdftex_jobname(k) for k in measured}
        self.expect("pdftex_jobname no longer gives pdfTeX's MEASURED job names",
                    got == measured, repr({k: v for k, v in got.items() if v != measured[k]}))
        for plan, pre in (("okpdf,nopages", False), ("nopages", True)):
            stale = self.workroot / "t.pdf"
            stale.unlink(missing_ok=True)
            if pre:
                stale.write_text("%PDF-1.5 stale\n")
            o = self.oracle(plan)
            try:
                r = o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
                self.expect(f"run_to_fixpoint graded plan '{plan}'"
                            f"{' after a stale PDF' if pre else ''} as compiling "
                            f"although its confirming pass wrote no PDF (a stale "
                            f"PDF was read as this pass's, C-95)",
                            not r.compiles and r.pdf is False, repr(r))
            except _oracle.OracleError as e:
                self.expect(f"run_to_fixpoint refused plan '{plan}'", False, str(e))
            stale.unlink(missing_ok=True)
        # The same defect in the pass loops OUTSIDE run_to_fixpoint (review of
        # C-95): false_ready_oracle.sh runs its passes through the shim, and
        # gen_contract.py through run_engine. Each is one call of the shared
        # primitive, which must clear the job's .pdf/.log/.fls/.fmt first.
        outs = [self.workroot / ("t" + e) for e in (".pdf", ".log", ".fls", ".fmt")]
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for f in outs:
                f.write_text("stale\n")
            self.oracle("nopages")
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                          "-interaction=nonstopmode", "t.tex"])
            left = [f.name for f in outs if f.exists() and f.read_text() == "stale\n"]
            self.expect(f"the _oracle.py pdflatex shim left an earlier run's "
                        f"{left} in place for a run that wrote none (a stale PDF "
                        f"read as this pass's, C-95; false_ready_oracle.sh)",
                        rc == 0 and not left, f"rc {rc}")
        finally:
            os.chdir(cwd)
        for f in outs:
            f.write_text("stale\n")
        try:
            self.oracle("timeout").run_engine(
                self.workroot, _oracle.ENGINE_PDFLATEX,
                ["-interaction=nonstopmode", "t.tex"], self.tv(), 60)
            left = [f.name for f in outs if f.exists() and f.read_text() == "stale\n"]
            self.expect(f"run_engine left an earlier run's {left} in place for a "
                        f"run that wrote none (gen_contract.py read them, C-95)",
                        not left)
        except _oracle.OracleError as e:
            self.expect("run_engine refused a protocol run", False, str(e))
        for f in outs:
            f.unlink(missing_ok=True)
        _oracle._ORACLE = None

        self.review3_checks()

        # check_apply_fixes_roundtrip.pdflatex_ok: None (not graded), never False.
        import check_apply_fixes_roundtrip as rt
        for plan, want in (("dead", None), ("fail", False), ("cut", None),
                           ("fwrite", None), ("cantlog", None)):
            self.oracle(plan)
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            self.expect(f"check_apply_fixes_roundtrip.pdflatex_ok under '{plan}' "
                        f"returned {got!r}, expected {want!r}", got is want)

        # The shim: every oracle failure AND every other exception -> INFRA_RC.
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for plan in ("dead", "cut", "nobanner", "fwrite"):
                self.oracle(plan)
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
                self.expect(f"the _oracle.py shim exits {rc} under '{plan}', not "
                            f"INFRA_RC={_oracle.INFRA_RC}", rc == _oracle.INFRA_RC)
            o = self.oracle("ok")

            def boom(*_a, **_k):
                raise ValueError("an unexpected bug in the oracle")
            o.run_pdflatex = boom
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "-interaction=nonstopmode", "t.tex"])
            self.expect(f"the shim exits {rc} on a non-OracleError exception, not "
                        f"INFRA_RC={_oracle.INFRA_RC} (1 would read as 'pdflatex "
                        f"failed')", rc == _oracle.INFRA_RC)
            self.oracle("fail")
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "-interaction=nonstopmode", "t.tex"])
            self.expect(f"the shim exits {rc} on a genuine pdfTeX failure, not 1", rc == 1)
        finally:
            os.chdir(cwd)
            _oracle._ORACLE = None

    # ---------------------------------------- review round 3 (C-99, M1, stdin)
    def review3_checks(self) -> None:
        """C-99: the document must not write any file the oracle reads as
        evidence (the supervisor's close-write counts), and the PDF verdict
        needs pdfTeX's own final report in the terminal AND the log, which
        must agree. M1: the file argument is one the oracle can name exactly.
        stdin: no engine run inherits the grader's stdin."""
        wr = self.workroot
        # (1) the supervisor saw the document write pdfTeX's own log/pdf twice
        for evid, what in (('{"alias": [], "cw": {"t.log": 2}, "err": "", "overflow": 0}', "its own log"),
                           ('{"alias": [], "cw": {"t.pdf": 2}, "err": "", "overflow": 0}', "its own pdf"),
                           ('{"alias": [], "cw": {}, "err": "OSError(38)", "overflow": 0}', "no inotify"),
                           ('{"alias": [], "cw": {}, "err": "", "overflow": 1}', "a queue overflow"),
                           ('{"alias": [["T.LOG", "t.log"]], "cw": {"t.log": 1}, "err": "", '
                            '"overflow": 0}', "an alias of its own log (case-insensitive root)"),
                           ('{"cw": {}, "err": "", "overflow": 0}', "no alias list"),
                           ("OMIT", "no evidence line at all"),
                           ("NOT-JSON", "an unreadable evidence line")):
            os.environ["FAKE_EVID"] = evid
            try:
                got, err = self.run_pdflatex("okpdf")
            finally:
                os.environ.pop("FAKE_EVID", None)
            self.expect(f"run_pdflatex graded a run whose supervisor reported "
                        f"{what} (C-99: the evidence is the document's)",
                        err is not None, f"returned {got!r}")
        # (2) the terminal and the log must agree; text after the report
        for plan, what in (("batchforge", "a forged terminal report and a "
                                          "silenced real one (\\batchmode)"),
                           ("termtail", "text after the terminal's final report"),
                           ("termonly", "a terminal report and a log with none")):
            o = self.oracle(plan)
            try:
                r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
                self.expect(f"run_to_fixpoint graded {what} as {r!r} (C-99)", False)
            except _oracle.OracleError:
                self.expect("-", True)
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
        # \synctex=1: pdfTeX's own SyncTeX line follows its terminal report
        o = self.oracle("synctex")
        try:
            r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
            self.expect(f"a \\synctex=1 document that ships a page no longer grades "
                        f"compiles: {r!r} (review round 4)", r.compiles)
        except _oracle.OracleError as e:
            self.expect("a \\synctex=1 document that ships a page was REFUSED "
                        "(review round 4: 9 frame papers)", False, str(e)[:200])
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
        # a batchmode document: no terminal report, the (supervised) log decides
        o = self.oracle("batchok")
        r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
        self.expect(f"a \\batchmode document that ships a page no longer grades "
                    f"compiles (the log alone decides): {r!r}", r.compiles)
        # a forged first-error line changes no verdict (the reason field is
        # document-influenceable; nothing that decides compiles reads it)
        o = self.oracle("errforge")
        r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
        self.expect(f"a document printing a forged '! ...' error line changed "
                    f"the verdict: {r!r}", r.compiles and r.rc == 0)
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
        # ... nor a CELL (review round 3 (c)): a READY document that fails
        # after printing an "infrastructure" lookalike is FALSE-READY, not
        # ungraded (the real grader, diff_real_roots.run_one, end to end).
        import diff_real_roots
        corp = self.td / "corpus-infraforge"
        (corp / "p").mkdir(parents=True, exist_ok=True)
        (corp / "p" / "t.tex").write_text("\\relax\n")
        cli = self.td / "fake-cli-ready"
        cli.write_text("#!/bin/sh\nexit 0\n")
        cli.chmod(0o755)
        self.oracle("infraforge")
        try:
            row = diff_real_roots.run_one({"arxiv_id": "p", "toplevel": "t.tex"},
                                          corp, cli, 60)
            self.expect(f"a document that printed a forged infrastructure error and "
                        f"then failed was scored {row.get('cell')!r}, not "
                        f"'FALSE-READY' (a cell decided from document text, C-99)",
                        row.get("cell") == "FALSE-READY", repr(row)[:300])
        except _oracle.OracleError as e:
            self.expect("the infraforge run was refused instead of graded", False, str(e))
        finally:
            _oracle._ORACLE = None
        # (3) the report parser: TeX's 79-byte wrap is ambiguous
        pre = b"x" * 79 + b"\n"   # a line of exactly 79 bytes, then print_nl
        long_job = "a" * 70
        long_line = b"Output written on " + long_job.encode() + b".pdf (1 page, 9 bytes)."
        for label, job, log, want in (
                ("a report after a 79-byte line", "t", b"This is pdfTeX\n" + pre
                 + b"Output written on t.pdf (1 page, 9 bytes).\nPDF statistics:\n 1 x\n",
                 ("pdf", 1)),
                ("a report wrapped at 79 bytes", long_job,
                 long_line[:79] + b"\n" + long_line[79:] + b"\nPDF statistics:\n", ("pdf", 1)),
                ("a forged report before the real one", "t",
                 b"Output written on t.pdf (1 page, 9 bytes).\nNo pages of output.\n"
                 b"PDF statistics:\n 0 x\n", ("none", 0)),
                ("a report naming another job", "t",
                 b"Output written on u.pdf (1 page, 9 bytes).\n", ("none", 0)),
                ("a fatal error", "t", b"!  ==> Fatal error occurred, no output PDF file "
                 b"produced!\n", ("none", 0)),
                ("text after the log's report", "t", b"Output written on t.pdf (1 page, "
                 b"9 bytes).\nPDF statistics:\n 1 x\nMORE\n", "OracleError")):
            try:
                got = _oracle.final_report(log, job, "log")
            except _oracle.OracleError as e:
                got = f"OracleError {e}"
            if want == "OracleError":
                self.expect(f"final_report on {label} = {got!r}, want a refusal",
                            str(got).startswith("OracleError"))
            else:
                self.expect(f"final_report on {label} = {got!r}, want {want!r}", got == want)
        # the terminal channel: pdfTeX's own post-report lines, and nothing else
        rep = b"Output written on t.pdf (1 page, 9 bytes)."
        syn = b"SyncTeX written on t.synctex.gz."
        tr = b"Transcript written on t.log."
        j48 = "a" * 48   # the SyncTeX line is then exactly 79 bytes (unwrapped)
        s48 = b"SyncTeX written on " + j48.encode() + b".synctex.gz."
        for label, job, term, ok in (
                ("the transcript line", "t", rep + b"\n" + tr + b"\n", True),
                ("SyncTeX then the transcript", "t", rep + b"\n" + syn + b"\n" + tr + b"\n", True),
                ("SyncTeX (uncompressed)", "t", rep + b"\nSyncTeX written on t.synctex.\n"
                 + tr + b"\n", True),
                ("a 79-byte SyncTeX line", j48, b"Output written on " + j48.encode()
                 + b".pdf (1 page, 9 bytes).\n" + s48 + b"\nTranscript written on "
                 + j48.encode() + b".log.\n", True),
                ("SyncTeX of another job", "t", rep + b"\nSyncTeX written on u.synctex.gz.\n"
                 + tr + b"\n", False),
                ("SyncTeX after the transcript", "t", rep + b"\n" + tr + b"\n" + syn + b"\n",
                 False),
                ("other text", "t", rep + b"\n" + syn + b"\nMORE\n" + tr + b"\n", False)):
            try:
                _oracle.final_report(term, job, "terminal")
                got = True
            except _oracle.OracleError:
                got = False
            self.expect(f"final_report on a terminal with {label}: accepted={got}, "
                        f"want {ok} (review round 4, \\synctex)", got == ok)
        # (4) M1: arguments the oracle cannot name exactly are refused
        (wr / "u.ltx").write_text("x")
        (wr / "u.ltx.tex").write_text("x")
        (wr / "real.tex").write_text("x")
        (wr / "lnk.tex").unlink(missing_ok=True)
        (wr / "lnk.tex").symlink_to("real.tex")
        (wr / "dir.tex").mkdir(exist_ok=True)
        for arg in ("a.b", "doc.", ".tex", "a%b.tex", "a~b.tex", "t.tex/", "missing.tex",
                    "lnk.tex", "dir.tex", "u.ltx", '"t.tex"', "t.txt", "sub//t.tex",
                    "./t.tex", "a#b.tex", "a$b.tex", "a{b}.tex", "été.tex"):
            try:
                _oracle.check_file_argument(arg, wr)
                self.expect(f"check_file_argument accepted {arg!r} (M1: the oracle "
                            f"cannot name its outputs exactly)", False)
            except _oracle.OracleError:
                self.expect("-", True)
        for arg in ("t.tex", "t.ltx", "a.b.tex", "real.tex"):
            try:
                _oracle.check_file_argument(arg, wr)
                self.expect("-", True)
            except _oracle.OracleError as e:
                self.expect(f"check_file_argument refused {arg!r}", False, str(e))
        # ... and on the RUN path (check_engine_argv), not only as a callable
        for arg in ("a%b.tex", "u.ltx", "missing.tex", "lnk.tex"):
            o = self.oracle("okpdf")
            try:
                r = o.run_pdflatex(wr, ["-interaction=nonstopmode", arg], self.tv(), 60)
                self.expect(f"run_pdflatex accepted file argument {arg!r} (M1)", False,
                            repr(r)[:100])
            except _oracle.OracleError:
                self.expect("-", True)
        for f in ("u.ltx", "u.ltx.tex", "real.tex", "lnk.tex"):
            (wr / f).unlink(missing_ok=True)
        (wr / "dir.tex").rmdir()
        self.supervisor_checks()
        self.host_diagnostic_checks()
        self.leak_check_checks()
        # (5) no engine run inherits the grader's stdin: the container's docker
        # client and the native supervisor both get /dev/null
        rfd, wfd = os.pipe()
        os.write(wfd, b"SECRET-STDIN\n")
        os.close(wfd)
        saved0 = os.dup(0)
        os.dup2(rfd, 0)
        os.close(rfd)
        try:
            got_stdin = self.td / "docker-stdin"
            os.environ["FAKE_STDIN"] = str(got_stdin)
            self.run_pdflatex("ok")
            os.environ.pop("FAKE_STDIN", None)
            self.expect("the docker client of an engine run read the grader's "
                        "stdin (stdin=DEVNULL)", got_stdin.exists()
                        and got_stdin.read_bytes() == b"", repr(
                            got_stdin.read_bytes()[:40] if got_stdin.exists() else None))
            bindir = self.td / "nbin-stdin"
            bindir.mkdir(exist_ok=True)
            dump = self.td / "native-stdin"
            eng = bindir / _oracle.ENGINE_PDFLATEX
            eng.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                           f"cat > '{dump}'\nexit 0\n")
            eng.chmod(0o755)
            fake_supervisor(bindir)
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            n.engine_base["PATH"] = f"{bindir}:/usr/bin:/bin"
            n.run_pdflatex(wr, ["-interaction=nonstopmode", "t.tex"], self.tv(), 60)
            self.expect("the native engine run read the grader's stdin "
                        "(stdin=DEVNULL)", dump.exists() and dump.read_bytes() == b"",
                        repr(dump.read_bytes()[:40] if dump.exists() else None))
        finally:
            os.environ.pop("FAKE_STDIN", None)
            os.dup2(saved0, 0)
            os.close(saved0)
            _oracle._ORACLE = None

    def supervisor_checks(self) -> None:
        """THE REAL SUPERVISOR (_SUPERVISOR_SRC), not the fake python3 the
        other checks use: on Linux (CI; the pinned image) it must count the
        evidence files' close-writes -- one is pdfTeX's, a second (directly
        or through a symlink) is the document's -- and give its child
        /dev/null; where inotify is missing (macOS) it must report that, and
        check_evidence must refuse the run (fail closed)."""
        d = self.td / "sup"
        d.mkdir(exist_ok=True)
        args = ["-interaction=nonstopmode", "t.tex"]

        def run(script: str):
            for f in d.iterdir():
                f.unlink()
            eng = d / "eng.sh"
            eng.write_text("#!/bin/sh\n" + script)
            eng.chmod(0o755)
            p = subprocess.run([sys.executable, "-I", "-c", _oracle._SUPERVISOR_SRC,
                                "NONCE", _oracle.evidence_names(args), str(eng)],
                               cwd=d, capture_output=True, input=b"SECRET-STDIN\n",
                               timeout=60)
            try:
                _oracle.check_evidence(p.stderr, "NONCE", args, "supervisor test")
                return "graded"
            except _oracle.OracleError as e:
                return f"refused: {str(e)[:120]}"
        if sys.platform.startswith("linux"):
            for label, script, want in (
                    ("pdfTeX writes its log once", "echo x > t.log\n", "graded"),
                    ("the document writes the log a second time",
                     "echo x > t.log\necho y >> t.log\n", "refused"),
                    ("the document writes the PDF pdfTeX also writes",
                     "echo x > t.pdf\necho y > t.pdf\necho z > t.log\n", "refused"),
                    ("the document writes the log through a symlink",
                     "echo x > t.log\nln -s t.log evil.txt\necho y > evil.txt\n",
                     "refused"),
                    # pdfTeX holds its log open (fd 3) while the document
                    # opens it twice writing nothing: the kernel MERGES the
                    # document's two adjacent close-writes, but pdfTeX's own
                    # (after its final report, an IN_MODIFY) stays apart.
                    ("the document opens the held-open log twice, writing nothing",
                     "exec 3>t.log\necho x >&3\n: >> t.log\n: >> t.log\n"
                     "echo z >&3\nexec 3>&-\n", "refused"),
                    ("pdfTeX alone, holding its log open", "exec 3>t.log\n"
                     "echo x >&3\necho z >&3\nexec 3>&-\n", "graded"),
                    ("the document writes other files freely",
                     "echo x > t.log\necho a > t.aux\necho b > t.aux\n", "graded"),
                    # ONE FILE, MANY NAMES (review round 4): the same inode
                    # under another name, and a case/Unicode variant (on a
                    # case-insensitive root, virtiofs over APFS, the SAME
                    # file; here a different one, refused all the same)
                    ("the document writes the log through a hard link",
                     "echo x > t.log\nln t.log hard.txt\necho y > hard.txt\n", "refused"),
                    ("the document writes a case variant of the log",
                     "echo x > t.log\necho y > T.LOG\n", "refused"),
                    ("the document writes a case variant of the PDF, pdfTeX none",
                     "echo x > t.log\necho y > T.pdf\n", "refused"),
                    ("the document renames a file onto the PDF",
                     "echo x > t.log\necho y > z.txt\nmv z.txt t.pdf\necho w > t.pdf\n",
                     "refused"),
                    # pdfTeX's -recorder writes pdflatex<pid>.fls and renames
                    # it, still open, to <job>.fls: ONE write of t.fls
                    ("pdfTeX's recorder renames its open .fls",
                     "exec 3>pdflatex99.fls\necho a >&3\nmv pdflatex99.fls t.fls\n"
                     "echo x > t.log\necho b >&3\nexec 3>&-\n", "graded")):
                got = run(script)
                self.expect(f"the real supervisor: {label}: got {got!r}, want {want!r} "
                            f"(C-99)", got.startswith(want))
            run("cat > stdin.got\necho x > t.log\n")
            got = (d / "stdin.got").read_bytes() if (d / "stdin.got").exists() else None
            self.expect("the real supervisor gave the engine the grader's stdin, not "
                        "/dev/null", got == b"", repr(got))
        else:
            got = run("echo x > t.log\n")
            self.expect(f"the real supervisor without inotify ({sys.platform}) was "
                        f"not refused: {got!r} (fail closed, C-99)",
                        got.startswith("refused"))

    def leak_check_checks(self) -> None:
        """THE IN-CONTAINER LEAK CHECK (C-97) runs as shell, here with a fake
        `ps` (one scripted listing per call) and an instant `sleep`: a leak
        is the SAME process (the same pid) still listed after
        LEAK_CONFIRM_S re-samples. A concurrent run's zombie that its
        supervisor reaps late is not a leak (review round 4 re-measure: it
        refused check_contracts_reproducible); a persistent zombie or orphan
        is, even when its command name is a glob pattern that matches a file
        in the working directory."""
        d = self.td / "leak"
        d.mkdir(exist_ok=True)
        (d / "ps").write_text('#!/bin/sh\nn=$(cat cnt 2>/dev/null || echo 0); '
                              'echo $((n+1)) > cnt\nsed -n "$((n+1))p" plan | tr "|" "\\n"\n')
        (d / "sleep").write_text("#!/bin/sh\nexit 0\n")
        for f in ("ps", "sleep"):
            (d / f).chmod(0o755)
        (d / "3096:p:Z").write_text("")   # `[pdflatex]` would glob to this
        z, o = " 3096 7 Z 5 [pdflatex]", " 55 1 S 9 gs -q"
        k = _oracle.LEAK_CONFIRM_S + 2
        for label, plan, leak in (
                ("a sibling's zombie reaped after 2 samples", [z, z] + [""] * k, False),
                ("a different zombie each sample", [" 1 7 Z 5 [pdflatex]",
                                                    " 2 7 Z 5 [pdflatex]", ""], False),
                ("a persistent zombie", [z] * k, True),
                ("a persistent orphan", [o] * k, True),
                ("a persistent orphan whose state letter alternates",
                 [" 777 1 R 9 gs -dBATCH", " 777 1 S 9 gs -dBATCH"] * k, True),
                ("an orphan that becomes a zombie of the same pid",
                 [" 55 1 S 9 gs -q"] + [" 55 1 Z 9 [gs]"] * k, True),
                ("nothing", [""], False)):
            (d / "plan").write_text("\n".join(plan) + "\n")
            (d / "cnt").unlink(missing_ok=True)
            p = subprocess.run(["sh", "-c", _oracle.LEAK_CHECK_SH + ' lp_leak N; echo "rc=$?"'],
                               cwd=d, capture_output=True, text=True, timeout=60,
                               env={**os.environ, "PATH": f"{d}:{os.environ['PATH']}"})
            got = "N_LEAK=" in p.stderr and "rc=1" in p.stdout
            self.expect(f"the container leak check on {label}: leak={got}, want "
                        f"{leak} (C-97)", got == leak, (p.stdout + p.stderr)[:200])
            if label == "a persistent zombie":
                # The pid alone is the identity, so a glob-expanded token
                # would still be detected; what globbing breaks is the
                # diagnostic, which must name the process ps listed.
                self.expect("the container leak check on a persistent zombie named "
                            "a glob-expanded process, not '3096:[pdflatex]:Z' (C-97)",
                            "N_LEAK=3096:[pdflatex]:Z" in p.stderr, p.stderr[:200])

    def host_diagnostic_checks(self) -> None:
        """HostDiagnostic (oracle_baseline_classify's host arm, never a
        grade) runs WITHOUT the evidence supervisor: the Mac hosting that TeX
        Live has no inotify, so supervising it refused every host run (review
        round 4). It still gives the engine /dev/null. And get_oracle() never
        hands out an unsupervised backend."""
        bindir = self.td / "hbin"
        bindir.mkdir(exist_ok=True)
        wr = self.td / "hwork"
        wr.mkdir(exist_ok=True)
        (wr / "t.tex").write_text("x")
        marker = self.td / "hdiag-supervisor-ran"
        dump = self.td / "hdiag-stdin"
        eng = bindir / _oracle.ENGINE_PDFLATEX
        eng.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                       f"cat > '{dump}'\necho x > t.pdf\n"
                       "printf 'Output written on t.pdf (1 page, 9 bytes).\\n"
                       "PDF statistics:\\n' > t.log\n"
                       "echo 'Output written on t.pdf (1 page, 9 bytes).'\nexit 0\n")
        eng.chmod(0o755)
        py = bindir / "python3"
        py.write_text(f"#!/bin/sh\ntouch '{marker}'\nexit 99\n")
        py.chmod(0o755)
        h = _oracle.HostDiagnostic.__new__(_oracle.HostDiagnostic)
        _oracle._Base.__init__(h)
        h.engine_base["PATH"] = f"{bindir}:/usr/bin:/bin"
        rfd, wfd = os.pipe()
        os.write(wfd, b"SECRET-STDIN\n")
        os.close(wfd)
        saved0 = os.dup(0)
        os.dup2(rfd, 0)
        os.close(rfd)
        try:
            with tempfile.TemporaryDirectory(prefix="hd-") as td:
                r = h.run_to_fixpoint(wr, "t.tex", _oracle.oracle_tex_env(Path(td)), 60)
            self.expect(f"HostDiagnostic graded a compiling fake run as {r!r}",
                        r.compiles)
        except _oracle.OracleError as e:
            self.expect("HostDiagnostic refused a host run (it needs no supervisor, "
                        "review round 4)", False, str(e)[:200])
        finally:
            os.dup2(saved0, 0)
            os.close(saved0)
        self.expect("HostDiagnostic ran the evidence supervisor", not marker.exists())
        self.expect("HostDiagnostic's engine read the grader's stdin (stdin=DEVNULL)",
                    dump.exists() and dump.read_bytes() == b"",
                    repr(dump.read_bytes()[:40] if dump.exists() else None))
        saved = _oracle._ORACLE
        _oracle._ORACLE = h
        try:
            _oracle.get_oracle(full_state=False)
            self.expect("get_oracle() handed out an unsupervised backend (C-99)", False)
        except _oracle.OracleError:
            self.expect("-", True)
        finally:
            _oracle._ORACLE = saved
        self.expect("a grading backend is unsupervised",
                    getattr(_oracle.NativeOracle, "supervised", False) is True
                    and getattr(_oracle.ContainerOracle, "supervised", False) is True)

    # ------------------------------------------------ the contract generator
    def generator_client(self) -> None:
        """gen_contract.py is a CLIENT of the oracle (run_engine), not a runner
        of its own: its jobs get the same proof-of-run refusals, the engine it
        names reaches the container, exactly the TeX variables it passes cross
        (on the native backend too: no host TeX variable leaks in), and an
        oracle failure stops the generator instead of reading as a TeX
        outcome."""
        tv = _oracle.oracle_tex_vars(self.workroot / "tx")
        for mode in ("dead", "daemonerr", "cut", "nobanner", "fwrite"):
            o = self.oracle(mode)
            try:
                got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX,
                                   ["-ini", "-jobname=t", "\\dump"], tv, 60)
                self.expect(f"run_engine returned {got!r} for a '{mode}' run "
                            f"instead of raising OracleError", False)
            except _oracle.OracleError:
                self.expect("-", True)
        argv_file = self.td / "argv"
        os.environ["FAKE_ARGV"] = str(argv_file)
        try:
            o = self.oracle("fail")
            got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini", "t.tex"],
                               dict(tv, FORCE_SOURCE_DATE="1"), 60)
            a = argv_file.read_text().split("\0")
            i = a.index("-c")
            fwd = sorted(a[j + 1] for j in range(len(a) - 1)
                         if a[j] == "-e" and j < i)
            want = sorted(["HOME=/tmp"] + [f"{k}={v}" for k, v in
                                           dict(tv, FORCE_SOURCE_DATE="1").items()])
            self.expect("run_engine: a genuine failure is rc 1, the engine reaches "
                        "the container after the nonce and timeout, and exactly "
                        "the caller's TeX variables are forwarded",
                        got[0] == 1 and a[i + 7] == _oracle.ENGINE_PDFTEX
                        and a[i + 5] == _oracle._SUPERVISOR_SRC
                        and a[i + 8:] == ["-ini", "t.tex"] and fwd == want,
                        f"{got!r} {a[i + 3:]} {fwd}")
            # Run the in-container script itself (a fake `timeout` that drops
            # its options, an engine path that proves it ran): the script must
            # start the engine it was GIVEN, not a name of its own.
            tb = self.td / "tbin"
            tb.mkdir(exist_ok=True)
            (tb / "timeout").write_text('#!/bin/sh\nshift 3\nexec "$@"\n')
            (tb / "timeout").chmod(0o755)
            # python3 -I -c SUPERVISOR NONCE NAMES ENGINE ARGS: run the engine
            (tb / "python3").write_text('#!/bin/sh\nshift 5\nexec "$@"\n')
            (tb / "python3").chmod(0o755)
            probe = tb / "given-engine"
            probe.write_text("#!/bin/sh\necho GIVEN-ENGINE-RAN \"$@\"\n")
            probe.chmod(0o755)
            # A fake `ps` (the container's procps columns): FAKE_PS lines.
            (tb / "ps").write_text('#!/bin/sh\nprintf "%b" "$FAKE_PS"\n')
            (tb / "ps").chmod(0o755)
            (tb / "sleep").write_text("#!/bin/sh\nexit 0\n")
            (tb / "sleep").chmod(0o755)
            clean_ps = ("    1     0 Ss     900 docker-init\\n"
                        "    7     1 S      900 sleep infinity\\n"
                        "   40     0 Ss       0 sh\\n")

            def script(ps_out):
                return subprocess.run(
                    ["sh", "-c", a[i + 1], "sh", "N", "60", "SUP", "x.log",
                     str(probe), "x.tex"],
                    capture_output=True, text=True,
                    env=dict(os.environ, PATH=f"{tb}:/usr/bin:/bin", FAKE_PS=ps_out))
            r = script(clean_ps)
            self.expect("the in-container script runs the engine run_engine names",
                        "GIVEN-ENGINE-RAN x.tex" in r.stdout and "N=0" in r.stderr,
                        f"{r.stdout!r} {r.stderr!r}")
            # C-97: a process left behind by an earlier run -- a zombie, or
            # an orphan reparented to PID 1 -- stops the run BEFORE the
            # engine starts; a young one (< 2 s, being reaped) does not.
            for label, extra, want_leak in (
                    ("a zombie", "  301   290 Z       40 gs\\n", True),
                    ("an orphan of PID 1", "  302     1 S       40 gs\\n", True),
                    ("an orphaned sleep", "  305     1 S       40 sleep 30\\n", True),
                    ("a zombie orphan", "  303     1 Z      600 perl\\n", True),
                    ("a process being reaped (<2 s)", "  304     1 Z        1 sh\\n", False)):
                r = script(clean_ps + extra)
                leaked = "N_LEAK=" in r.stderr and "GIVEN-ENGINE-RAN" not in r.stdout
                self.expect(f"the in-container script {'ran the engine despite' if want_leak else 'refused'} "
                            f"{label} left in the container (C-97)", leaked == want_leak,
                            f"{r.stdout!r} {r.stderr!r}")
        finally:
            os.environ.pop("FAKE_ARGV", None)
        # An engine the oracle does not run (named through _oracle's table,
        # not spelled here: check_oracle_pin scans this file).
        not_run = sorted(_oracle.TEX_ENGINE_BINARIES - set(_oracle.ENGINES))[0]
        for bad_engine, bad_vars in ((not_run, tv), (_oracle.ENGINE_PDFTEX,
                                                   dict(tv, PATH="/host/bin"))):
            o = self.oracle("ok")
            try:
                o.run_engine(self.workroot, bad_engine, ["t.tex"], bad_vars, 60)
                self.expect(f"run_engine accepted engine {bad_engine!r} with "
                            f"variables {sorted(bad_vars)}", False)
            except _oracle.OracleError:
                self.expect("-", True)
        try:
            self.oracle("ok").image_command([_oracle.ENGINE_PDFLATEX, "t.tex"])
            self.expect("image_command started a TeX engine", False)
        except _oracle.OracleError:
            self.expect("-", True)
        # Native backend: the host's TeX variables never cross into a
        # run_engine job; only the caller's do. A fake engine on PATH dumps
        # the environment it received.
        bindir = self.td / "bin"
        bindir.mkdir(exist_ok=True)
        fake = bindir / _oracle.ENGINE_PDFTEX
        envdump = self.td / "envdump"
        fake.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                        f"env > '{envdump}'\nexit 0\n")
        fake.chmod(0o755)
        hostile = dict(KPATHSEA_HOSTILE, openin_any="a", max_print_line="79")
        saved = {k: os.environ.get(k) for k in hostile}
        os.environ.update(hostile)
        try:
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            # The image's PATH, with the fake engine's directory in front
            # (the host's PATH never reaches an engine).
            n.engine_base["PATH"] = f"{bindir}:/usr/bin:/bin"
            fake_supervisor(bindir)
            rc, _, _ = n.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["t.tex"], tv, 60)
            got = dict(x.split("=", 1) for x in envdump.read_text().splitlines()
                       if "=" in x)
            leak = not_allowed(got, tv)
            self.expect("native run_engine: the caller's TeX variables and no host "
                        "TeX variable", rc == 0 and got.get("openin_any") == "p"
                        and not leak
                        and all(got.get(k) == v for k, v in tv.items()),
                        f"leaked {leak}")
        finally:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        # The generator itself: an oracle failure is never a TeX outcome.
        import gen_contract as gc
        o = self.oracle("dead")
        tex = gc.Tex(_oracle.IMAGE, oracle=o)
        try:
            tex.pdflatex(tex.job("x"), b"\\relax\n")
            self.expect("gen_contract.Tex.pdflatex returned a result for a "
                        "'dead' run", False)
        except SystemExit as e:
            self.expect("gen_contract.Tex.pdflatex: a 'dead' run is not reported "
                        "as INFRASTRUCTURE", "INFRASTRUCTURE" in str(e.code), str(e.code))
        finally:
            tex.close()
            _oracle._ORACLE = None

    # ------------------------------------------- the ONE grading environment
    def grading_env(self) -> None:
        """C-91 (OPEN-118 known limit (b)): every GRADED run gets exactly the
        protocol's TeX environment, whoever calls the oracle and whatever the
        host exports -- ORACLE_TEX_VARS imposed, a private TEXMFHOME/TEXMFVAR
        required, every other TeX-shaping variable dropped. Before, the shim
        forwarded the host's values (or none: no SOURCE_DATE_EPOCH, no
        openin_any/openout_any), the native shell path ran a bare pdflatex,
        and check_apply_fixes_roundtrip passed the host environment. Each
        entry point is driven here with a HOSTILE host environment and the
        variables that reach the engine are read back: from the fake docker's
        argv (container) and from a fake engine's environment (native)."""
        hostile = {"SOURCE_DATE_EPOCH": "1700000000", "openin_any": "a",
                   "openout_any": "a", "FORCE_SOURCE_DATE": "1",
                   "max_print_line": "1000", "TEXINPUTS": f"{self.workroot}/inp:",
                   # C-93: a caller's/host's temporary directories never reach
                   # the engine (TMPDIR itself: see host_tmp below)
                   "TMP": "/tmp", "TEMP": "/tmp",
                   "JAVA_TOOL_OPTIONS": "-XX:+UsePerfData",
                   **KPATHSEA_HOSTILE}
        host_tmp = {"TMPDIR": "/tmp"}
        want_fixed = dict(_oracle.ORACLE_TEX_VARS)
        argv_file = self.td / "argv-env"

        def forwarded() -> dict:
            a = argv_file.read_text().split("\0")
            i = a.index("-c")
            return dict(a[j + 1].split("=", 1) for j in range(len(a) - 1)
                        if a[j] == "-e" and j < i)

        def tmp_created() -> bool:
            f = Path(str(argv_file) + ".tmpdir")
            return f.exists() and f.read_text() == "1"

        def exactly_protocol(got: dict, texmf_host: str | None,
                             tmp_existed: bool) -> str:
            """'' when `got` is the protocol's environment, else what is wrong."""
            bad = []
            for k, v in want_fixed.items():
                if got.get(k) != v:
                    bad.append(f"{k}={got.get(k)!r} (protocol {v!r})")
            for k in ("FORCE_SOURCE_DATE", "max_print_line", "TEXINPUTS"):
                if k in got:
                    bad.append(f"host {k}={got[k]!r} reached the engine")
            for k in _oracle._GRADING_TEXMF:
                if not got.get(k) or got.get(k) == texmf_host:
                    bad.append(f"{k}={got.get(k)!r} is not a private per-run one")
            # C-93: the private temporary directory, beside the private
            # trees, created before the run; TMP/TEMP/java's derived from it.
            tv_dir = got.get("TEXMFVAR")
            want_tmp = (str(Path(tv_dir).parent / _oracle.PRIVATE_TMP_NAME)
                        if tv_dir else None)
            if not want_tmp or got.get("TMPDIR") != want_tmp:
                bad.append(f"TMPDIR={got.get('TMPDIR')!r} is not the run's private "
                           f"temporary directory {want_tmp!r}")
            elif not tmp_existed:
                bad.append(f"the run's private TMPDIR {want_tmp} was not created "
                           f"before the engine started")
            for k in ("TMP", "TEMP"):
                if got.get(k) != got.get("TMPDIR"):
                    bad.append(f"{k}={got.get(k)!r} is not the private TMPDIR")
            jto = got.get("JAVA_TOOL_OPTIONS", "")
            if ("-XX:-UsePerfData" not in jto.split()
                    or f"-Djava.io.tmpdir={got.get('TMPDIR')}" not in jto.split()
                    or "-XX:+UsePerfData" in jto):
                bad.append(f"JAVA_TOOL_OPTIONS={jto!r} does not keep java out of "
                           f"/tmp (-XX:-UsePerfData, java.io.tmpdir=TMPDIR)")
            leak = not_allowed(got, set(want_fixed) | set(_oracle._GRADING_TEXMF)
                               | {"TMPDIR", "TMP", "TEMP", "JAVA_TOOL_OPTIONS"})
            if leak:
                bad.append(f"not on the allow-list (image env + protocol): {leak}")
            return "; ".join(bad)

        saved = {k: os.environ.get(k) for k in list(hostile) + ["FAKE_ARGV",
                                                                  "TEXMFHOME", "TMPDIR"]}
        os.environ["FAKE_ARGV"] = str(argv_file)
        host_th = str(self.workroot / "host-th")
        try:
            # (1) the Python API: a caller dict carrying the hostile values.
            o = self.oracle("ok")
            try:
                o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                               dict(self.tv(), **hostile), 60)
                why = exactly_protocol(forwarded(), None, tmp_created())
            except _oracle.OracleError as e:
                why = f"the protocol's own run was refused: {e}"
            self.expect("ContainerOracle.run_pdflatex forwards a caller's TeX "
                        "variables instead of imposing the protocol's", not why, why)
            # (2) no private TEXMF: refused, not run in the shared TEXMFVAR.
            o = self.oracle("ok")
            try:
                o.run_pdflatex(self.workroot, ["t.tex"], dict(
                    want_fixed, **_oracle.private_tmp_vars(self.workroot / "tx")), 60)
                self.expect("run_pdflatex graded a run with no private "
                            "TEXMFHOME/TEXMFVAR (the container's persistent "
                            "TEXMFVAR would carry state)", False)
            except _oracle.OracleError:
                self.expect("-", True)
            # (2b) C-93: a caller's TMPDIR that is not the run's private one
            # (the host's /tmp: the long-lived container's shared /tmp, where
            # a killed repstopdf -> gs left /tmp/gs_*) is refused, not run.
            for bad_tmp in ("/tmp", None, str(self.workroot / "elsewhere")):
                env = dict(self.tv())
                if bad_tmp is None:
                    env.pop("TMPDIR", None)
                else:
                    env["TMPDIR"] = bad_tmp
                o = self.oracle("ok")
                try:
                    o.run_pdflatex(self.workroot, ["t.tex"], env, 60)
                    self.expect(f"run_pdflatex graded a run whose TMPDIR is "
                                f"{bad_tmp!r}, not its private one (C-93)", False)
                except _oracle.OracleError:
                    self.expect("-", True)
            # (2c) the per-run environment itself carries the private TMPDIR.
            self.expect("oracle_tex_vars carries no private TMPDIR/TMP/TEMP/"
                        "JAVA_TOOL_OPTIONS (C-93)",
                        {k: self.tv().get(k) for k in ("TMPDIR", "TMP", "TEMP")}
                        == dict.fromkeys(("TMPDIR", "TMP", "TEMP"),
                                         str(self.workroot / "tx"
                                             / _oracle.PRIVATE_TMP_NAME))
                        and "-XX:-UsePerfData" in self.tv().get("JAVA_TOOL_OPTIONS", ""),
                        repr({k: self.tv().get(k) for k in _oracle._GRADING_TMP}))
            # (3) the shim, under a hostile HOST environment.
            os.environ.update(hostile, TEXMFHOME=host_th, **host_tmp)
            cwd = os.getcwd()
            os.chdir(self.workroot)
            try:
                self.oracle("ok")
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
            why = exactly_protocol(forwarded(), host_th, tmp_created()) if rc == 0 else f"rc {rc}"
            self.expect("the _oracle.py pdflatex shim (the shell graders' path) "
                        "does not give its run the protocol's environment", not why,
                        why)
            # (4) the shim on the NATIVE backend (CI's tex-oracle job): a fake
            # engine on PATH dumps the environment it was started with.
            bindir = self.td / "nbin"
            bindir.mkdir(exist_ok=True)
            dump = self.td / "native-env"
            eng = bindir / _oracle.ENGINE_PDFLATEX
            eng.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                           f"env > '{dump}'\n"
                           f"if [ -d \"$TMPDIR\" ]; then echo 1; else echo 0; fi "
                           f"> '{dump}.tmpdir'\nexit 0\n")
            eng.chmod(0o755)
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            n.engine_base["PATH"] = f"{bindir}:/usr/bin:/bin"
            fake_supervisor(bindir)
            _oracle._ORACLE = n
            os.chdir(self.workroot)
            try:
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
            got = (dict(x.split("=", 1) for x in dump.read_text().splitlines()
                        if "=" in x) if dump.exists() else {})
            made = Path(f"{dump}.tmpdir")
            why = (exactly_protocol(got, host_th, made.exists()
                                    and made.read_text().strip() == "1")
                   if rc == 0 else f"rc {rc}")
            self.expect("the shim on the native backend does not give its run the "
                        "protocol's environment", not why, why)
            for k in hostile:
                os.environ.pop(k, None)
            os.environ.pop("TEXMFHOME", None)
            os.environ.pop("TMPDIR", None)
            # (5) check_apply_fixes_roundtrip.pdflatex_ok, a grader that
            # passed `dict(os.environ)` until C-91.
            import check_apply_fixes_roundtrip as rt
            self.oracle("ok")
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            why = exactly_protocol(forwarded(), None, tmp_created()) if got is not None else "not graded"
            self.expect("check_apply_fixes_roundtrip.pdflatex_ok does not grade "
                        "in the protocol's environment", not why, why)
        finally:
            _oracle._ORACLE = None
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        # (6a) the container backend's own environment is the image's: a
        # container started with an extra `-e` (under the oracle's name) would
        # give every exec that variable, so fingerprint() refuses it.
        import json as _json
        arch = sorted(_oracle.TREE_FINGERPRINTS)[0]
        fp = dict(_oracle.TREE_FINGERPRINTS[arch], arch=arch,
                  banner="pdfTeX " + _oracle.EXPECT_VERSION)
        for extra, want_ok in (({"HOSTNAME": "abc"}, True),
                               ({"HOSTNAME": "abc", "shell_escape": "t"}, False),
                               ({"TEXMFCNF": "/x"}, False)):
            os.environ["FAKE_FP"] = _json.dumps(fp)
            cenv = self.td / "container-env"
            cenv.write_text("\0".join(
                f"{k}={v}" for k, v in dict(_oracle.IMAGE_ENV, **extra).items()))
            os.environ["FAKE_CENV"] = str(cenv)
            o = self.oracle("ok")
            try:
                o.fingerprint()
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"ContainerOracle.fingerprint {'refused' if want_ok else 'accepted'} "
                        f"a container whose environment is the image's plus "
                        f"{sorted(extra)}", ok == want_ok)
        for k in ("FAKE_FP", "FAKE_CENV"):
            os.environ.pop(k, None)
        _oracle._ORACLE = None
        # (6) the shell side: on BOTH backends oracle_setup must route every
        # run through the shim (a bare engine ran on the native one).
        osh = self.repo / "scripts/tools/_oracle.sh"
        py = str(self.repo / "scripts/tools/_oracle.py")
        stub = ('python3() { case "$2" in assert-native) return 0 ;; '
                'version) echo "pdfTeX 3.141592653-2.6-1.40.29" ;; '
                f'workroot) echo "{self.td}/wr" ;; esac; }}; ')
        for backend, envset in (("native", {"LP_ORACLE_IN_IMAGE": "x"}),
                                ("container", {})):
            env = {k: v for k, v in os.environ.items() if k != "LP_ORACLE_IN_IMAGE"}
            env.update(envset, ROOT=str(self.repo), TEX_TIMEOUT="30")
            p = subprocess.run(
                ["bash", "-c", stub + f'source "{osh}"; oracle_setup t 1; '
                 'printf "%s\\n" "$ORACLE_BACKEND" "$ORACLE_TIMEOUT_INSIDE" '
                 '"${PDFLATEX[@]}"'], capture_output=True, text=True, env=env)
            got = p.stdout.split("\n")
            self.expect(f"_oracle.sh ({backend}) does not run every grader's "
                        f"pdflatex through the _oracle.py shim",
                        got[:6] == [backend, "1", "python3", py,
                                    _oracle.SHIM_COMMAND, "--timeout"],
                        repr(got[:6]) + p.stderr[-200:])
        # (7) image_command (gen_contract.py's non-TeX commands) starts no
        # engine by any route: an engine as an argument another program runs,
        # a format selector, a shell that could run anything.
        eng = sorted(_oracle.TEX_ENGINE_BINARIES)
        for argv in (["xargs", "-a", "list", _oracle.ENGINE_PDFTEX],
                     ["kpsewhich", "&" + eng[0]], ["sh", "-c", "true"],
                     ["sha256sum", _selector("progname") + _oracle.ENGINE_PDFLATEX],
                     ["/usr/bin/" + eng[-1], "x"]):
            try:
                self.oracle("ok").image_command(argv)
                self.expect(f"image_command ran {argv[:1]}... (a TeX engine, a "
                            f"format selector or a shell)", False)
            except _oracle.OracleError:
                self.expect("-", True)
        _oracle._ORACLE = None

    # ------------------------------------ argv allow-list and container state
    def container_init(self) -> None:
        """C-97: the long-lived container reaps (--init) and is bounded
        (--pids-limit). A container started without them (an older oracle's)
        is replaced, never graded in; one that still lacks them after
        creation is refused. Drives the real _ensure_container against the
        fake docker, reading back its docker calls."""
        # Review round 2 (LOW-4): the configuration is part of the container's
        # NAME, so an older oracle's container is never replaced under a
        # grader still running it.
        import inspect
        src = inspect.getsource(_oracle.ContainerOracle.__init__)
        tag = _oracle.CONTAINER_CONFIG_TAG
        self.expect("the oracle's container name no longer carries its "
                    "configuration (--init, the pids limit)",
                    "+ CONTAINER_CONFIG_TAG" in src and "init" in tag
                    and str(_oracle.PIDS_LIMIT) in tag)
        # Review round 2 (LOW-2): clearing an output never follows a symlink.
        link, target = self.workroot / "t.pdf", self.workroot / "fig.pdf"
        for f in (link, target):
            f.unlink(missing_ok=True)
        target.write_text("figure\n")
        link.symlink_to(target.name)
        try:
            self.oracle("ok").remove([link])
            ok = target.exists() and not link.is_symlink()
        except _oracle.OracleError:
            ok = False
        self.expect("ContainerOracle.remove deleted a symlink's TARGET (clearing "
                    "t.pdf -> fig.pdf deleted the figure) or kept the link", ok)
        for f in (link, target):
            f.unlink(missing_ok=True)
        # ... and a document shipping its own output name as a symlink is not
        # graded at all (pdfTeX would write through it into the target).
        target.write_text("figure\n")
        link.symlink_to(target.name)
        try:
            self.oracle("okpdf").run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
            refused = False
        except _oracle.OracleError:
            refused = True
        self.expect("run_to_fixpoint graded a document whose t.pdf is a symlink "
                    "(pdfTeX writes through it into fig.pdf)", refused and
                    target.read_text() == "figure\n")
        for f in (link, target, self.workroot / "t.log"):
            f.unlink(missing_ok=True)
        _oracle._ORACLE = None
        calls, state = self.td / "calls", self.td / "cstate"
        img = _oracle.IMAGE
        lim = str(_oracle.PIDS_LIMIT)
        cases = (("no --init", f"true {img} false {lim}", "true " + lim, True, True),
                 ("no --pids-limit", f"true {img} true 0", "true " + lim, True, True),
                 ("the oracle's own", f"true {img} true {lim}", "true " + lim, False, True),
                 ("docker ignoring --init", f"true {img} false {lim}", "false " + lim,
                  True, False))
        saved = {k: os.environ.get(k) for k in
                 ("FAKE_CALLS", "FAKE_STATE", "FAKE_INSPECT", "FAKE_HOSTCFG")}
        try:
            for label, insp, hostcfg, want_replace, want_ok in cases:
                calls.write_text("")
                state.write_text("present")
                os.environ.update(FAKE_CALLS=str(calls), FAKE_STATE=str(state),
                                  FAKE_INSPECT=insp, FAKE_HOSTCFG=hostcfg)
                o = _oracle.ContainerOracle.__new__(_oracle.ContainerOracle)
                _oracle._Base.__init__(o)
                o.docker, o.workroot, o.name = str(self.fake), self.workroot, "lp-oracle-fake"
                try:
                    _silenced(o._ensure_container)
                    ok = True
                except _oracle.OracleError:
                    ok = False
                log = calls.read_text().splitlines()
                runs = [c for c in log if c.startswith("run -d")]
                replaced = any(c.startswith("rm -f") for c in log) and bool(runs)
                flags_ok = all("--init" in r.split() and f"--pids-limit {lim}" in r
                               for r in runs)
                self.expect(f"_ensure_container on a container with {label}: "
                            f"replaced={replaced} (want {want_replace}), accepted="
                            f"{ok} (want {want_ok}), new container flags ok="
                            f"{flags_ok} (C-97)",
                            replaced == want_replace and ok == want_ok and flags_ok,
                            "; ".join(log)[:300])
        finally:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v

    def argv_and_state(self) -> None:
        """C-91 review round 5. (a) A graded run's ARGV is an allow-list, on
        every entry point: the round-5 review MEASURED `-cnf-line=openout_any=a`
        (an \\openout to /tmp written, rc 0) and `-shell-escape` /
        `-cnf-line=shell_escape=t` (\\pdfshellescape=1) passing through the
        shim and run_pdflatex on both backends. (b) Every writable kpathsea
        tree is private per run (TEXMFCONFIG was not: a .sty planted there
        flipped a clean graded run from rc 1 to rc 0). (c) The long-lived
        container is refused when its persistent TeX trees hold a file
        (check_texmf_trees, every construction) or any path of its root
        filesystem changed since creation (check_state, once per session)."""
        hostile = [["-cnf-line=openout_any=a", "t.tex"],
                   ["-cnf-line=shell_escape=t", "t.tex"],
                   ["-shell-escape", "t.tex"], ["--shell-escape", "t.tex"],
                   ["-enable-write18", "t.tex"], ["-shell-restricted", "t.tex"],
                   ["-no-shell-escape", "t.tex"], ["-output-directory=/tmp", "t.tex"],
                   ["-jobname=x", "t.tex"], ["-ini", "t.tex"],
                   ["-translate-file=cp227.tcx", "t.tex"],
                   ["-kpathsea-debug=4095", "t.tex"], ["-mktex=tfm", "t.tex"],
                   [_selector("fmt") + "x", "t.tex"], [_selector("progname") + "x", "t.tex"],
                   [_amp("x"), "t.tex"], ["t.tex", "u.tex"], [" " + _amp("x")],
                   ["t.tex \\relax"], ["../t.tex"], ["/etc/t.tex"], ["\\input t"],
                   ["-interaction=nonstopmode"], []]
        for argv in hostile:
            o = self.oracle("ok")
            try:
                o.run_pdflatex(self.workroot, argv, self.tv(), 60)
                self.expect(f"run_pdflatex ran the argv {argv!r} (not on the "
                            f"graded allow-list)", False)
            except _oracle.OracleError:
                self.expect("-", True)
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for argv in hostile[:3]:
                self.oracle("ok")
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", *argv])
                self.expect(f"the _oracle.py pdflatex shim exited {rc} for the argv "
                            f"{argv!r}, expected INFRA_RC", rc == _oracle.INFRA_RC)
            # the native backend's shim: a fake engine that would grade rc 0
            bindir = self.td / "nbin-argv"
            bindir.mkdir(exist_ok=True)
            eng = bindir / _oracle.ENGINE_PDFLATEX
            eng.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\nexit 0\n")
            eng.chmod(0o755)
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            n.engine_base["PATH"] = f"{bindir}:/usr/bin:/bin"
            fake_supervisor(bindir)
            _oracle._ORACLE = n
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                          "-cnf-line=openout_any=a",
                                          "-interaction=nonstopmode", "t.tex"])
            self.expect(f"the native shim exited {rc} for -cnf-line, expected "
                        f"INFRA_RC", rc == _oracle.INFRA_RC)
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                          "-interaction=nonstopmode", "-halt-on-error",
                                          "t.tex"])
            self.expect(f"the native shim refused the graders' own argv (rc {rc})",
                        rc == 0)
        finally:
            os.chdir(cwd)
            _oracle._ORACLE = None
        # the graders' own argv still runs (run_once, run_to_fixpoint)
        o = self.oracle("ok")
        try:
            r = o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
            self.expect("run_to_fixpoint no longer runs the protocol's argv", r.rc == 0)
        except _oracle.OracleError as e:
            self.expect("run_to_fixpoint refused the protocol's own argv", False, str(e))
        # run_engine: gen_contract.py's INITEX argv passes, an override does not
        tv = _oracle.oracle_tex_vars(self.workroot / "tx")
        for argv, want in ((["-ini", "-etex", "-interaction=nonstopmode",
                             "-translate-file=cp227.tcx", "-jobname=lpvirgin",
                             "\\dump"], True),
                           (["-ini", "-cnf-line=shell_escape=t", "\\dump"], False),
                           (["-shell-escape", "t.tex"], False),
                           ([_selector("progname") + "x", "t.tex"], False)):
            o = self.oracle("ok")
            try:
                o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, argv, tv, 60)
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"run_engine {'refused' if want else 'ran'} {argv!r}",
                        ok == want)
        # (b) every writable kpathsea tree is private and required
        self.expect("private_texmf_vars no longer makes TEXMFCONFIG private",
                    set(_oracle.private_texmf_vars("/w")) >= {"TEXMFHOME", "TEXMFVAR",
                                                              "TEXMFCONFIG"}
                    and set(_oracle._GRADING_TEXMF) >= {"TEXMFHOME", "TEXMFVAR",
                                                        "TEXMFCONFIG"})
        try:
            env = dict(self.tv())
            env.pop("TEXMFCONFIG")
            _oracle.graded_env(env)
            self.expect("graded_env accepted a run without a private TEXMFCONFIG "
                        "(the container's persistent one is searched first)", False)
        except _oracle.OracleError:
            self.expect("-", True)
        # (b2) C-93: the container backend itself refuses a temporary
        # directory outside the work root, or TMP/TEMP/java's not derived from
        # it, on EVERY engine run (run_engine does not pass graded_env).
        outside = "/tmp/lp-c93-outside"
        for label, override in (
                ("a TMPDIR outside the work root",
                 _oracle.private_tmp_vars("/tmp/lp-c93-outside-td")),
                ("a TMPDIR that is not one plain path",
                 _oracle.private_tmp_vars(str(self.workroot) + "/a b")),
                ("a TMP not derived from TMPDIR", {"TMP": outside}),
                ("a JAVA_TOOL_OPTIONS not derived from TMPDIR",
                 {"JAVA_TOOL_OPTIONS": "-XX:+UsePerfData"})):
            o = self.oracle("ok")
            try:
                o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini", "\\dump"],
                             dict(tv, **override), 60)
                self.expect(f"the container backend ran an engine with {label} "
                            f"(C-93)", False)
            except _oracle.OracleError:
                self.expect("-", True)
        # (c) the container's state
        import json as _json
        arch = sorted(_oracle.TREE_FINGERPRINTS)[0]
        os.environ["FAKE_FP"] = _json.dumps(dict(
            _oracle.TREE_FINGERPRINTS[arch], arch=arch,
            banner="pdfTeX " + _oracle.EXPECT_VERSION))
        cenv = self.td / "container-env-state"
        cenv.write_text("\0".join(f"{k}={v}" for k, v in _oracle.IMAGE_ENV.items()))
        os.environ["FAKE_CENV"] = str(cenv)
        for trees, want_ok in (
                (None, True),
                ("D /tmp/texmf\nD /tmp/.texlive2026/texmf-var\nD /tmp/.texlive2026/"
                 "texmf-config\n/tmp/.texlive2026/texmf-config/tex/latex/p.sty\n", False),
                ("D /tmp/texmf\n", False)):
            if trees is None:
                os.environ.pop("FAKE_TREES", None)
            else:
                os.environ["FAKE_TREES"] = trees
            try:
                self.oracle("ok").fingerprint()  # every construction runs it
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"ContainerOracle.fingerprint (check_texmf_trees) "
                        f"{'refused' if want_ok else 'accepted'} the trees "
                        f"{trees!r}", ok == want_ok)
        for k in ("FAKE_TREES", "FAKE_FP", "FAKE_CENV"):
            os.environ.pop(k, None)
        wr = str(self.workroot)
        clean = ("d /\nd /tmp\nd /tmp/.texlive2026\nd /tmp/.texlive2026/texmf-var\n"
                 "f /var/cache/fontconfig/0123456789abcdef0123456789abcdef-le64.cache-9\n"
                 f"f /etc/hostname\nd {wr}\nd {self.workroot.parent}\n")
        for find, want_ok in ((clean, True),
                              (clean + "f /usr/local/texlive/texmf-local/tex/latex/p.sty\n", False),
                              (clean + "f /tmp/.texlive2026/texmf-config/p.sty\n", False),
                              (clean + "f /tmp/x.txt\n", False),
                              (clean + "f /usr/local/texlive/2026/texmf.cnf\n", False),
                              # C-97: --init touches these two DIRECTORIES only
                              (clean + "d /usr\nd /usr/sbin\n", True),
                              (clean + "d /usr\nd /usr/sbin\nf /usr/sbin/x\n", False),
                              (clean + "f /usr\n", False)):
            os.environ["FAKE_FIND"] = find
            _oracle._STATE_CHECKED = False
            o = self.oracle("ok")
            _oracle._STATE_CHECKED = False
            try:
                _oracle.get_oracle()
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"get_oracle's session state scan "
                        f"{'refused' if want_ok else 'accepted'} a container whose "
                        f"changed paths are {find.split()[-1]!r}", ok == want_ok)
        os.environ.pop("FAKE_FIND", None)
        _oracle._ORACLE = None
        _oracle._STATE_CHECKED = False

    # ----------------------------------------------------------------- shell
    def shell_grader(self) -> None:
        fro = (self.repo / "scripts/tools/false_ready_oracle.sh").read_text()
        funcs = {}
        for name in ("run_pdflatex", "drift_class"):
            m = re.search(rf"^{name}\(\) \{{.*?^\}}$", fro, re.M | re.S)
            if not m:
                self.expect(f"false_ready_oracle.sh no longer defines {name}()", False)
                return
            funcs[name] = m.group(0)
        eng = self.td / "fake-engine"
        eng.write_text(FAKE_ENGINE)
        eng.chmod(0o755)
        osh = (self.repo / "scripts/tools/_oracle.sh").read_text()
        m = re.search(r"^oracle_vet\(\) \{.*?^\}$", osh, re.M | re.S)
        if not m:
            self.expect("_oracle.sh no longer defines oracle_vet()", False)
            return
        readers = re.findall(r"^oracle_(?:job|pdf_written)\(\) \{.*?\}$", osh, re.M)
        if len(readers) != 2:
            self.expect("_oracle.sh no longer defines oracle_job()/oracle_pdf_written()",
                        False)
            return
        lib = self.td / "fro_funcs.sh"
        lib.write_text(f'ROOT="{self.repo}"\n' + m.group(0) + "\n" + "\n".join(readers)
                       + "\n" + funcs["run_pdflatex"] + "\n" + funcs["drift_class"] + "\n")
        wd = self.td / "wd"
        wd.mkdir(exist_ok=True)

        def run(plan: str, **extra) -> str:
            self.count.unlink(missing_ok=True)
            env = dict(os.environ, FAKE_PLAN=plan, TMPDIR=str(self.td), **extra)
            p = subprocess.run(
                ["bash", "-c", f'source "{lib}"; PDFLATEX=("{eng}"); TIMEOUT=; '
                 f'run_pdflatex "{wd}" t.tex 1'], capture_output=True, text=True,
                env=env)
            return p.stdout.strip()
        for plan in ("dead", "ok,dead", "fail,dead"):
            got = run(plan)
            # Every pass runs (success must be STABLE), so a lost SECOND pass
            # must void the result even after a genuine first one.
            self.expect(f"false_ready_oracle.sh run_pdflatex graded plan '{plan}' "
                        f"as '{got}' (a pass with no pdfTeX banner)",
                        got.startswith("NOPROOF"))
        got = run("fail")
        self.expect(f"run_pdflatex no longer grades a genuine failure rc 1 (got '{got}')",
                    got.split()[:1] == ["1"])
        # OPEN-118 review round 3: banner present, then pdfTeX failing to write
        # its own output (disk full) -- refused; the document's own \openout
        # refusal -- still graded; a work root below the floor -- refused
        # before any pass runs.
        for plan in ("fwrite", "ok,fwrite"):
            got = run(plan)
            self.expect(f"false_ready_oracle.sh run_pdflatex graded plan '{plan}' "
                        f"as '{got}' (pdfTeX could not write its own output)",
                        got.startswith("ENVFAIL"))
        got = run("openout")
        self.expect(f"run_pdflatex no longer grades a document's own \\openout "
                    f"refusal rc 1 (got '{got}')", got.split()[:1] == ["1"])
        # C-97 review round 2: the PDF verdict is pdfTeX's own report in the
        # pass's log -- a genuine page is "yes", a .pdf the document wrote
        # itself is "no", and so is a stale one under a no-pages pass.
        for plan, want in (("okpdf", "0 yes"), ("forge", "0 no"), ("okpdf,forge", "0 no")):
            got = (wd / "t.pdf").unlink(missing_ok=True) or run(plan)
            self.expect(f"false_ready_oracle.sh run_pdflatex graded plan '{plan}' "
                        f"as '{got}', expected '{want}' (C-97: a .pdf pdfTeX did not "
                        f"report writing is not a PDF)", got == want)
        got = (wd / "t.pdf").unlink(missing_ok=True) or run("batchforge")
        self.expect(f"false_ready_oracle.sh run_pdflatex graded plan 'batchforge' "
                    f"as '{got}' (a forged terminal report against the log's "
                    f"'No pages of output.' is not a grade, C-99)",
                    got.startswith("ENVFAIL"))
        for f in ("t.pdf", "t.log"):
            (wd / f).unlink(missing_ok=True)
        got = run("ok", LP_ORACLE_MIN_FREE_MB=str(10 ** 12))
        self.expect(f"run_pdflatex graded a run with the work root below the "
                    f"free-space floor as '{got}'", got.startswith("ENVFAIL")
                    and not self.count.exists())
        # diff_compile_check.sh: the run is inline, so pin the ORDER: a vet
        # before the engine, a vet of the run's stdout after it, and the
        # refusal before any grade is computed.
        dcc = (self.repo / "scripts/tools/diff_compile_check.sh").read_text()
        i_pre = dcc.find('oracle_vet "$d" 2>/dev/null || envok=no')
        i_run = dcc.find('"${PDFLATEX[@]}" -interaction=nonstopmode -halt-on-error "$base" >"$pout"')
        i_post = dcc.find('! oracle_vet "$d" "$pout" -interaction=nonstopmode')
        i_ref = dcc.find('"ENVFAIL" "not graded')
        i_grade = dcc.find('then pl=COMPILES; else pl=FAILS; fi')
        self.expect("diff_compile_check.sh no longer vets free space before the "
                    "run AND the run's own output after it, before grading",
                    -1 not in (i_pre, i_run, i_post, i_ref, i_grade)
                    and i_pre < i_run < i_post < i_ref < i_grade)
        # C-95/C-97 review round 2: diff_compile_check.sh's PDF verdict and log
        # name come from the oracle's ONE reader, not `${base%.tex}.pdf`.
        self.expect("diff_compile_check.sh no longer takes its PDF verdict from "
                    "oracle_pdf_written (pdfTeX's own report) and its job name "
                    "from oracle_job",
                    'oracle_pdf_written "$d" "$base"' in dcc
                    and 'job="$(oracle_job "$base")"' in dcc
                    and "${base%.tex}" not in dcc and "${base%.tex}" not in fro)
        # ... and NO oracle client forms a run's output name or PDF verdict
        # itself (review round 3, M2: the first check was a narrow regex, evaded
        # four ways). See output_names_findings.
        hits = output_names_findings(self.repo)
        self.expect(f"an oracle client names an engine output or takes a PDF "
                    f"verdict other than through the oracle API (C-95/C-99): "
                    f"{hits[:6]}", not hits)
        # The halt run's proof must be checked BEFORE its artefacts are deleted.
        i_halt = fro.find('read -r hrc hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"')
        i_rm = fro.find('"${ORACLE_RM[@]}" "$rundir/$job.pdf"')
        i_chk = fro.find("grep -q 'This is pdfTeX' \"$rundir/$job.log\"")
        i_nop = fro.find("124|125|126|127|NOPROOF|ENVFAIL)")
        self.expect("false_ready_oracle.sh checks the halt run's pdfTeX log and "
                    "NOPROOF only AFTER deleting it (or not at all)",
                    -1 not in (i_halt, i_rm, i_chk, i_nop)
                    and i_halt < i_nop < i_rm and i_halt < i_chk < i_rm)
        for g, m, want in (("error-halt", "compiles", "hard-rejects"),
                           ("strong-fatal", "compiles", "hard-rejects"),
                           ("compiles", "error-halt", "hard-compiles"),
                           ("error-halt", "strong-fatal", "soft"),
                           ("compiles", "compiles", "ok")):
            p = subprocess.run(["bash", "-c", f'source "{lib}"; drift_class {g} {m}'],
                               capture_output=True, text=True)
            self.expect(f"drift_class {g} vs manifest {m} = '{p.stdout.strip()}', "
                        f"expected {want}", p.stdout.strip() == want)


def _amp(fmt: str) -> str:
    """`&fmt` (TeX's format selector), built from a parameter for the same
    reason as _selector."""
    return "&" + fmt


def _selector(kind: str) -> str:
    """A format selector (`-progname=`), built from a parameter: this file is
    scanned by check_oracle_pin, and a literal one is (rightly) a finding."""
    return f"-{kind}="


def _silenced(fn, *a):
    import contextlib
    import io
    buf = io.StringIO()
    out = io.TextIOWrapper(io.BytesIO())  # the shim writes sys.stdout.buffer
    with contextlib.redirect_stderr(buf), contextlib.redirect_stdout(out):
        try:
            return fn(*a)
        except SystemExit as e:
            return e.code
        except ValueError as e:  # the injected bug below: escaping IS the finding
            return f"raised {type(e).__name__}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    repo = Path(ap.parse_args().repo).resolve()
    saved = {k: os.environ.get(k) for k in ("FAKE_PLAN", "FAKE_COUNT", "DEAD_MSG")}
    with tempfile.TemporaryDirectory(prefix="oracle-infra-") as td:
        c = Checker(repo, Path(td))
        # An OracleError a section did not expect is a FAILURE of that
        # section (the oracle refused a run the protocol makes), reported
        # with its message, never a crash that hides the other sections.
        for section in (c.python_graders, c.generator_client, c.grading_env,
                        c.argv_and_state, c.container_init, c.shell_grader):
            try:
                section()
            except _oracle.OracleError as e:
                c.expect(f"{section.__name__}: the oracle refused a run the "
                         f"protocol makes", False, str(e)[:300])
            finally:
                _oracle._ORACLE = None
    for k, v in saved.items():
        if v is None:
            os.environ.pop(k, None)
        else:
            os.environ[k] = v
    if c.failures:
        print("[oracle-infra] FAIL: an oracle run without proof that pdfTeX ran "
              "would be graded:", file=sys.stderr)
        for f in c.failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-infra] OK: {c.n} checks; every no-proof shape (dead daemon "
          f"socket, daemon error, cut stream, no banner) and every "
          f"environment-failure shape (pdfTeX unable to write its own output, "
          f"work root below the free-space floor before or after a run) is "
          f"refused by the Python graders, the shim (INFRA_RC) and the shell "
          f"graders, and a genuine pdfTeX failure (incl. a document's own "
          f"\\openout refusal) is still graded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
