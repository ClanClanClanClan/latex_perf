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
point (run_pdflatex, the shim, check_apply_fixes_roundtrip.pdflatex_ok)
under a HOSTILE host environment and reads back what reached the engine:
EXACTLY the image's environment, ORACLE_TEX_VARS, the fixed run variables
and the protocol clock (OPEN-128), nothing else; `_oracle.sh` must route
every run through the shim; image_command must start no engine by any route.
Review round 4: those checks named the variables that must NOT reach the
engine, and a host `openout_any_pdflatex=a` (a kpathsea form nobody listed)
flipped a grade on the native backend. They now assert what MAY reach it --
the image's own environment (`_oracle.IMAGE_ENV`) plus the run's TeX
variables -- and the container backend must refuse a container whose own
environment is not the image's.

C-93 (2026-09-29): a PRIVATE TMPDIR per run (repstopdf -> gs left /tmp/gs_*
in the long-lived container when a timeout killed it). Since OPEN-128 every
run is its own container, and its TMPDIR and TeX trees live at fixed paths on
its own fresh tmpfs; the checks read back that the engine got them and that
the supervisor creates them before the engine starts.

C-95 (2026-09-29): each run's evidence is its own. A stale PDF (or log, .fls,
.fmt) from an earlier pass or run was read as the current one's by three
copies of the pass loop (run_to_fixpoint, false_ready_oracle.sh through the
shim, gen_contract.py through run_engine). The per-run primitive now clears
them; the checks drive each entry point with stale outputs present.

C-97 (2026-09-29): a container reaps (--init) and is bounded (--pids-limit).
OPEN-128 (ADR-015 E15): ONE LAUNCH DEFINITION. Every container the oracle
starts -- an engine run, the session probe, an image command, a removal --
is `_oracle.launch_argv`'s, with exactly its flags (read back from the fake
docker); the session probe refuses a container whose tree, read-only facts,
environment, work-root view or shim is not the pinned one; every engine
run must carry the shim's proof (sha256 and the engine's mark); the native
backend is refused; a measurement (`measure`) is tagged and never compared
with a grade; the clock is part of the oracle's identity.

This gate is PURE (no docker, no TeX): it drives the real grading code with
FAKE docker/engine executables that reproduce each failure shape, including the
re-reviewer's dead-socket one, and asserts each is refused, while a genuine
pdfTeX failure (banner present, rc 1) is still graded. Its kill-tests in
check_gate_selftests.py revert each proof check and must make it fail.

Run: python3 scripts/tools/check_oracle_infra_grading.py --repo .
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

DEAD_MSG = ("failed to connect to the docker API at unix:///nonexistent.sock; "
            "check if the path is correct and if the daemon is running: dial "
            "unix /nonexistent.sock: connect: no such file or directory")

# A fake `docker` for the ONE launch definition (OPEN-128: every engine run is
# `docker run --rm ... -v RUNDIR:/lp/run ... --entrypoint sh IMAGE -c SCRIPT
# sh NONCE TIMEOUT SUPERVISOR CONFIG ENGINE ARGS...`). Container paths are
# mapped back to the host through the run's -v mounts. Engine runs are
# answered according to FAKE_MODE (one mode per call, consumed from a
# comma-separated FAKE_PLAN via FAKE_COUNT); like the real supervisor it first
# deletes the config's `remove` files in the run directory:
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
# The session probe (`--entrypoint python3 ... -c PROBE`) answers FAKE_FP,
# FAKE_RO, FAKE_CENV (a NUL-separated environment file), the nonce the host
# wrote into the probe's run directory, and FAKE_SHIM (default: the pinned
# sha256). `--entrypoint rm` deletes its (host = container) paths.
# The fake container's user (OPEN-126: --user, never root).
FAKE_USER = "501:20"
FAKE_DOCKER = r'''#!/usr/bin/env python3
import json, os, sys
a = sys.argv[1:]
if os.environ.get("FAKE_STDIN"):   # what the docker client got on stdin
    open(os.environ["FAKE_STDIN"], "wb").write(sys.stdin.buffer.read())
if os.environ.get("FAKE_CALLS"):        # every docker call, one per line
    open(os.environ["FAKE_CALLS"], "a").write("\0".join(a) + "\n")
if a[:1] == ["version"]:
    print("27.0"); sys.exit(0)
if a[:2] == ["image", "inspect"]:
    sys.exit(0)
if a[:2] == ["rm", "-f"] or a[:1] == ["ps"]:
    sys.exit(0)
if a[:1] != ["run"]:
    sys.exit(0)
mounts, workdir, entry, rest = [], "/", None, []
k = 1
while k < len(a):
    if a[k] == "-v":
        spec = a[k + 1].split(":")
        mounts.append((spec[0], spec[1])); k += 2; continue
    if a[k] == "-w":
        workdir = a[k + 1]; k += 2; continue
    if a[k] == "--entrypoint":
        entry = a[k + 1]
        rest = a[k + 3:]          # after the image
        break
    k += 1
def host_of(cpath):
    for h, c in sorted(mounts, key=lambda m: -len(m[1])):
        if cpath == c or cpath.startswith(c.rstrip("/") + "/"):
            return h + cpath[len(c):]
    return None
if os.environ.get("FAKE_ARGV") and entry == "sh":
    open(os.environ["FAKE_ARGV"], "w").write("\0".join(a))
if entry == "python3":                   # the session probe
    probe_dir = host_of("/lp/run")
    nonce = open(os.path.join(probe_dir, "nonce")).read() if probe_dir else ""
    if os.environ.get("FAKE_CENV"):
        cenv = dict(x.split("=", 1) for x in open(os.environ["FAKE_CENV"]).read().split("\0") if "=" in x)
    else:
        cenv = json.loads(os.environ["FAKE_DEFAULT_CENV"])
    print(json.dumps({"fp": json.loads(os.environ["FAKE_FP"]),
                      "ro": json.loads(os.environ.get("FAKE_RO", '{"euid": 501, "texmfroot": '
                            '"/usr/local/texlive/2026", "root_ro": true, "tree_ro": true}')),
                      "env": cenv, "nonce": nonce,
                      "shim": os.environ.get("FAKE_SHIM", json.loads(os.environ["FAKE_SHIM_MAP"])[
                          {"linux/arm64": "aarch64", "linux/amd64": "x86_64"}[
                              a[a.index("--platform") + 1]]])}))
    sys.exit(int(os.environ.get("FAKE_PROBE_RC", "0")))
if entry == "rm":
    for q in rest:
        if q.startswith("-"):
            continue
        try:
            os.unlink(q)
        except FileNotFoundError:
            pass
    sys.exit(0)
if entry != "sh":
    sys.exit(0)                          # image commands
plan = os.environ["FAKE_PLAN"].split(",")
cf = os.environ["FAKE_COUNT"]
n = int(open(cf).read()) if os.path.exists(cf) else 0
open(cf, "w").write(str(n + 1))
mode = plan[min(n, len(plan) - 1)]
i = a.index("-c")
nonce = a[i + 3]
cfg = json.loads(a[i + 6])
cwd = host_of(workdir)
for f in cfg.get("remove", []):         # the supervisor clears stale evidence
    try:
        os.unlink(os.path.join(cwd, f))
    except FileNotFoundError:
        pass
if os.environ.get("FAKE_CFG"):
    open(os.environ["FAKE_CFG"], "w").write(a[i + 6])
banner = "This is pdfTeX, Version 3.141592653-2.6-1.40.29 (TeX Live 2026)\n"
def rcline(rc):
    # the run supervisor's evidence line (C-99, OPEN-128), then the rc line
    evid = os.environ.get("FAKE_EVID") or json.dumps({
        "alias": [], "cw": {}, "err": "", "overflow": 0, "engine_pid": 10,
        "shim_sha256": json.loads(os.environ["FAKE_SHIM_MAP"])[
            cfg["shim"].rsplit("lpshim-", 1)[1][:-3]], "shim_mode": "restricted",
        "fs_denied": [0]})
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
        # -z (C-129): without it git C-quotes a non-ASCII path, which then
        # names no file and escapes every check.
        out = subprocess.run(["git", "-C", str(repo), "ls-files", "-z"],
                             capture_output=True, encoding="utf-8",
                             errors="surrogateescape", timeout=60)
        if out.returncode == 0 and out.stdout.strip("\0"):
            return [f for f in out.stdout.split("\0") if f]
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


def evid(**over) -> str:
    """A supervisor evidence line (C-99, OPEN-128) with the protocol's shim
    proof unless a field is overridden: a refusal test must fail for ITS
    defect, not for a missing shim mark."""
    e = {"alias": [], "cw": {}, "err": "", "overflow": 0, "engine_pid": 10,
         "shim_sha256": _oracle.SHIM_SHA256[_oracle.ARCH_OF_RECORD],
         "shim_mode": "restricted", "fs_denied": [0]}
    e.update(over)
    return json.dumps({k: v for k, v in e.items() if v is not OMIT})


OMIT = object()


def record_fp(arch: str | None = None) -> dict:
    arch = arch or _oracle.ARCH_OF_RECORD
    return dict(_oracle.TREE_FINGERPRINTS[arch], arch=arch,
                banner="pdfTeX " + _oracle.EXPECT_VERSION,
                texmfroot="/usr/local/texlive/2026")


# The protocol's complete engine environment (what graded_env + engine_env
# give a graded run): read back from the run's configuration.
def protocol_env() -> dict:
    return _oracle.engine_env(_oracle.graded_env({}))


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
        self.shim_dir = self.workroot / ".lp-shim" / "fake"
        self.shim_dir.mkdir(parents=True)
        # The file arguments the fakes run must exist (check_file_argument, M1).
        # (t.TEX and t.Tex too: CI's file system is case-SENSITIVE, a Mac's
        # is not, so on a Mac they are t.tex itself.)
        for f in ("t.tex", "t.ltx", "a.b.tex", "x.tex", "t.TEX", "t.Tex"):
            (self.workroot / f).write_text("\\relax\n")
        os.environ["DEAD_MSG"] = DEAD_MSG
        os.environ["FAKE_COUNT"] = str(self.count)
        os.environ["FAKE_SHIM_MAP"] = json.dumps(_oracle.SHIM_SHA256)
        os.environ["FAKE_DEFAULT_CENV"] = json.dumps(
            dict(_oracle.IMAGE_ENV, HOSTNAME=_oracle.ORACLE_HOSTNAME))
        os.environ["FAKE_FP"] = json.dumps(record_fp())

    def expect(self, label: str, ok: bool, detail: str = "") -> None:
        self.n += 1
        if not ok:
            self.failures.append(f"{label}{': ' + detail if detail else ''}")

    def bare(self):
        """A ContainerOracle wired to the fake docker, without __init__'s
        docker handshake and with NO session probe taken yet."""
        o = _oracle.ContainerOracle.__new__(_oracle.ContainerOracle)
        _oracle._Base.__init__(o)
        o.docker, o.workroot, o.name = str(self.fake), self.workroot, "lp-oracle-fake"
        o.user = FAKE_USER
        o.shim_dir = self.shim_dir
        o._fps = {}
        return o

    def oracle(self, plan: str):
        """A ContainerOracle wired to the fake docker, its session probe
        already taken (the fake fingerprint of the architecture of record)."""
        self.count.unlink(missing_ok=True)
        os.environ["FAKE_PLAN"] = plan
        o = self.bare()
        rec = _oracle.ARCH_OF_RECORD
        o._fps = {rec: record_fp(rec), "x86_64": record_fp("x86_64")}
        o._fp = o._fps[rec]
        _oracle._ORACLE = o
        return o

    def tv(self) -> dict:
        """What tex_env gives a grader (graded_env imposes the rest)."""
        return _oracle.oracle_tex_vars()

    def run_pdflatex(self, plan: str):
        o = self.oracle(plan)
        try:
            return o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                                  self.tv(), 60), None
        except _oracle.OracleError as e:
            return None, e

    def cfg(self, path: Path) -> dict:
        return json.loads(path.read_text())

    # ---------------------------------------------------------------- python
    def python_graders(self) -> None:
        for mode in ("dead", "daemonerr", "cut", "nobanner"):
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

        # C-95: each pass's evidence is its own (see the older notes in git).
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
                    if f.suffix in (".pdf", ".log"):
                        f.unlink()
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
        # The same defect in the pass loops OUTSIDE run_to_fixpoint (C-95): the
        # shim (false_ready_oracle.sh) and run_engine (gen_contract.py) each
        # take the one primitive, whose run deletes the job's evidence files
        # INSIDE its container (the supervisor's `remove`) before the engine.
        outs = [self.workroot / ("t" + e) for e in (".pdf", ".log", ".fls", ".fmt")]
        cfgf = self.td / "cfg-stale"
        os.environ["FAKE_CFG"] = str(cfgf)
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for f in outs:
                f.write_text("stale\n")
            self.oracle("nopages")
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                          "-interaction=nonstopmode", "t.tex"])
            left = [f.name for f in outs if f.exists() and f.read_text() == "stale\n"]
            rm = self.cfg(cfgf).get("remove") if cfgf.exists() else None
            self.expect(f"the _oracle.py pdflatex shim left an earlier run's "
                        f"{left} in place for a run that wrote none (a stale PDF "
                        f"read as this pass's, C-95; false_ready_oracle.sh); the "
                        f"run's supervisor was told to remove {rm}",
                        rc == 0 and not left
                        and sorted(rm or []) == sorted(f.name for f in outs), f"rc {rc}")
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
        finally:
            os.environ.pop("FAKE_CFG", None)
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
        stdin: no engine run inherits the grader's stdin. OPEN-128: a run
        whose engine did not run under the pinned shim is refused."""
        wr = self.workroot
        # (1) the supervisor saw the document write pdfTeX's own log/pdf twice,
        # or could not watch, or the shim's proof is missing or wrong
        for ev, what in ((evid(cw={"t.log": 2}), "its own log"),
                         (evid(cw={"t.pdf": 2}), "its own pdf"),
                         (evid(err="OSError(38)"), "no inotify"),
                         (evid(overflow=1), "a queue overflow"),
                         (evid(alias=[["T.LOG", "t.log"]], cw={"t.log": 1}),
                          "an alias of its own log (case-insensitive root)"),
                         (evid(alias=OMIT), "no alias list"),
                         ("OMIT", "no evidence line at all"),
                         ("NOT-JSON", "an unreadable evidence line"),
                         # OPEN-128: the shim's proof
                         (evid(shim_sha256="0" * 64), "another shim than the pinned one"),
                         (evid(shim_sha256=OMIT), "no shim hash"),
                         (evid(shim_mode=None), "no shim mark on the engine "
                          "(the preload was ignored: the real clock)"),
                         (evid(shim_mode="free"), "a shim without the TeX "
                          "file-system view on the engine")):
            os.environ["FAKE_EVID"] = ev
            try:
                got, err = self.run_pdflatex("okpdf")
            finally:
                os.environ.pop("FAKE_EVID", None)
            self.expect(f"run_pdflatex graded a run whose supervisor reported "
                        f"{what} (C-99/OPEN-128: the evidence is not the oracle's)",
                        err is not None, f"returned {got!r}")
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
        os.environ["FAKE_EVID"] = evid()
        try:
            got, err = self.run_pdflatex("okpdf")
            self.expect("a run with the protocol's evidence (the pinned shim, its "
                        "mark on the engine) is refused", err is None, str(err)[:200])
        finally:
            os.environ.pop("FAKE_EVID", None)
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
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
        o = self.oracle("batchok")
        r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
        self.expect(f"a \\batchmode document that ships a page no longer grades "
                    f"compiles (the log alone decides): {r!r}", r.compiles)
        o = self.oracle("errforge")
        r = o.run_to_fixpoint(wr, "t.tex", self.tv(), 60)
        self.expect(f"a document printing a forged '! ...' error line changed "
                    f"the verdict: {r!r}", r.compiles and r.rc == 0)
        for f in ("t.pdf", "t.log"):
            (wr / f).unlink(missing_ok=True)
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
        pre = b"x" * 79 + b"\n"
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
        rep = b"Output written on t.pdf (1 page, 9 bytes)."
        syn = b"SyncTeX written on t.synctex.gz."
        tr = b"Transcript written on t.log."
        j48 = "a" * 48
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
        # (5) no engine run inherits the grader's stdin: the docker client
        # gets /dev/null (the supervisor gives the engine /dev/null, or a
        # measurement's own input file: supervisor_checks)
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
        finally:
            os.environ.pop("FAKE_STDIN", None)
            os.dup2(saved0, 0)
            os.close(saved0)
            _oracle._ORACLE = None

    def supervisor_checks(self) -> None:
        """THE REAL SUPERVISOR (_SUPERVISOR_SRC): on Linux (CI) it must count
        the evidence files' close-writes -- one is pdfTeX's, a second
        (directly or through a symlink) is the document's -- give its child
        /dev/null (or a measurement's input file), delete the stale evidence
        and create the run's directories BEFORE the engine starts, and pass
        the engine EXACTLY the configured environment; where inotify is
        missing (macOS) it must report that, and check_evidence must refuse
        the run (fail closed)."""
        d = self.td / "sup"
        d.mkdir(exist_ok=True)
        args = ["-interaction=nonstopmode", "t.tex"]

        def run(script: str, stdin_file=None, extra=None):
            for f in d.iterdir():
                if f.is_dir():
                    shutil.rmtree(f)
                else:
                    f.unlink()
            eng = d / "eng.sh"
            eng.write_text("#!/bin/sh\n" + script)
            eng.chmod(0o755)
            cfg = {"names": _oracle.evidence_names(args),
                   "remove": _oracle.evidence_names(args),
                   "env": {"PATH": "/usr/bin:/bin", "LPTEST": "only-this"},
                   "mkdirs": [str(d / "mk" / "a")]}
            if stdin_file:
                cfg["stdin"] = str(stdin_file)
            cfg.update(extra or {})
            p = subprocess.run([sys.executable, "-I", "-c", _oracle._SUPERVISOR_SRC,
                                "NONCE", json.dumps(cfg), str(eng)],
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
                    ("the document opens the held-open log twice, writing nothing",
                     "exec 3>t.log\necho x >&3\n: >> t.log\n: >> t.log\n"
                     "echo z >&3\nexec 3>&-\n", "refused"),
                    ("pdfTeX alone, holding its log open", "exec 3>t.log\n"
                     "echo x >&3\necho z >&3\nexec 3>&-\n", "graded"),
                    ("the document writes other files freely",
                     "echo x > t.log\necho a > t.aux\necho b > t.aux\n", "graded"),
                    ("the document writes the log through a hard link",
                     "echo x > t.log\nln t.log hard.txt\necho y > hard.txt\n", "refused"),
                    ("the document writes a case variant of the log",
                     "echo x > t.log\necho y > T.LOG\n", "refused"),
                    ("the document writes a case variant of the PDF, pdfTeX none",
                     "echo x > t.log\necho y > T.pdf\n", "refused"),
                    ("the document renames a file onto the PDF",
                     "echo x > t.log\necho y > z.txt\nmv z.txt t.pdf\necho w > t.pdf\n",
                     "refused"),
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
            inp = self.td / "measure-stdin"
            inp.write_bytes(b"\\relax\n")
            run("cat > stdin.got\necho x > t.log\n", stdin_file=inp)
            got = (d / "stdin.got").read_bytes() if (d / "stdin.got").exists() else None
            self.expect("the real supervisor did not give a measurement's engine "
                        "its terminal input file (ADR-015 E7)", got == b"\\relax\n",
                        repr(got))
            run("env > env.got\nls -d mk/a > mk.got\necho x > t.log\n")
            env = (d / "env.got").read_text() if (d / "env.got").exists() else ""
            got = sorted(ln.split("=", 1)[0] for ln in env.splitlines() if "=" in ln)
            self.expect("the real supervisor passed the engine an environment other "
                        "than EXACTLY its configuration (OPEN-128: not even docker's "
                        "HOSTNAME)", set(got) <= {"PATH", "LPTEST", "PWD", "SHLVL", "_",
                                                  "OLDPWD"} and "LPTEST" in got, repr(got))
            self.expect("the real supervisor did not create the run's directories "
                        "before the engine started (C-93's TMPDIR)",
                        (d / "mk.got").exists())
            (d / "t.pdf").write_text("stale")
            run("ls t.pdf > seen.got 2>/dev/null; echo x > t.log\n")
            self.expect("the real supervisor did not delete the job's stale evidence "
                        "inside the run before the engine started (C-95)",
                        (d / "seen.got").exists() and (d / "seen.got").read_text() == "")
        else:
            got = run("echo x > t.log\n")
            self.expect(f"the real supervisor without inotify ({sys.platform}) was "
                        f"not refused: {got!r} (fail closed, C-99)",
                        got.startswith("refused"))

    def host_diagnostic_checks(self) -> None:
        """HostDiagnostic (oracle_baseline_classify's host arm, never a
        grade) runs WITHOUT the evidence supervisor, gives the engine
        /dev/null, and get_oracle() never hands out an unsupervised backend.
        The retired native backend cannot be constructed (ADR-015 E15)."""
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
            r = h.run_to_fixpoint(wr, "t.tex", _oracle.oracle_tex_env(), 60)
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
            _oracle.get_oracle()
            self.expect("get_oracle() handed out an unsupervised backend (C-99)", False)
        except _oracle.OracleError:
            self.expect("-", True)
        finally:
            _oracle._ORACLE = saved
        self.expect("a grading backend is unsupervised",
                    getattr(_oracle.ContainerOracle, "supervised", False) is True)
        try:
            _oracle.NativeOracle()
            self.expect("the retired native backend can be constructed (ADR-015 "
                        "E15: it grades nothing)", False)
        except _oracle.OracleError:
            self.expect("-", True)

    # ------------------------------------------------ the contract generator
    def generator_client(self) -> None:
        """gen_contract.py and the L_S0 generators are CLIENTS of the oracle
        (run_engine): their jobs get the same proof-of-run refusals, the
        engine they name reaches the container, the environment is the
        protocol's with only the documented overrides (the log width; the
        clock as a parameter), and an oracle failure stops the generator
        instead of reading as a TeX outcome."""
        tv = _oracle.oracle_tex_vars()
        for mode in ("dead", "daemonerr", "cut", "nobanner", "fwrite"):
            o = self.oracle(mode)
            try:
                got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX,
                                   ["-ini", "-jobname=t", "\\dump"], tv, 60)
                self.expect(f"run_engine returned {got!r} for a '{mode}' run "
                            f"instead of raising OracleError", False)
            except _oracle.OracleError:
                self.expect("-", True)
        argv_file, cfgf = self.td / "argv", self.td / "cfg-gen"
        os.environ["FAKE_ARGV"] = str(argv_file)
        os.environ["FAKE_CFG"] = str(cfgf)
        try:
            o = self.oracle("fail")
            lw = {"max_print_line": "1000000"}
            got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini", "t.tex"],
                               dict(tv, **lw), 60)
            a = argv_file.read_text().split("\0")
            i = a.index("-c")
            env = self.cfg(cfgf)["env"]
            want = _oracle.engine_env(dict(_oracle.oracle_tex_vars(), **lw))
            self.expect("run_engine: a genuine failure is rc 1, the engine reaches "
                        "the container after the nonce, timeout, supervisor and "
                        "configuration, and the engine's environment is exactly "
                        "the protocol's plus the caller's log width",
                        got[0] == 1 and a[i + 7] == _oracle.ENGINE_PDFTEX
                        and a[i + 5] == _oracle._SUPERVISOR_SRC
                        and a[i + 8:] == ["-ini", "t.tex"] and env == want,
                        f"{got!r} {a[i + 7:]} {sorted(set(env) ^ set(want))}")
            # the clock is a PARAMETER (gen_contract's second date, OPEN-128 (6))
            o = self.oracle("fail")
            o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini", "t.tex"],
                         tv, 60, clock="fixed:1790000000")
            env = self.cfg(cfgf)["env"]
            self.expect("run_engine(clock=fixed:1790000000) did not run under that "
                        "clock (SOURCE_DATE_EPOCH, FORCE_SOURCE_DATE, the shim's "
                        "LP_CLOCK_EPOCH)", env.get("SOURCE_DATE_EPOCH") == "1790000000"
                        and env.get("LP_CLOCK_EPOCH") == "1790000000"
                        and env.get("FORCE_SOURCE_DATE") == "1", repr(
                            {k: env.get(k) for k in ("SOURCE_DATE_EPOCH", "LP_CLOCK_EPOCH")}))
            # Run the in-container script itself (a fake `timeout` that drops
            # its options, an engine path that proves it ran): the script must
            # start the engine it was GIVEN, not a name of its own.
            tb = self.td / "tbin"
            tb.mkdir(exist_ok=True)
            (tb / "timeout").write_text('#!/bin/sh\nshift 3\nexec "$@"\n')
            (tb / "timeout").chmod(0o755)
            # python3 -I -c SUPERVISOR NONCE CONFIG ENGINE ARGS: run the engine
            (tb / "python3").write_text('#!/bin/sh\nshift 5\nexec "$@"\n')
            (tb / "python3").chmod(0o755)
            probe = tb / "given-engine"
            probe.write_text("#!/bin/sh\necho GIVEN-ENGINE-RAN \"$@\"\n")
            probe.chmod(0o755)
            r = subprocess.run(
                ["sh", "-c", a[i + 1], "sh", "N", "60", "SUP", "{}", str(probe), "x.tex"],
                capture_output=True, text=True,
                env=dict(os.environ, PATH=f"{tb}:/usr/bin:/bin"))
            self.expect("the in-container script runs the engine run_engine names",
                        "GIVEN-ENGINE-RAN x.tex" in r.stdout and "N=0" in r.stderr,
                        f"{r.stdout!r} {r.stderr!r}")
        finally:
            os.environ.pop("FAKE_ARGV", None)
            os.environ.pop("FAKE_CFG", None)
        # An engine the oracle does not run (named through _oracle's table,
        # not spelled here: check_oracle_pin scans this file); a variable
        # that is not TeX-shaping; a TeX-shaping one that differs from the
        # protocol's (only the log width and the clock may differ).
        not_run = sorted(_oracle.TEX_ENGINE_BINARIES - set(_oracle.ENGINES))[0]
        for bad_engine, bad_vars in ((not_run, tv),
                                     (_oracle.ENGINE_PDFTEX, dict(tv, PATH="/host/bin")),
                                     (_oracle.ENGINE_PDFTEX, dict(tv, openin_any="a")),
                                     (_oracle.ENGINE_PDFTEX, dict(tv, TMPDIR="/tmp")),
                                     (_oracle.ENGINE_PDFTEX,
                                      dict(tv, TEXMFVAR=str(self.workroot / "tv")))):
            o = self.oracle("ok")
            try:
                o.run_engine(self.workroot, bad_engine, ["t.tex"], bad_vars, 60)
                self.expect(f"run_engine accepted engine {bad_engine!r} with "
                            f"variables {sorted(set(bad_vars.items()) - set(tv.items()))}",
                            False)
            except _oracle.OracleError:
                self.expect("-", True)
        try:
            self.oracle("ok").image_command([_oracle.ENGINE_PDFLATEX, "t.tex"])
            self.expect("image_command started a TeX engine", False)
        except _oracle.OracleError:
            self.expect("-", True)
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
        """C-91 (OPEN-118 known limit (b)), OPEN-128: every GRADED run gets
        EXACTLY the protocol's environment, whoever calls the oracle and
        whatever the host or the caller exports: the image's environment,
        ORACLE_TEX_VARS, the fixed run variables (the private trees and
        TMPDIR at fixed paths on the run's own tmpfs, the hash seeds, the
        shim's view) and the protocol clock -- read back from the run's
        configuration (the env the supervisor passes verbatim)."""
        hostile = {"SOURCE_DATE_EPOCH": "1700000000", "openin_any": "a",
                   "openout_any": "a", "FORCE_SOURCE_DATE": "0",
                   "max_print_line": "1000", "TEXINPUTS": f"{self.workroot}/inp:",
                   "TMP": "/tmp", "TEMP": "/tmp", "LP_CLOCK_EPOCH": "1",
                   "LP_FS_ROOTS": "/", "LD_PRELOAD": "/x.so", "PYTHONHASHSEED": "7",
                   "JAVA_TOOL_OPTIONS": "-XX:+UsePerfData",
                   "TEXMFVAR": str(self.workroot / "host-tv"),
                   **KPATHSEA_HOSTILE}
        want = protocol_env()
        cfgf = self.td / "cfg-env"

        def check(label: str) -> None:
            if not cfgf.exists():
                self.expect(f"{label}: no run reached the container", False)
                return
            c = self.cfg(cfgf)
            got = c["env"]
            diff = sorted(k for k in set(got) | set(want) if got.get(k) != want.get(k))
            self.expect(f"{label}: the engine's environment is not EXACTLY the "
                        f"protocol's (C-91, OPEN-128)", not diff,
                        repr({k: (got.get(k), want.get(k)) for k in diff[:6]}))
            self.expect(f"{label}: the supervisor does not create the run's private "
                        f"trees and TMPDIR before the engine starts (C-93)",
                        set(_oracle.FIXED_RUN_DIRS) <= set(c.get("mkdirs", [])),
                        repr(c.get("mkdirs")))
            self.expect(f"{label}: the engine runs without the pinned shim "
                        f"preloaded (OPEN-128)",
                        c.get("shim") == f"{_oracle.SHIM_DIR}/"
                        f"{_oracle.shim_name(_oracle.ARCH_OF_RECORD)}"
                        and c.get("mark") == _oracle.SHIM_MARK_DIR, repr(c.get("shim")))
            cfgf.unlink()

        saved = {k: os.environ.get(k) for k in list(hostile) + ["FAKE_CFG", "TMPDIR",
                                                                  "TEXMFHOME"]}
        os.environ["FAKE_CFG"] = str(cfgf)
        try:
            # (1) the Python API: a caller dict carrying the hostile values.
            o = self.oracle("ok")
            o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                           dict(self.tv(), **hostile), 60)
            check("ContainerOracle.run_pdflatex with a hostile caller dict")
            # (2) a caller with no TeX variable at all: the oracle supplies them.
            o = self.oracle("ok")
            o.run_pdflatex(self.workroot, ["t.tex"], {}, 60)
            check("ContainerOracle.run_pdflatex with an empty caller dict")
            # (3) the shim, under a hostile HOST environment.
            os.environ.update(hostile, TEXMFHOME=str(self.workroot / "host-th"),
                              TMPDIR="/tmp")
            cwd = os.getcwd()
            os.chdir(self.workroot)
            try:
                self.oracle("ok")
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
            self.expect(f"the shim under a hostile host environment exited {rc}", rc == 0)
            check("the _oracle.py pdflatex shim (the shell graders' path)")
            for k in list(hostile) + ["TEXMFHOME", "TMPDIR"]:
                os.environ.pop(k, None)
            # (4) the retired native backend: LP_ORACLE_IN_IMAGE is refused by
            # get_oracle and by the shim (INFRA_RC), never graded inside.
            os.environ["LP_ORACLE_IN_IMAGE"] = _oracle.IMAGE
            _oracle._ORACLE = None
            try:
                _oracle.get_oracle()
                self.expect("get_oracle() graded with LP_ORACLE_IN_IMAGE set (the "
                            "retired native backend, ADR-015 E15)", False)
            except _oracle.OracleError:
                self.expect("-", True)
            os.chdir(self.workroot)
            try:
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
                os.environ.pop("LP_ORACLE_IN_IMAGE", None)
            self.expect(f"the shim with LP_ORACLE_IN_IMAGE set exited {rc}, not "
                        f"INFRA_RC (ADR-015 E15)", rc == _oracle.INFRA_RC)
            # (5) check_apply_fixes_roundtrip.pdflatex_ok, a grader that
            # passed `dict(os.environ)` until C-91.
            import check_apply_fixes_roundtrip as rt
            self.oracle("ok")
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            self.expect(f"pdflatex_ok did not grade ({got!r})", got is not None)
            check("check_apply_fixes_roundtrip.pdflatex_ok")
        finally:
            _oracle._ORACLE = None
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        # (6) the oracle's own values: the fixed paths are the container's
        # (never a host path) and every writable kpathsea tree is private
        self.expect("the fixed run variables no longer make every writable "
                    "kpathsea tree (TEXMFHOME/TEXMFVAR/TEXMFCONFIG) private to the "
                    "run's tmpfs, or TMPDIR/TMP/TEMP/java's derived from one "
                    "directory there (C-91, C-93, OPEN-128)",
                    set(_oracle.FIXED_TREES) == {"TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG"}
                    and all(v.startswith(_oracle.PRIVATE_ROOT + "/")
                            for v in _oracle.FIXED_TREES.values())
                    and all(_oracle.FIXED_RUN_VARS[k] == _oracle.FIXED_TMP
                            for k in ("TMPDIR", "TMP", "TEMP"))
                    and _oracle.FIXED_RUN_VARS["JAVA_TOOL_OPTIONS"]
                    == _oracle.java_tool_options(_oracle.FIXED_TMP)
                    and _oracle.PRIVATE_ROOT.startswith("/tmp/"))
        self.expect("the protocol's clock is not a fixed one, or graded_env does "
                    "not impose it (ADR-015 E10)",
                    _oracle.PROTOCOL_CLOCK.startswith(_oracle.CLOCK_PREFIX)
                    and protocol_env().get("LP_CLOCK_EPOCH") == str(_oracle.PROTOCOL_EPOCH)
                    and protocol_env().get("SOURCE_DATE_EPOCH") == str(_oracle.PROTOCOL_EPOCH)
                    and protocol_env().get("FORCE_SOURCE_DATE") == "1")
        # (7) the shell side: oracle_setup routes every run through the shim,
        # and refuses the retired native backend
        osh = self.repo / "scripts/tools/_oracle.sh"
        py = str(self.repo / "scripts/tools/_oracle.py")
        stub = ('python3() { case "$2" in '
                'version) echo "pdfTeX 3.141592653-2.6-1.40.29" ;; '
                f'workroot) echo "{self.td}/wr" ;; esac; }}; ')
        env = {k: v for k, v in os.environ.items() if k != "LP_ORACLE_IN_IMAGE"}
        env.update(ROOT=str(self.repo), TEX_TIMEOUT="30")
        p = subprocess.run(
            ["bash", "-c", stub + f'source "{osh}"; oracle_setup t 1; '
             'printf "%s\\n" "$ORACLE_BACKEND" "$ORACLE_TIMEOUT_INSIDE" '
             '"${PDFLATEX[@]}"'], capture_output=True, text=True, env=env)
        got = p.stdout.split("\n")
        self.expect("_oracle.sh does not run every grader's pdflatex through the "
                    "_oracle.py shim", got[:6] == ["container", "1", "python3", py,
                                                   _oracle.SHIM_COMMAND, "--timeout"],
                    repr(got[:6]) + p.stderr[-200:])
        p = subprocess.run(
            ["bash", "-c", stub + f'source "{osh}"; oracle_setup t 1; echo GRADING'],
            capture_output=True, text=True, env=dict(env, LP_ORACLE_IN_IMAGE="x"))
        self.expect("_oracle.sh with LP_ORACLE_IN_IMAGE set still grades (the "
                    "retired native branch, ADR-015 E15)",
                    p.returncode == 2 and "GRADING" not in p.stdout,
                    f"rc {p.returncode} {p.stdout[-80:]!r}")
        # (8) image_command (gen_contract.py's non-TeX commands) starts no
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

    # --------------------------------------------- the ONE launch definition
    def launch_definition(self) -> None:
        """ADR-015 E15, OPEN-128 (4): every container the oracle starts is
        launch_argv's, with exactly its flags, and mounts only the work root's
        paths; the session probe checks the container it describes. Read back
        from the fake docker's calls."""
        calls = self.td / "calls"
        calls.write_text("")
        os.environ["FAKE_CALLS"] = str(calls)
        try:
            o = self.oracle("okpdf")
            o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
            o.image_command(["kpsewhich", "article.cls"], cwd=self.workroot)
            (self.workroot / "rmme.txt").write_text("x")
            o.remove([self.workroot / "rmme.txt"])
            p = self.bare()
            os.environ["FAKE_PLAN"] = "ok"
            p.fingerprint()
        except _oracle.OracleError as e:
            self.expect("the oracle refused a protocol run in launch_definition",
                        False, str(e)[:200])
        finally:
            os.environ.pop("FAKE_CALLS", None)
        runs = [c.split("\0") for c in calls.read_text().splitlines()
                if c.split("\0")[:1] == ["run"]]
        kinds = sorted({r[r.index("--entrypoint") + 1] for r in runs if "--entrypoint" in r})
        self.expect(f"the oracle's containers are not one launch definition: saw "
                    f"entry points {kinds}, want sh (engine), python3 (probe), "
                    f"kpsewhich (image command), rm (removal)",
                    kinds == ["kpsewhich", "python3", "rm", "sh"], repr(kinds))
        lim, mem = str(_oracle.PIDS_LIMIT), _oracle.MEMORY_LIMIT
        want_pairs = [("--pull", "never"), ("--pids-limit", lim), ("--memory", mem),
                      ("--memory-swap", mem), ("--tmpfs", f"/tmp:{_oracle.TMPFS_OPTIONS}"),
                      ("--network", "none"), ("--hostname", _oracle.ORACLE_HOSTNAME),
                      ("--user", FAKE_USER),
                      ("--platform", _oracle.PLATFORMS[_oracle.ARCH_OF_RECORD]),
                      ("-e", "HOME=/tmp")]
        for r in runs:
            head = r[:r.index("--entrypoint")] if "--entrypoint" in r else r
            pairs = list(zip(head, head[1:]))
            miss = [pp for pp in want_pairs if pp not in pairs]
            flags = [f for f in ("--rm", "--init", "--read-only") if f not in head]
            mounts = [head[k + 1] for k in range(len(head) - 1) if head[k] == "-v"]
            outside = [m for m in mounts
                       if not str(Path(m.split(":")[0]).resolve()).startswith(
                           str(self.workroot))]
            self.expect(f"a container of the oracle lacks {miss + flags} or mounts "
                        f"{outside} from outside the work root (ADR-015 E15: one "
                        f"launch definition, OPEN-126: read-only, non-root)",
                        not miss and not flags and not outside, " ".join(head)[:300])
        eng = [r for r in runs if "--entrypoint" in r and r[r.index("--entrypoint") + 1] == "sh"]
        ok = bool(eng) and all(
            any(m.endswith(":" + _oracle.RUN_DIR) for m in r)
            and any(m.endswith(":" + _oracle.SHIM_DIR + ":ro") for m in r)
            and r[r.index("-w") + 1] == _oracle.RUN_DIR for r in eng)
        self.expect("an engine run's directory is not mounted at the fixed RUN_DIR "
                    "(with -w RUN_DIR), or the shim not read-only at SHIM_DIR "
                    "(OPEN-128 (1): the cwd a document reads is fixed)", ok)
        # The session probe refuses each defect of the container it describes.
        good_cenv = self.td / "cenv-good"
        good_cenv.write_text("\0".join(f"{k}={v}" for k, v in dict(
            _oracle.IMAGE_ENV, HOSTNAME=_oracle.ORACLE_HOSTNAME).items()))
        for label, envs, want_ok in (
                ("the protocol's container", {}, True),
                ("another HOSTNAME", {"FAKE_CENV": ("HOSTNAME", "abc")}, False),
                ("an extra variable", {"FAKE_CENV": ("shell_escape", "t")}, False),
                ("another shim", {"FAKE_SHIM": "0" * 64}, False),
                ("a writable tree", {"FAKE_RO": json.dumps(
                    {"euid": 501, "texmfroot": "/t", "root_ro": True, "tree_ro": False})},
                 False),
                ("a root engine", {"FAKE_RO": json.dumps(
                    {"euid": 0, "texmfroot": "/t", "root_ro": True, "tree_ro": True})},
                 False),
                ("an x86_64 tree", {"FAKE_FP": json.dumps(record_fp("x86_64"))}, False),
                ("another fmt", {"FAKE_FP": json.dumps(dict(record_fp(), fmt_sha256="0" * 64))},
                 False),
                ("a failing probe", {"FAKE_PROBE_RC": "3"}, False)):
            saved = {k: os.environ.get(k) for k in ("FAKE_CENV", "FAKE_SHIM", "FAKE_RO",
                                                     "FAKE_FP", "FAKE_PROBE_RC")}
            try:
                for k, v in envs.items():
                    if k == "FAKE_CENV":
                        f = self.td / "cenv-bad"
                        f.write_text(good_cenv.read_text() + "\0" + f"{v[0]}={v[1]}")
                        os.environ[k] = str(f)
                    else:
                        os.environ[k] = v
                try:
                    self.bare().session_probe()
                    ok = True
                except _oracle.OracleError:
                    ok = False
            finally:
                for k, v in saved.items():
                    if v is None:
                        os.environ.pop(k, None)
                    else:
                        os.environ[k] = v
            self.expect(f"the session probe {'refused' if want_ok else 'accepted'} "
                        f"{label}", ok == want_ok)
        # A work root the container does not see (the nonce does not round-trip).
        o = self.bare()
        o.workroot = self.td / "elsewhere"
        o.workroot.mkdir(exist_ok=True)
        real = _oracle.launch_argv
        _oracle.launch_argv = lambda *a, **k: [x.replace(str(o.workroot), "/nowhere")
                                               for x in real(*a, **k)]
        try:
            o.session_probe()
            self.expect("the session probe accepted a work root the container does "
                        "not see (the nonce did not round-trip)", False)
        except (_oracle.OracleError, OSError, TypeError):
            self.expect("-", True)
        finally:
            _oracle.launch_argv = real
        # The repository's shim must be the pinned one before it is installed.
        real_dir = _oracle.SHIM_SRC_DIR
        bad = self.td / "bad-shim"
        bad.mkdir(exist_ok=True)
        for arch in _oracle.SHIM_SHA256:
            (bad / _oracle.shim_name(arch)).write_bytes(b"not the pinned shim")
        _oracle.SHIM_SRC_DIR = bad
        try:
            self.bare()._install_shim()
            self.expect("_install_shim installed a shim whose sha256 is not "
                        "SHIM_SHA256", False)
        except _oracle.OracleError:
            self.expect("-", True)
        finally:
            _oracle.SHIM_SRC_DIR = real_dir
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

    def identity_and_readonly(self) -> None:
        """OPEN-126, OPEN-128 (3). (a) ADR-015 E2: an oracle on another
        architecture than ARCH_OF_RECORD refuses to grade (a measurement may
        run there, tagged); two oracle blocks that differ in architecture,
        tree or CLOCK are refused as incomparable, and so is a measurement
        block. (b) A writable TeX tree or a root engine is refused."""
        rec = _oracle.ARCH_OF_RECORD
        for arch in sorted(_oracle.TREE_FINGERPRINTS):
            fp = record_fp(arch)
            for meas in (False, True):
                try:
                    _oracle._check_fingerprint(fp, "test", measurement=meas)
                    ok = True
                except _oracle.OracleError:
                    ok = False
                self.expect(f"_check_fingerprint {'refused' if (arch == rec or meas) else 'accepted'} "
                            f"an oracle on {arch} (architecture of record {rec}, "
                            f"measurement {meas})", ok == (arch == rec or meas))
        a = dict(_oracle.TREE_FINGERPRINTS[rec], arch=rec, image=_oracle.IMAGE,
                 clock=_oracle.PROTOCOL_CLOCK)
        for label, b, want in (
                ("the same oracle", dict(a), True),
                ("another architecture", dict(a, arch="x86_64"), False),
                ("no architecture", {k: v for k, v in a.items() if k != "arch"}, False),
                ("another format", dict(a, fmt_sha256="0" * 64), False),
                ("another fixed clock", dict(a, clock="fixed:1790000000"), False),
                ("the legacy real clock", dict(a, clock="real"), False),
                ("no clock", {k: v for k, v in a.items() if k != "clock"}, False),
                ("a measurement", dict(a, entry="measure"), False),
                ("a measurement-only block", dict(a, measurement_only=True), False)):
            try:
                _oracle.require_same_oracle(b, a, "test")
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"require_same_oracle {'refused' if want else 'accepted'} "
                        f"{label}", ok == want)
        base = {"euid": 501, "texmfroot": "/t", "root_ro": True, "tree_ro": True}
        for label, probe, want in (
                ("a read-only tree, unprivileged", base, True),
                ("a writable tree", dict(base, tree_ro=False), False),
                ("a writable root filesystem", dict(base, root_ro=False), False),
                ("an unreadable mount table", dict(base, tree_ro=None), False),
                ("a root engine", dict(base, euid=0), False)):
            try:
                _oracle.check_readonly(probe, "test")
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"check_readonly {'refused' if want else 'accepted'} {label}",
                        ok == want)
        for c, want in ((_oracle.PROTOCOL_CLOCK, True), ("fixed:0", True),
                        ("real", False), ("forced", False), ("fixed:", False),
                        ("fixed:-1", False), ("fixed:1e9", False)):
            try:
                _oracle.clock_vars(c)
                ok = True
            except _oracle.OracleError:
                ok = False
            self.expect(f"clock_vars {'refused' if want else 'accepted'} {c!r} "
                        f"(only a fixed clock is a run's clock, OPEN-128)", ok == want)

    def argv_checks(self) -> None:
        """C-91 review round 5. A graded run's ARGV is an allow-list, on
        every entry point: the round-5 review MEASURED `-cnf-line=openout_any=a`
        (an \\openout to /tmp written, rc 0) and `-shell-escape` /
        `-cnf-line=shell_escape=t` (\\pdfshellescape=1) passing through the
        shim and run_pdflatex."""
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
        finally:
            os.chdir(cwd)
            _oracle._ORACLE = None
        o = self.oracle("ok")
        try:
            r = o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
            self.expect("run_to_fixpoint no longer runs the protocol's argv", r.rc == 0)
        except _oracle.OracleError as e:
            self.expect("run_to_fixpoint refused the protocol's own argv", False, str(e))
        tv = _oracle.oracle_tex_vars()
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
        _oracle._ORACLE = None

    # ------------------------------------------ the measurement entry point
    def measurement(self) -> None:
        """ADR-015 E7, OPEN-128 (2): `measure` runs the pinned engine through
        the same launch definition with terminal input, an explicit
        architecture and an explicit clock; its result is tagged (entry
        measure; measurement_only off the architecture of record) and never
        compared with a grade; its environment is an allow-list too."""
        cfgf = self.td / "cfg-measure"
        argv_file = self.td / "argv-measure"
        os.environ["FAKE_CFG"] = str(cfgf)
        os.environ["FAKE_ARGV"] = str(argv_file)
        try:
            for arch in (_oracle.ARCH_OF_RECORD, "x86_64"):
                o = self.oracle("nobanner")   # a measurement needs no banner
                try:
                    r = o.measure(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini"],
                                  stdin=b"\\relax\n", env={"SOURCE_DATE_EPOCH": "1788076260"},
                                  arch=arch, readings=[(1788076260, 123456)])
                    c = self.cfg(cfgf)
                    a = argv_file.read_text().split("\0")
                    pv = r.provenance
                    ok = (r[0] == 1 and pv.get("entry") == "measure"
                          and pv.get("measurement_only") is (arch != _oracle.ARCH_OF_RECORD)
                          and pv.get("arch") == arch
                          and c["env"].get("LP_CLOCK") == "1788076260.123456"
                          and c["env"].get("SOURCE_DATE_EPOCH") == "1788076260"
                          and c.get("stdin") == _oracle.IN_DIR + "/stdin"
                          and ("--platform", _oracle.PLATFORMS[arch]) in list(zip(a, a[1:]))
                          and c["shim"].endswith(_oracle.shim_name(arch)))
                    self.expect(f"measure on {arch}: the run, its tag, its clock "
                                f"readings, its terminal input or its platform are "
                                f"wrong", ok, f"{r[0]} {pv} {c.get('stdin')}")
                    try:
                        _oracle.require_same_oracle(pv, _oracle.ContainerOracle.provenance(o),
                                                    "test")
                        self.expect(f"require_same_oracle accepted a measurement on "
                                    f"{arch} as a grade", False)
                    except _oracle.OracleError:
                        self.expect("-", True)
                except _oracle.OracleError as e:
                    self.expect(f"measure on {arch} was refused", False, str(e)[:200])
            # clock "real" (a control run): no fixed clock reaches the engine
            o = self.oracle("ok")
            o.measure(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini"], clock="real",
                      unset=("SOURCE_DATE_EPOCH", "FORCE_SOURCE_DATE"))
            env = self.cfg(cfgf)["env"]
            self.expect("measure(clock='real') still fixed the clock",
                        not {"LP_CLOCK_EPOCH", "SOURCE_DATE_EPOCH",
                             "FORCE_SOURCE_DATE"} & set(env), repr(sorted(env)))
            # its allow-lists
            for kw, what in (({"env": {"shell_escape": "t"}}, "shell_escape"),
                             ({"env": {"TEXMFVAR": "/x"}}, "a TEXMF tree"),
                             ({"env": {"LD_PRELOAD": "/x"}}, "LD_PRELOAD"),
                             ({"unset": ("openin_any",)}, "an unset of openin_any"),
                             ({"arch": "riscv64"}, "an unknown architecture"),
                             ({"clock": "forced"}, "a legacy clock")):
                o = self.oracle("ok")
                try:
                    o.measure(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini"], **kw)
                    self.expect(f"measure accepted {what} (ADR-015 E7: the same "
                                f"env discipline as grading)", False)
                except _oracle.OracleError:
                    self.expect("-", True)
            # the CLI form (the migration of the spike's recipe)
            os.chdir(self.workroot)
            try:
                self.oracle("ok")
                rec = self.td / "measure.json"
                rc = _silenced(_oracle.main, ["measure", "--arch", "arm64", "--work",
                                              str(self.workroot), "--clock-readings",
                                              "1788076260.123456", "--record", str(rec),
                                              "--", _oracle.ENGINE_PDFTEX, "-ini"])
                got = json.loads(rec.read_text()) if rec.exists() else {}
                self.expect(f"`_oracle.py measure` exited {rc} or recorded no "
                            f"measurement provenance",
                            rc == 0 and got.get("provenance", {}).get("entry") == "measure",
                            repr(got)[:200])
            finally:
                os.chdir(self.repo)
        finally:
            os.environ.pop("FAKE_CFG", None)
            os.environ.pop("FAKE_ARGV", None)
            _oracle._ORACLE = None

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
                        c.argv_checks, c.launch_definition,
                        c.identity_and_readonly, c.measurement, c.shell_grader):
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
