#!/usr/bin/env python3
"""OPEN-034 sample-2 re-grade with the AUTHORITATIVE oracle.

The sweep's grader prompt said "stop early if a pass exits nonzero" — the
exact one-pass defect the repo's run_to_fixpoint docstring was written to
correct (natbib papers fail pass 1 and compile on pass 2). This mirrors
scripts/tools/diff_real_roots.py:run_to_fixpoint byte-for-byte:
  <=3 passes, -halt-on-error KEPT, break on first rc 0, then ONE CONFIRMING
  pass whose rc is authoritative.
"""
import json, os, shutil, subprocess, sys, tempfile, pathlib

CORP = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Archives/LP_v24_FULL_BACKUP_20250716_165548/corpus/papers"
CLI = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/_build/default/latex-parse/src/validators_cli.exe"
MAX_PASSES, TIMEOUT = 3, 300

ENV = dict(os.environ)
ENV.update({"TEXMFVAR": "/tmp/regrade-texmfvar", "openout_any": "p", "openin_any": "p"})


def run_to_fixpoint(work, toplevel):
    rc, passes = 1, 0
    while passes < MAX_PASSES:
        try:
            t = subprocess.run(["pdflatex",
                                "-interaction=nonstopmode", "-halt-on-error", toplevel],
                               cwd=work, env=ENV, capture_output=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return -1, passes + 1
        rc, passes = t.returncode, passes + 1
        if rc == 0:
            break
    if rc != 0:
        return rc, passes
    try:
        confirm = subprocess.run(["pdflatex",
                                  "-interaction=nonstopmode", "-halt-on-error", toplevel],
                                 cwd=work, env=ENV, capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return -1, passes + 1
    return confirm.returncode, passes + 1


def first_error(work, toplevel):
    log = pathlib.Path(work) / (pathlib.Path(toplevel).stem + ".log")
    if not log.exists():
        return ""
    for line in log.read_text(errors="replace").splitlines():
        if line.startswith("!"):
            return line[:160]
    return ""


def grade(aid, top):
    pkg = pathlib.Path(CORP) / aid
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        rc, passes = run_to_fixpoint(str(work), top)
        pdf = (work / (pathlib.Path(top).stem + ".pdf")).exists()
        err = first_error(str(work), top)
    if rc == -1:
        return dict(arxiv_id=aid, toplevel=top, cell="ungraded-infra",
                    pdflatex_verdict="timeout", passes=passes)
    compiles = (rc == 0 and pdf)
    c = subprocess.run([CLI, "--compile-check", str(pkg / top)],
                       capture_output=True, text=True, timeout=TIMEOUT)
    cli_ready = (c.returncode == 0)
    reasons = [l.strip() for l in (c.stdout + c.stderr).splitlines()
               if l.strip().startswith(("T0", "T2", "T3", "T4", "T5", "MODEL-NOT"))]
    cell = ("true-READY" if compiles and cli_ready else
            "false-NOT-READY" if compiles and not cli_ready else
            "FALSE-READY" if not compiles and cli_ready else "true-NOT-READY")
    return dict(arxiv_id=aid, toplevel=top, cell=cell,
                pdflatex_verdict="compiles" if compiles else "fails",
                pdflatex_rc=rc, passes=passes, first_error=err,
                cli_rc=c.returncode, cli_reasons=reasons[:4])


if __name__ == "__main__":
    todo = [l.split("\t") for l in open(sys.argv[1]).read().splitlines() if l.strip()]
    out_path = sys.argv[2]
    rows = []
    for i, (aid, top) in enumerate(todo, 1):
        r = grade(aid, top)
        rows.append(r)
        print(f"[{i}/{len(todo)}] {aid} {r['cell']} ({r['pdflatex_verdict']}, "
              f"{r.get('passes','?')}p) {r.get('first_error','')[:60]}", flush=True)
        pathlib.Path(out_path).write_text(json.dumps(rows, indent=1) + "\n")
    counts = {}
    for r in rows:
        counts[r["cell"]] = counts.get(r["cell"], 0) + 1
    print("COUNTS:", json.dumps(counts))
