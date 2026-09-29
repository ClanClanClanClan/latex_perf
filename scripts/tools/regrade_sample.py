#!/usr/bin/env python3
"""OPEN-034 sample-2 re-grade with the AUTHORITATIVE oracle.

The sweep's grader prompt said "stop early if a pass exits nonzero" — the
exact one-pass defect the repo's run_to_fixpoint docstring was written to
correct (natbib papers fail pass 1 and compile on pass 2). This mirrors
scripts/tools/diff_real_roots.py:run_to_fixpoint byte-for-byte:
  <=3 passes, -halt-on-error KEPT, break on first rc 0, then ONE CONFIRMING
  pass whose rc is authoritative.
"""
import json, shutil, subprocess, sys, pathlib

CORP = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Archives/LP_v24_FULL_BACKUP_20250716_165548/corpus/papers"
CLI = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/_build/default/latex-parse/src/validators_cli.exe"
MAX_PASSES, TIMEOUT = 3, 300

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _oracle import get_oracle, job_output, pdf_written  # noqa: E402


def run_to_fixpoint(work, toplevel, env):
    """The recorded protocol, run by the ONE oracle: the pinned TeX Live image
    (ADR-012 decision 7). Superseded for sample 2 by
    `diff_real_roots.py --repass --results results_sample2.json
    --sample-offset 200`, which records per-row provenance."""
    r = get_oracle().run_to_fixpoint(pathlib.Path(work), toplevel, env, TIMEOUT,
                                     MAX_PASSES)
    return r.rc, r.passes


def first_error(work, toplevel):
    log = job_output(work, toplevel, ".log")  # pdfTeX's job name (C-95)
    if not log.exists():
        return ""
    for line in log.read_text(errors="replace").splitlines():
        if line.startswith("!"):
            return line[:160]
    return ""


# The reason filter over --compile-check output. It is a named function so that
# scripts/tools/check_compile_check_consumers.py imports THIS code rather than a
# hand copy of it (ADR-012 M0): the leading T0..T5 token is the contract.
REASON_PREFIXES = ("T0", "T2", "T3", "T4", "T5", "MODEL-NOT")


def reason_lines(out):
    return [l.strip() for l in out.splitlines()
            if l.strip().startswith(REASON_PREFIXES)]


def grade(aid, top):
    pkg = pathlib.Path(CORP) / aid
    with get_oracle().tempdir() as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        rc, passes = run_to_fixpoint(str(work), top, get_oracle().tex_env(td))
        pdf = pdf_written(work, top)  # pdfTeX's own report (C-97)
        err = first_error(str(work), top)
    if rc == -1:
        return dict(arxiv_id=aid, toplevel=top, cell="ungraded-infra",
                    pdflatex_verdict="timeout", passes=passes)
    compiles = (rc == 0 and pdf)
    c = subprocess.run([CLI, "--compile-check", str(pkg / top)],
                       capture_output=True, text=True, timeout=TIMEOUT)
    cli_ready = (c.returncode == 0)
    reasons = reason_lines(c.stdout + c.stderr)
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
