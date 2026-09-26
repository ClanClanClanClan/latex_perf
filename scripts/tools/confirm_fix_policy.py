#!/usr/bin/env python3
"""Confirm the fix policy on an UNTOUCHED window: breaks AND meaning (OPEN-112).

    python3 scripts/tools/confirm_fix_policy.py --offset 2600 --n 119 --out conf.json

Three arms per paper, each on a fresh copy of the package, fixer applied to
every .tex (the gen_apply_fixes_real_differential recipe), compiled with
run_to_fixpoint at the pinned engine:

  CTRL     pristine                       (must be rc 0, else the paper is excluded)
  ALL      --apply-fixes-all              (the fixer as it was before OPEN-112)
  DEFAULT  --apply-fixes                  (the shipped allow-list)

For each fixed arm: rc and first error (the BREAK question), and the pdftotext
word diff against CTRL (the MEANING question -- OPEN-110 showed `preserved`
means rc 0, not unchanged in meaning), plus which rules applied edits
(LP_FIX_TRACE). A fixer crash or timeout raises: never graded as "no edits"
(C-70).
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse, collections, difflib, hashlib, json, os, pathlib, re, shutil
import subprocess, tempfile
from concurrent.futures import ThreadPoolExecutor

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/tools"))
from diff_real_roots import PIN, build_frame, run_to_fixpoint  # noqa: E402
from gen_apply_fixes_real_differential import first_error  # noqa: E402

CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"
WORD = re.compile(r"\S+")
ARMS = {"CTRL": None, "ALL": "--apply-fixes-all", "DEFAULT": "--apply-fixes"}


def tex_env(td):
    return dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                TEXMFVAR=str(pathlib.Path(td) / "tv"),
                openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")


def arm(pkg, top, flag, timeout):
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        rules = collections.Counter()
        if flag:
            trace = pathlib.Path(td) / "trace.tsv"
            env = dict(os.environ, LP_FIX_TRACE=str(trace))
            for tex in sorted(work.rglob("*.tex")):
                before = tex.read_bytes()
                try:
                    r = subprocess.run([str(CLI), flag, str(tex)],
                                       capture_output=True, env=env, timeout=timeout)
                except subprocess.TimeoutExpired:
                    raise RuntimeError(f"fixer timed out on {tex} ({flag})")
                if r.returncode not in (0, 1):
                    raise RuntimeError(f"fixer crashed (exit {r.returncode}) on "
                                       f"{tex} ({flag}): {r.stderr[-300:]!r}")
                if r.stdout and r.stdout != before:
                    tex.write_bytes(r.stdout)
            if trace.is_file():
                for line in trace.read_text(errors="replace").splitlines():
                    parts = line.split("\t")
                    if len(parts) >= 2:
                        rules[parts[1]] += 1
        rc, _ = run_to_fixpoint(work, top, tex_env(td), timeout)
        pdf = work / (pathlib.Path(top).stem + ".pdf")
        text = None
        if rc == 0 and pdf.is_file():
            text = subprocess.run(["pdftotext", "-enc", "UTF-8", str(pdf), "-"],
                                  capture_output=True).stdout.decode("utf-8", "replace")
        return {"rc": rc, "first_error": "" if rc == 0 else first_error(work, top),
                "rules": dict(rules), "text": text}


def hunks(a, b, ctx=6, cap=15):
    wa, wb = WORD.findall(a), WORD.findall(b)
    ops = [o for o in difflib.SequenceMatcher(None, wa, wb, autojunk=False).get_opcodes()
           if o[0] != "equal"]
    return len(ops), [{"before": " ".join(wa[max(0, i1 - ctx):i2 + ctx]),
                       "after": " ".join(wb[max(0, j1 - ctx):j2 + ctx])}
                      for _, i1, i2, j1, j2 in ops[:cap]]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offset", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--timeout", type=int, default=240)
    ns = ap.parse_args()
    root = pathlib.Path(os.environ["LP_REAL_CORPUS"]).resolve()
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0]
    if PIN not in banner:
        sys.exit(f"FATAL: engine skew {banner!r}")
    for k in ("LP_FIX_ONLY", "LP_FIX_EXCLUDE", "LP_FIX_TRACE", "L0_APPLY_FIXES"):
        if os.environ.get(k):
            sys.exit(f"FATAL: {k} set in the caller's environment")
    frame = build_frame(root)
    ordered = sorted(frame, key=lambda r: hashlib.sha256(r["arxiv_id"].encode()).hexdigest())
    window = ordered[ns.offset:ns.offset + ns.n]
    if len(window) < ns.n:
        sys.exit(f"FATAL: frame has {len(ordered)} papers; window overruns it")

    def one(rec):
        pkg, top = root / rec["arxiv_id"], rec["toplevel"]
        row = {"arxiv_id": rec["arxiv_id"], "rank": ordered.index(rec)}
        ctrl = arm(pkg, top, None, ns.timeout)
        row["CTRL"] = {"rc": ctrl["rc"], "first_error": ctrl["first_error"]}
        if ctrl["rc"] != 0:
            row["cell"] = "excluded-did-not-compile"
            return row
        row["cell"] = "measured"
        for name in ("ALL", "DEFAULT"):
            a = arm(pkg, top, ARMS[name], ns.timeout)
            rec_a = {"rc": a["rc"], "first_error": a["first_error"], "rules": a["rules"]}
            if a["text"] is not None and ctrl["text"] is not None:
                rec_a["word_hunks_total"], rec_a["word_hunks"] = hunks(ctrl["text"], a["text"])
            row[name] = rec_a
        return row

    rows, errors = [], []
    with ThreadPoolExecutor(ns.jobs) as ex:
        futs = [(rec, ex.submit(one, rec)) for rec in window]
        for i, (rec, fu) in enumerate(futs, 1):
            try:
                rows.append(fu.result())
            except Exception as e:  # recorded AND fails the run
                errors.append({"arxiv_id": rec["arxiv_id"], "error": repr(e)})
            print(f"[{i}/{len(futs)}] {rec['arxiv_id']}", flush=True)
    m = [r for r in rows if r["cell"] == "measured"]
    summ = {"sampled": len(rows), "compiled_pristine": len(m)}
    for name in ("ALL", "DEFAULT"):
        summ[f"{name}_broken"] = sum(1 for r in m if r[name]["rc"] != 0)
        summ[f"{name}_text_changed"] = sum(1 for r in m if r[name]["rc"] == 0
                                           and r[name].get("word_hunks_total", 0) > 0)
        summ[f"{name}_papers_edited"] = sum(1 for r in m if r[name]["rules"])
    prov = {"frame_size": len(frame), "offset": ns.offset, "n": ns.n,
            "selection": "sha256(arxiv_id) ascending", "engine": banner,
            "cli_sha256": hashlib.sha256(CLI.read_bytes()).hexdigest(),
            "src_tree_sha": subprocess.run(
                ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
                cwd=REPO, capture_output=True, text=True).stdout.strip(),
            "measured_at_sha": subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                                              capture_output=True, text=True).stdout.strip()}
    pathlib.Path(ns.out).write_text(json.dumps(
        {"provenance": prov, "summary": summ, "errors": errors, "rows": rows},
        indent=1, ensure_ascii=False))
    print(json.dumps(summ, indent=1))
    print("SENTINEL_DONE", flush=True)
    return 2 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
