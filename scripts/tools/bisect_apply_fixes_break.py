#!/usr/bin/env python3
"""Isolate WHICH fix producer turns a compiling real paper into a broken one.

    python3 scripts/tools/bisect_apply_fixes_break.py 2507.05786v1 [more ids...]

WHY THIS IS A COMMITTED TOOL AND NOT A ONE-OFF. PROJECT_STATE's OPEN-076
records the trap this exists to avoid: "first-error attribution in a multi-rule
fixer is a HYPOTHESIS until bisected." A previous session read the first
pdflatex error, named a plausible rule, and was wrong — withdrawing TYPO-028
later cleared breaks that had been attributed to CHEM-005/SCRIPT-001 and
OPEN-072. Reading the error tells you the SYMPTOM; only isolation tells you the
CAUSE. Doing that by hand is slow enough that people skip it, so it is a script.

METHOD, and each step exists because skipping it produced a wrong answer once:

  1. Copy the tree to /private/tmp. NEVER compile in the corpus: pdflatex
     writes .aux/.log next to the source and would mutate the measurement basis.
  2. SNAPSHOT the shipped file set before compiling, and afterwards delete only
     what appeared. Do NOT glob *.pdf -- that deletes FIGURES and manufactures a
     break (measured: 2507.04187v1 "reported broken" with
     `File 'figs/ppo_motivation.pdf' not found`, entirely the harness's doing).
  3. Confirm the paper compiles BEFORE (rc 0) and breaks AFTER the full fixer
     (rc != 0). A paper that fails step 3 is not evidence of anything.
  4. CHEAP PASS: apply each firing rule ALONE and keep only those that change
     bytes. Compiling every firing rule is ~40 pdflatex runs per paper; the
     byte filter typically cuts that to under ten.
  5. SUFFICIENCY: apply each byte-changing rule alone and compile. A rule that
     alone takes rc 0 -> rc != 0 is sufficient.
  6. NECESSITY: apply every firing rule EXCEPT the candidate, to fixpoint, and
     compile. If the paper survives, the candidate is necessary too. A rule that
     is sufficient but NOT necessary means an interaction, which is a different
     finding and must be reported as one rather than rounded to a culprit.

Exit 0 always; this is an instrument, not a gate.
"""
import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from diff_real_roots import run_to_fixpoint, PIN  # noqa: E402

REPO = pathlib.Path(__file__).resolve().parents[2]
CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"
CORPUS = pathlib.Path(
    os.environ.get("LP_REAL_CORPUS", "")).expanduser()


def toplevel_of(pkg: pathlib.Path) -> str:
    """From arXiv's own 00README.json — never a \\documentclass scan, which a
    commented-out class fools (that IS the 2506.14914v1 defect)."""
    meta = json.loads((pkg / "00README.json").read_text())
    tops = [s["filename"] for s in meta.get("sources", [])
            if s.get("usage") == "toplevel"]
    return tops[0] if len(tops) == 1 else ""


def tex_env(td):
    return dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                TEXMFVAR=str(pathlib.Path(td) / "tv"),
                openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")


def first_error(work, toplevel):
    log = work / (pathlib.Path(toplevel).stem + ".log")
    if not log.is_file():
        return ""
    for raw in log.read_bytes().split(b"\n"):
        if raw.startswith(b"!"):
            return raw.decode("utf-8", "replace").strip()[:160]
    return ""


def firing_rules(work):
    ids = set()
    for tex in sorted(work.rglob("*.tex")):
        try:
            r = subprocess.run([str(CLI), str(tex)], capture_output=True,
                               timeout=120)
        except subprocess.TimeoutExpired:
            continue
        for line in r.stdout.decode("utf-8", "replace").splitlines():
            parts = line.split("\t")
            if len(parts) >= 2 and "-" in parts[0] and parts[0][0].isupper():
                ids.add(parts[0].strip())
    return sorted(ids)


def apply_rules(work, rules, timeout=120):
    """Apply the given rules (None = the DEFAULT fixer) to every .tex, to
    fixpoint over the rule list. Returns the list of files that changed."""
    changed = set()
    for _ in range(8):
        round_changed = False
        for tex in sorted(work.rglob("*.tex")):
            for rule in (rules if rules is not None else [None]):
                cmd = [str(CLI)]
                cmd += ["--apply-fixes"] if rule is None else \
                       ["--apply-fixes-for", rule]
                cmd += [str(tex)]
                before = tex.read_bytes()
                try:
                    r = subprocess.run(cmd, capture_output=True, timeout=timeout)
                except subprocess.TimeoutExpired:
                    continue
                if r.returncode in (0, 1) and r.stdout and r.stdout != before:
                    tex.write_bytes(r.stdout)
                    changed.add(str(tex.relative_to(work)))
                    round_changed = True
        if not round_changed:
            break
    return sorted(changed)


def trial(pkg, toplevel, rules, timeout=240):
    """Fresh copy -> compile -> apply -> recompile. Returns (rc0, rc1, err, changed)."""
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        env = tex_env(td)
        shipped = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        rc0, _ = run_to_fixpoint(work, toplevel, env, timeout)
        if rc0 != 0:
            return rc0, None, first_error(work, toplevel), []
        for q in sorted((x for x in work.rglob("*") if x.is_file()),
                        key=lambda x: -len(x.parts)):
            if q.relative_to(work) not in shipped:
                q.unlink(missing_ok=True)
        changed = apply_rules(work, rules)
        rc1, _ = run_to_fixpoint(work, toplevel, env, timeout)
        return rc0, rc1, first_error(work, toplevel), changed


def bisect(arxiv_id):
    pkg = CORPUS / arxiv_id
    top = toplevel_of(pkg)
    out = {"paper": arxiv_id, "toplevel": top}
    if not top:
        out["error"] = "no unique toplevel in 00README.json"
        return out

    rc0, rc1, err, changed = trial(pkg, top, None)
    out["rc_before"], out["rc_after_full_fixer"] = rc0, rc1
    out["first_error"] = err
    out["changed_files"] = changed
    if rc0 != 0:
        out["verdict"] = "EXCLUDED: does not compile before the fixer"
        return out
    if rc1 == 0:
        out["verdict"] = "NOT REPRODUCED: the full fixer does not break it"
        return out

    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        probe = pathlib.Path(td) / "w"
        shutil.copytree(pkg, probe)
        firing = firing_rules(probe)
    out["firing_rules"] = firing

    # 4. cheap pass — which rules change bytes at all
    byte_changing = []
    for rule in firing:
        with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
            w = pathlib.Path(td) / "w"
            shutil.copytree(pkg, w)
            if apply_rules(w, [rule]):
                byte_changing.append(rule)
    out["byte_changing_rules"] = byte_changing

    # 5. sufficiency
    sufficient = []
    for rule in byte_changing:
        _, rc, e, _ = trial(pkg, top, [rule])
        if rc not in (0, None):
            sufficient.append({"rule": rule, "first_error": e})
    out["sufficient"] = sufficient

    # 6. necessity — all firing rules EXCEPT the candidate
    necessary = []
    for s in sufficient:
        others = [r for r in firing if r != s["rule"]]
        _, rc, _, _ = trial(pkg, top, others)
        if rc == 0:
            necessary.append(s["rule"])
    out["necessary"] = necessary

    if len(sufficient) == 1 and necessary == [sufficient[0]["rule"]]:
        out["verdict"] = f"CULPRIT {sufficient[0]['rule']} (necessary AND sufficient)"
    elif sufficient:
        out["verdict"] = ("MULTIPLE or NON-NECESSARY: "
                          f"sufficient={[s['rule'] for s in sufficient]} "
                          f"necessary={necessary}")
    else:
        out["verdict"] = ("NO SINGLE RULE reproduces it — an INTERACTION. "
                          "Do not round this to a culprit.")
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("papers", nargs="+")
    ap.add_argument("--out", default="")
    ns = ap.parse_args()
    if not CLI.is_file():
        print(f"FATAL: {CLI} not built", file=sys.stderr)
        return 2
    if not CORPUS.is_dir():
        print("FATAL: LP_REAL_CORPUS unset or missing", file=sys.stderr)
        return 2
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0]
    if PIN not in banner:
        print(f"FATAL: engine skew: {banner!r} vs pinned {PIN!r}",
              file=sys.stderr)
        return 3
    results = []
    for p in ns.papers:
        r = bisect(p)
        results.append(r)
        print(f"\n=== {p} ===")
        for k in ("rc_before", "rc_after_full_fixer", "first_error",
                  "changed_files", "byte_changing_rules", "sufficient",
                  "necessary", "verdict"):
            if k in r:
                print(f"  {k}: {r[k]}")
        sys.stdout.flush()
    if ns.out:
        pathlib.Path(ns.out).write_text(json.dumps(results, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
