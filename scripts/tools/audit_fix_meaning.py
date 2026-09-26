#!/usr/bin/env python3
"""Does a fix rule change what a compiling paper SAYS? (OPEN-110, allow-list)

    python3 scripts/tools/audit_fix_meaning.py --out meaning.json [--k 5] [--jobs 6]

WHY. OPEN-110 measured that `preserved` (rc 0 after the fixer) is not
`unchanged in meaning`: CHEM-005 turns `c_- > 0` into `c→ 0` inside a theorem
statement and still compiles. An allow-list of fix rules therefore cannot be
built from break counts alone -- a rule with zero breaks has only been shown
not to CRASH the build. This instrument measures the other half.

WHAT. For every CANDIDATE rule (applied >= 1 edit in the OPEN-110 sweep and
never in any measured repair set), take up to K compiling papers where it
applied the most edits. Build each paper pristine once, and once per rule with
`LP_FIX_ONLY=<rule>` (the converging fixer restricted to that rule), then diff:
  - the WORD sequence of `pdftotext` output (what the paper says), as hunks
    with context -- the thing a reviewer classifies;
  - `pdftotext -layout` line count changed and page count (how it is laid out).
A rule whose edits only fire in cascade (after another rule's edit) applies
nothing alone; that is recorded as `edits_alone == 0`, not as "safe".

The fixer's exit status is part of its output (C-70): a crash raises.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse, collections, difflib, hashlib, json, os, pathlib, re, shutil
import subprocess, tempfile
from concurrent.futures import ThreadPoolExecutor

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/tools"))
from diff_real_roots import PIN, run_to_fixpoint  # noqa: E402
import _measurement_provenance as _mp  # noqa: E402

CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"
SWEEP = REPO / "corpora/apply_fixes_real/rule_attribution_400_719.json"
# Rules implicated in ANY measured break, in any window (OPEN-109, OPEN-110
# including its audit). They are excluded by evidence, not audited here.
IMPLICATED = {
    "CHEM-005", "CHEM-009", "CJK-001", "MATH-009", "MATH-014", "MATH-029",
    "MATH-043", "MATH-044", "MATH-078", "MATH-097", "SCRIPT-006", "SCRIPT-016",
    "SCRIPT-019", "STRUCT-001", "STYLE-024", "TYPO-001", "TYPO-002",
    "TYPO-005", "TYPO-010", "TYPO-012", "TYPO-013", "TYPO-022", "TYPO-037",
    "TYPO-062",
}
WORD = re.compile(r"\S+")


def tex_env(td):
    return dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                TEXMFVAR=str(pathlib.Path(td) / "tv"),
                openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")


def build(pkg, top, rule, timeout):
    """Fresh copy -> (optionally) LP_FIX_ONLY=rule fixer -> compile -> text."""
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        edits = 0
        if rule:
            trace = pathlib.Path(td) / "trace.tsv"
            env = dict(os.environ, LP_FIX_ONLY=rule, LP_FIX_TRACE=str(trace))
            for tex in sorted(work.rglob("*.tex")):
                before = tex.read_bytes()
                try:
                    r = subprocess.run([str(CLI), "--apply-fixes", str(tex)],
                                       capture_output=True, env=env,
                                       timeout=timeout)
                except subprocess.TimeoutExpired:
                    raise RuntimeError(f"fixer timed out on {tex} ({rule})")
                if r.returncode not in (0, 1):
                    raise RuntimeError(f"fixer crashed (exit {r.returncode}) "
                                       f"on {tex} ({rule}): {r.stderr[-300:]!r}")
                if r.stdout and r.stdout != before:
                    tex.write_bytes(r.stdout)
            if trace.is_file():
                edits = sum(1 for _ in trace.read_text(errors="replace").splitlines())
        rc, _ = run_to_fixpoint(work, top, tex_env(td), timeout)
        pdf = work / (pathlib.Path(top).stem + ".pdf")
        if rc != 0 or not pdf.is_file():
            return {"rc": rc, "edits": edits, "text": None, "layout": None,
                    "pages": None}
        txt = subprocess.run(["pdftotext", "-enc", "UTF-8", str(pdf), "-"],
                             capture_output=True).stdout.decode("utf-8", "replace")
        lay = subprocess.run(["pdftotext", "-layout", "-enc", "UTF-8", str(pdf),
                              "-"], capture_output=True).stdout.decode(
                                  "utf-8", "replace")
        return {"rc": rc, "edits": edits, "text": txt, "layout": lay,
                "pages": txt.count("\f")}


def word_hunks(a, b, ctx=6, cap=25):
    wa, wb = WORD.findall(a), WORD.findall(b)
    sm = difflib.SequenceMatcher(None, wa, wb, autojunk=False)
    hunks = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        hunks.append({"before": " ".join(wa[max(0, i1 - ctx):i2 + ctx]),
                      "after": " ".join(wb[max(0, j1 - ctx):j2 + ctx]),
                      "removed": " ".join(wa[i1:i2]), "added": " ".join(wb[j1:j2])})
    return len(hunks), hunks[:cap]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--k", type=int, default=5)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--timeout", type=int, default=240)
    ap.add_argument("--rules", default="", help="comma list overriding the candidates")
    ns = ap.parse_args()

    root = pathlib.Path(os.environ["LP_REAL_CORPUS"]).resolve()
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0]
    if PIN not in banner:
        sys.exit(f"FATAL: engine skew {banner!r}")
    for k in ("LP_FIX_ONLY", "LP_FIX_EXCLUDE", "LP_FIX_TRACE"):
        if os.environ.get(k):
            sys.exit(f"FATAL: {k} set in the caller's environment")

    sweep = json.loads(SWEEP.read_text())
    rows = [r for s in sweep["shards"] for r in s["rows"]
            if r.get("cell") == "preserved"]
    by_rule = collections.defaultdict(list)
    for r in rows:
        for rule, n in r.get("applied_rules", {}).items():
            by_rule[rule].append((n, r["arxiv_id"], r["toplevel"]))
    rules = (ns.rules.split(",") if ns.rules
             else sorted(k for k in by_rule if k not in IMPLICATED))
    plan = collections.defaultdict(list)      # paper -> [rules]
    tops = {}
    for rule in rules:
        for n, aid, top in sorted(by_rule.get(rule, []), reverse=True)[:ns.k]:
            plan[aid].append(rule)
            tops[aid] = top

    results, errors = [], []

    def one(aid):
        pkg, top = root / aid, tops[aid]
        base = build(pkg, top, None, ns.timeout)
        out = []
        for rule in plan[aid]:
            f = build(pkg, top, rule, ns.timeout)
            rec = {"rule": rule, "arxiv_id": aid, "rc_pristine": base["rc"],
                   "rc_fixed": f["rc"], "edits_alone": f["edits"],
                   "pages": [base["pages"], f["pages"]]}
            if base["text"] is not None and f["text"] is not None:
                n, h = word_hunks(base["text"], f["text"])
                la, lb = base["layout"].splitlines(), f["layout"].splitlines()
                rec.update(word_hunks_total=n, word_hunks=h,
                           layout_lines_changed=sum(
                               1 for t in difflib.ndiff(la, lb) if t[:1] in "+-"))
            out.append(rec)
        return out

    with ThreadPoolExecutor(ns.jobs) as ex:
        futs = {aid: ex.submit(one, aid) for aid in sorted(plan)}
        for i, (aid, fu) in enumerate(futs.items(), 1):
            try:
                results.extend(fu.result())
            except Exception as e:  # recorded AND fails the run
                errors.append({"arxiv_id": aid, "error": repr(e)})
            print(f"[{i}/{len(futs)}] {aid}", flush=True)
            pathlib.Path(ns.out).write_text(json.dumps(
                {"complete": False, "errors": errors, "results": results},
                indent=1, ensure_ascii=False))
    prov = {"cli_sha256": hashlib.sha256(CLI.read_bytes()).hexdigest(),
            "cli_platform": _mp.cli_platform(),
            "cli_build_root": _mp.cli_build_root(CLI),  # C-72
            "src_tree_sha": subprocess.run(
                ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
                cwd=REPO, capture_output=True, text=True).stdout.strip(),
            "engine": banner, "k": ns.k, "rules": rules,
            "sample": "papers 'preserved' in rule_attribution_400_719.json, "
                      "top-k by edits of the rule"}
    pathlib.Path(ns.out).write_text(json.dumps(
        {"provenance": prov, "complete": True, "errors": errors,
         "results": results}, indent=1, ensure_ascii=False))
    print("SENTINEL_DONE", flush=True)
    return 2 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
