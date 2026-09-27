#!/usr/bin/env python3
"""Before/after cell diff of a graded artefact across the oracle-baseline
change (ADR-012 decision 7).

The "before" is the artefact as committed at a git revision (graded by a host
TeX Live); the "after" is the working-tree artefact, re-graded through
`scripts/tools/_oracle.py`. It prints and (with --out) writes every row whose
pdflatex outcome moved -- rc, PDF, verdict -- and, separately, every row whose
first error line changed while the verdict did not, because a changed error
under an unchanged verdict is the cheapest early sign of macro drift.

Supported artefacts (their row schemas differ):
  strict_battery   corpora/strict_battery/manifest.json      rows[].pdflatex
  apply_fixes_real corpora/apply_fixes_real/results*.json    rows[].rc_before/rc_after

  oracle_baseline_cells.py --kind strict_battery \\
      --path corpora/strict_battery/manifest.json --rev origin/main \\
      --out corpora/oracle_baseline/diff_strict_battery.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def rows_of(kind: str, doc: dict) -> dict:
    out = {}
    if kind == "strict_battery":
        for r in doc["rows"]:
            p = r["pdflatex"]
            out[r["file"]] = {"rc": p["rc"], "pdf": p["pdf"], "compiles": p["compiles"],
                              "first_error": p["first_error"][:160]}
    elif kind == "apply_fixes_real":
        for r in doc["rows"]:
            out[r["arxiv_id"]] = {
                "cell": r["cell"], "rc_before": r.get("rc_before"),
                "rc_after": r.get("rc_after"),
                "first_error_before": (r.get("first_error_before") or "")[:160],
                "first_error_after": (r.get("first_error_after") or "")[:160],
                "changed_files": r.get("changed_files")}
    else:
        raise SystemExit(f"unknown --kind {kind}")
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--kind", required=True, choices=["strict_battery", "apply_fixes_real"])
    ap.add_argument("--path", required=True)
    ap.add_argument("--rev", default="origin/main")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--out", default=None)
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    old = json.loads(subprocess.run(["git", "show", f"{ns.rev}:{ns.path}"], cwd=repo,
                                    capture_output=True, text=True, check=True).stdout)
    new = json.loads((repo / ns.path).read_text())
    a, b = rows_of(ns.kind, old), rows_of(ns.kind, new)
    if set(a) != set(b):
        print(f"row sets differ: only before {sorted(set(a) - set(b))}, "
              f"only after {sorted(set(b) - set(a))}", file=sys.stderr)
        return 2
    verdict_keys = (("rc", "pdf", "compiles") if ns.kind == "strict_battery"
                    else ("cell", "rc_before", "rc_after", "changed_files"))
    err_keys = (("first_error",) if ns.kind == "strict_battery"
                else ("first_error_before", "first_error_after"))
    moved, err_only = [], []
    for k in sorted(a):
        va = {x: a[k][x] for x in verdict_keys}
        vb = {x: b[k][x] for x in verdict_keys}
        if va != vb:
            moved.append({"row": k, "before": a[k], "after": b[k]})
        elif any(a[k][x] != b[k][x] for x in err_keys):
            err_only.append({"row": k, "before": {x: a[k][x] for x in err_keys},
                             "after": {x: b[k][x] for x in err_keys}})
    print(f"[cells] {ns.path}: {len(a)} rows; outcome moved on {len(moved)}; "
          f"first error changed with the outcome unchanged on {len(err_only)}")
    for m in moved:
        print(f"  MOVED {m['row']}: {json.dumps({x: m['before'][x] for x in verdict_keys})}"
              f" -> {json.dumps({x: m['after'][x] for x in verdict_keys})}")
    for m in err_only:
        print(f"  error-text {m['row']}: {m['before']} -> {m['after']}")
    if ns.out:
        Path(repo / ns.out).parent.mkdir(parents=True, exist_ok=True)
        (repo / ns.out).write_text(json.dumps({
            "artefact": ns.path, "before_rev": ns.rev,
            "before_oracle": "host TeX Live (no image recorded)",
            "after_oracle": (new.get("provenance", {}).get("oracle")
                             or new.get("provenance", {}).get("oracle_provenance")),
            "rows": len(a), "outcome_moved": moved,
            "first_error_changed_only": err_only}, indent=1, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
