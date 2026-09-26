#!/usr/bin/env python3
"""Measure the strict-tier boundary scan over a real-paper sample.

ADR-012, milestone M0, deliverable (e). The CLI's `--strict-boundary FILE`
prints every construct in the project CLOSURE (root, \\input children, local
.sty/.cls, the .bbl) for which the strict grammar has no production — see
latex-parse/src/strict_boundary.mli. This script runs it over every root of a
results file and writes the per-paper findings and their distribution.

The scan is DIAGNOSTIC in M0: it changes no verdict and no exit code. What it
measures is how far each real paper is from the strict tier's grammar, which is
an UPPER BOUND on strict coverage from the grammar side only: a paper with no
finding still needs an attested configuration contract (M1/M3) and a decider
(M2/M3) before it can get a PROVEN verdict.

Usage:
  measure_strict_boundary.py --results corpora/real_roots/results_sample2.json \\
      --corpus $LP_REAL_CORPUS --cli _build/default/latex-parse/src/validators_cli.exe \\
      --out corpora/real_roots/strict_boundary_sample2.json
"""
from __future__ import annotations

import argparse
import collections
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TURING = {"def", "let", "xparse", "atletter", "expl3", "conditional", "loop",
          "csname", "expandafter", "write", "foreign"}


def scan(cli: Path, top: Path) -> list[dict]:
    p = subprocess.run([str(cli), "--strict-boundary", str(top)],
                       capture_output=True, timeout=600)
    if p.returncode != 0:
        raise SystemExit(f"[strict-boundary] FATAL: {top}: rc {p.returncode}: "
                         f"{p.stderr.decode('utf-8', 'replace')[:200]}")
    out = p.stdout.decode("utf-8", "replace").splitlines()
    if not out or not out[-1].startswith("BOUNDARY-SUMMARY\t"):
        raise SystemExit(f"[strict-boundary] FATAL: {top}: no summary line")
    rows = []
    for line in out[:-1]:
        f = line.split("\t")
        if len(f) != 6 or f[0] != "BOUNDARY":
            raise SystemExit(f"[strict-boundary] FATAL: malformed line {line!r}")
        where, count = f[3], int(f[4])
        file, _, ln = where.rpartition(":")
        rows.append({"category": f[1], "id": f[2], "file": file,
                     "line": int(ln), "count": count, "construct": f[5]})
    if int(out[-1].split("\t")[1]) != len(rows):
        raise SystemExit(f"[strict-boundary] FATAL: {top}: summary count mismatch")
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--results", required=True)
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--cli", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=6)
    a = ap.parse_args()
    res = json.loads(Path(a.results).read_text())
    cli = Path(a.cli)

    def one(d):
        top = Path(a.corpus) / d["arxiv_id"] / d["toplevel"]
        fs = scan(cli, top)
        root = Path(d["toplevel"]).name
        cats = sorted({f["category"] for f in fs})
        return {
            "id": d["arxiv_id"], "toplevel": d["toplevel"], "cell": d["cell"],
            "categories": cats,
            "root_only_categories": sorted({f["category"] for f in fs
                                            if f["file"] == d["toplevel"]
                                            or f["file"] == root}),
            "bbl_only_categories": sorted(
                {f["category"] for f in fs if f["file"].endswith(".bbl")}
                - {f["category"] for f in fs if not f["file"].endswith(".bbl")}),
            "findings": fs,
        }

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        rows = list(ex.map(one, res["docs"]))
    n = len(rows)
    per_cat = collections.Counter(c for r in rows for c in r["categories"])
    turing = [r for r in rows if TURING & set(r["categories"])]
    local = [r for r in rows if "local_style" in r["categories"]]
    clean = [r for r in rows if not r["categories"]]
    only_def = [r for r in rows if set(r["categories"]) == {"def"}]
    closure_gain = [r for r in rows
                    if set(r["categories"]) - set(r["root_only_categories"])]
    turing_bbl_only = [r for r in turing
                       if not (TURING & (set(r["categories"])
                                         - set(r["bbl_only_categories"])))]
    summary = {
        "n": n,
        "no_finding": len(clean),
        "no_finding_and_compiles": sum(1 for r in clean
                                       if r["cell"] in ("true-READY",
                                                        "false-NOT-READY")),
        "any_turing_construct": len(turing),
        "turing_only_in_bbl": len(turing_bbl_only),
        "local_style_file": len(local),
        "local_style_without_turing": len([r for r in local if r not in turing]),
        "blocked_only_by_def": len(only_def),
        "closure_adds_a_category_the_root_lacks": len(closure_gain),
        "papers_per_category": dict(sorted(per_cat.items(),
                                           key=lambda kv: (-kv[1], kv[0]))),
    }
    out = {
        "provenance": {
            "produced_by": "scripts/tools/measure_strict_boundary.py",
            "results_source": a.results,
            "measured_at_sha": subprocess.run(
                ["git", "rev-parse", "HEAD"], capture_output=True,
                text=True).stdout.strip(),
            "src_tree_sha": subprocess.run(
                ["git", "rev-parse", "HEAD:latex-parse/src"],
                capture_output=True, text=True).stdout.strip() or None,
            "note": "DIAGNOSTIC (ADR-012 M0): no verdict or exit code depends "
                    "on this scan.",
        },
        "summary": summary,
        "rows": rows,
    }
    Path(a.out).write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
