#!/usr/bin/env python3
"""Grade the strict-tier standing battery and write its manifest.

ADR-012 (docs/v27/adr/ADR-012-contract-bounded-proven-tier.md) and
docs/v27/STRICT_TIER_DESIGN.md section E define a standing regression battery:
minimal documents, each exhibiting ONE failure mode of the strict tier's
fatal_reason table (E0-E14). Before ADR-012 the CLI printed READY with a
PREMISE-CERTIFIED line on most of them. Milestone M0 relabels every one as
heuristic; milestones M2/M3 must turn every one into PROVEN NOT-READY with the
named E-code.

For every `corpora/strict_battery/*.tex` this script records:

  pdflatex  the pinned-oracle outcome, graded by the SAME protocol as the
            real-paper differential: `-interaction=nonstopmode -halt-on-error`,
            restricted shell-escape (the stock default), up to 3 passes plus
            the confirming pass (diff_real_roots.run_to_fixpoint), and a PDF is
            REQUIRED (design section B.4: rc 0 with no PDF is the fatal E0).
  cli       the current CLI's --compile-check exit code, and the tier and kind
            tokens of its TIER line.
  expected  the E-code the strict tier must eventually decide (from the file
            name prefix) and the verdict it must eventually print.

Usage:
  gen_strict_battery.py [--repo .]           grade and write manifest.json
  gen_strict_battery.py --repo . --check     re-grade and diff against it

The --check mode needs pdflatex, so it is a local/nightly tool, never part of
the pure spec-drift job (the OPEN-101 lesson). The CI-side assertion that no
battery document renders PROVEN in M0 lives in latex-parse/src/test_verdict.ml,
which runs the CLI only.
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
from diff_real_roots import PIN, run_to_fixpoint  # noqa: E402

BATTERY = Path("corpora/strict_battery")
CLI = Path("_build/default/latex-parse/src/validators_cli.exe")

E_DESCRIPTIONS = {
    "e0": "rc 0 but no PDF (no typeset material)",
    "e1": "undefined control sequence",
    "e2": "undefined environment",
    "e3": "mode violation",
    "e4": "double superscript or subscript",
    "e5": "group or environment stack discipline",
    "e6": "\\par in math or in a non-long argument",
    "e7": "missing mandatory argument",
    "e8": "definer clash",
    "e9": "counter operation on an unknown counter",
    "e10": "missing input or graphics file",
    "e11": "Unicode code point without a u8 definition",
    "e12": "configuration fatal",
    "e13": "bad key or ill-typed argument",
    "e14": "capacity overflow",
}


def first_error(log: Path) -> str:
    if not log.is_file():
        return ""
    lines = log.read_text(errors="replace").split("\n")
    for i, line in enumerate(lines):
        if line.startswith("!"):
            return "".join(lines[i:i + 2]).strip()[:200]
    return ""


def grade(tex: Path, timeout: int = 60) -> dict:
    with tempfile.TemporaryDirectory() as td:
        work = Path(td) / "w"
        work.mkdir()
        shutil.copy(tex, work / tex.name)
        env = dict(os.environ, TEXMFHOME=str(Path(td) / "th"),
                   TEXMFVAR=str(Path(td) / "tv"), openin_any="p",
                   openout_any="p", SOURCE_DATE_EPOCH="0")
        rc, passes = run_to_fixpoint(work, tex.name, env, timeout)
        pdf = (work / (tex.stem + ".pdf")).is_file()
        err = first_error(work / (tex.stem + ".log"))
    return {"rc": rc, "passes": passes, "pdf": pdf,
            "compiles": rc == 0 and pdf, "first_error": err}


def cli_verdict(repo: Path, tex: Path) -> dict:
    p = subprocess.run([str(repo / CLI), "--compile-check", str(tex)],
                       capture_output=True, timeout=120)
    out = p.stdout.decode("utf-8", "replace")
    tier = kind = None
    for line in out.splitlines():
        if line.startswith("TIER\t"):
            f = line.split("\t")
            tier, kind = f[1], f[2]
            break
    return {"rc": p.returncode, "tier": tier, "kind": kind,
            "token_line": next((l.split("\t")[0] for l in out.splitlines()
                                if l.startswith(("READY\t", "NOT-READY\t"))),
                               None)}


def build(repo: Path) -> dict:
    pin = subprocess.run(["pdflatex", "--version"], capture_output=True,
                         text=True).stdout.split("\n")[0].strip()
    if not pin.startswith(PIN):
        raise SystemExit(f"[strict-battery] PIN MISMATCH: {pin!r} != {PIN!r}")
    rows = []
    for tex in sorted((repo / BATTERY).glob("*.tex")):
        m = re.match(r"(e\d+)_", tex.name)
        if not m:
            raise SystemExit(f"[strict-battery] {tex.name}: name must start "
                             f"with its E-code, e.g. e3_frac_in_text.tex")
        code = m.group(1)
        rows.append({
            "file": tex.name,
            "e_code": code.upper(),
            "failure_mode": E_DESCRIPTIONS[code],
            "pdflatex": grade(tex),
            "cli_m0": cli_verdict(repo, tex),
            "must_eventually_render": f"PROVEN NOT-READY [{code.upper()}]",
        })
    return {
        "provenance": {
            "produced_by": "scripts/tools/gen_strict_battery.py",
            "oracle": pin,
            "protocol": "pdflatex -interaction=nonstopmode -halt-on-error, "
                        "restricted shell-escape (default), up to 3 passes plus "
                        "a confirming pass, PDF required",
            "src_tree_sha": subprocess.run(
                ["git", "rev-parse", "HEAD:latex-parse/src"], cwd=repo,
                capture_output=True, text=True).stdout.strip() or None,
        },
        "summary": {
            "n": len(rows),
            "pdflatex_fails": sum(1 for r in rows if not r["pdflatex"]["compiles"]),
            "cli_ready_exit_0": sum(1 for r in rows if r["cli_m0"]["rc"] == 0),
            "cli_proven": sum(1 for r in rows if r["cli_m0"]["tier"] == "proven"),
        },
        "rows": rows,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--check", action="store_true")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    out = build(repo)
    man = repo / BATTERY / "manifest.json"
    if ns.check:
        old = json.loads(man.read_text())
        a = [(r["file"], r["pdflatex"]["compiles"], r["cli_m0"]["rc"],
              r["cli_m0"]["tier"]) for r in old["rows"]]
        b = [(r["file"], r["pdflatex"]["compiles"], r["cli_m0"]["rc"],
              r["cli_m0"]["tier"]) for r in out["rows"]]
        if a != b:
            print("[strict-battery] FAIL: the battery moved; diff:")
            for x, y in zip(a, b):
                if x != y:
                    print(f"    {x} -> {y}")
            return 1
        print(f"[strict-battery] OK: {len(b)} documents unchanged")
        return 0
    man.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    s = out["summary"]
    print(f"[strict-battery] wrote {man}: {s['n']} documents, pdflatex fails "
          f"{s['pdflatex_fails']}, CLI exit 0 on {s['cli_ready_exit_0']}, "
          f"PROVEN on {s['cli_proven']}")
    for r in out["rows"]:
        print(f"  {r['file']:36s} pdflatex={'ok ' if r['pdflatex']['compiles'] else 'FAIL'} "
              f"rc={r['pdflatex']['rc']} pdf={r['pdflatex']['pdf']} "
              f"cli={r['cli_m0']['rc']} {r['cli_m0']['kind']}  {r['pdflatex']['first_error'][:70]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
