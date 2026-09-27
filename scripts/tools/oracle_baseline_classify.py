#!/usr/bin/env python3
"""Attribute each cell the oracle-baseline change moved (ADR-012 decision 7).

`diff_real_roots.py --repass --rebaseline-oracle --diff-out FILE` writes, per
row, the grade recorded under the host TeX Live ("before") and the grade under
the pinned image ("after"). A difference has three possible sources, and the
owner's decision asks for each changed cell to be put in one:

  (i)   the host tree was DAMAGED (orphaned files with no package-database
        owner, failed restores, missing collections);
  (ii)  UPSTREAM DRIFT: the host's package set is newer or older than the
        image's 2026 snapshot, and the package changed behaviour;
  (iii) unexplained -- investigate.

This tool does the mechanical half. For every row whose compile verdict
changed it re-grades the same document on the HOST TeX Live today, through
`_oracle.host_diagnostic()` (a diagnostic backend that `get_oracle()` never
returns and whose provenance says NOT-THE-ORACLE), and records:

  host_now      rc / PDF / first error on the host tree today
  host_agrees_with  "before" (the difference is between the two trees),
                "after" (the host's own grade has moved since it was recorded),
                or "neither"
  packages      TeX Live packages that own a file the log of either run loaded
                and whose revision differs between the host and image
                package databases (from the tlpdb files passed in)

The human half -- reading the two logs and naming the mechanism -- is
recorded in the `classification` field by hand; this tool never writes it.

  oracle_baseline_classify.py --diff corpora/oracle_baseline/diff_X.json \\
      --corpus $LP_REAL_CORPUS --host-tlpdb /usr/local/texlive/2026/tlpkg/texlive.tlpdb \\
      --image-tlpdb /path/to/image.tlpdb
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402


def compiles(g: dict) -> bool | None:
    v = str(g.get("pdflatex_verdict") or "").lower()
    if v in ("compiles", "fails"):
        return v == "compiles"
    if g.get("pdflatex_rc") is None:
        return None
    return g["pdflatex_rc"] == 0 and g.get("pdflatex_pdf", True) is not False


def tlpdb_files(path: Path) -> tuple[dict, dict]:
    """(file basename -> package, package -> revision) from a tlpdb."""
    owner, rev, name = {}, {}, None
    for line in path.read_text(errors="replace").split("\n"):
        if line.startswith("name "):
            name = line[5:].strip()
        elif line.startswith("revision ") and name:
            rev[name] = line[9:].strip()
        elif line.startswith(" ") and name and "/" in line:
            owner.setdefault(line.strip().split(" ")[0].rsplit("/", 1)[-1], name)
    return owner, rev


def loaded_files(log: Path) -> set[str]:
    if not log.is_file():
        return set()
    txt = log.read_text(errors="replace")
    return set(m.rsplit("/", 1)[-1] for m in
               re.findall(r"\(([^()\s]+\.(?:sty|cls|def|cfg|fd|tex|ltx|clo|lua))", txt))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--diff", required=True)
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--host-tlpdb", required=True)
    ap.add_argument("--image-tlpdb", required=True)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--also", nargs="*", default=[],
                    help="arxiv ids to attribute although their verdict did not "
                         "move (e.g. the failure REASON changed)")
    ns = ap.parse_args()

    dpath = Path(ns.diff)
    diff = json.loads(dpath.read_text())
    howner, hrev = tlpdb_files(Path(ns.host_tlpdb))
    iowner, irev = tlpdb_files(Path(ns.image_tlpdb))
    host = _oracle.host_diagnostic()
    oracle = _oracle.get_oracle()
    moved = [r for r in diff["rows"] if compiles(r["before"]) != compiles(r["after"])
             or r["arxiv_id"] in ns.also]
    print(f"[classify] {len(moved)} row(s) to attribute in {dpath.name}")
    for r in moved:
        src = Path(ns.corpus) / r["arxiv_id"]
        grades = {}
        for label, be in (("host_now", host), ("image", oracle)):
            with oracle.tempdir(prefix="classify-") as td:
                work = Path(td) / "w"
                shutil.copytree(src, work)
                run = be.run_to_fixpoint(work, r["toplevel"], be.tex_env(td), ns.timeout)
                log = work / (Path(r["toplevel"]).stem + ".log")
                grades[label] = {"pdflatex_rc": run.rc, "pdflatex_pdf": run.pdf,
                                 "first_error": _oracle.first_error_block(log)[:300],
                                 "_files": loaded_files(log)}
        files = grades["host_now"].pop("_files") | grades["image"].pop("_files")
        pkgs = sorted({howner.get(f) or iowner.get(f) for f in files} - {None})
        r["host_now"] = grades["host_now"]
        r["image_rerun"] = grades["image"]
        hn = compiles(grades["host_now"])
        r["host_agrees_with"] = ("before" if hn == compiles(r["before"]) else
                                 "after" if hn == compiles(r["after"]) else "neither")
        r["packages_with_revision_drift"] = [
            {"package": p, "host": hrev.get(p, "ABSENT from host tlpdb"),
             "image": irev.get(p, "ABSENT from image tlpdb")}
            for p in pkgs if hrev.get(p) != irev.get(p)]
        print(f"  {r['arxiv_id']:16s} before={compiles(r['before'])} "
              f"after={compiles(r['after'])} host_now={hn} "
              f"agrees={r['host_agrees_with']} "
              f"drift={[d['package'] for d in r['packages_with_revision_drift']]}")
        print(f"      host : {grades['host_now']['first_error'][:150]}")
        print(f"      image: {grades['image']['first_error'][:150]}")
    diff["classification_inputs"] = {
        "host_diagnostic": host.provenance(),
        "method": "each verdict-changed row re-graded on the host tree today and "
                  "once more under the image; packages owning a loaded file "
                  "whose revision differs between the two tlpdbs"}
    dpath.write_text(json.dumps(diff, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
