#!/usr/bin/env python3
"""Prove the oracle HARNESS is transparent: the container backend, driven from
the host, grades exactly as the native backend does inside the pinned image.

WHY (ADR-012 decision 7). `_oracle.py` has two backends. CI's tex-oracle job
runs inside the image and uses `native`; a maintainer's machine uses
`container` (`docker exec` into a long-lived container of the same image).
Every number re-graded locally is published as if CI had graded it, so the two
paths must be the same function of the document. Things that could make them
differ, each of which this compares rather than assumes:

  * the environment crossing into the container (only an allow-list of TeX
    variables is forwarded, and HOME is /tmp as in CI);
  * the working directory mapping (the work root is mounted at the same path);
  * the timeout (enforced inside the container by `timeout`, on the host by
    subprocess for native);
  * the multi-pass fixpoint and PDF detection (same code, run in two places).

HOW. For each document: stage it twice in two fresh directories under the
oracle work root; grade copy A with the container backend from THIS process;
grade copy B by running `_oracle.py`'s own native backend INSIDE the container
(`docker exec -e LP_ORACLE_IN_IMAGE=<image> python3 ...`), which first
verifies the image's tree fingerprint. Compare rc, passes, PDF and the first
`!` error line. Any disagreement fails (exit 1).

The document set: every strict-battery fixture, every corpora/compile_check
document, and (with --corpus) real arXiv trees from real_roots sample 1,
chosen deterministically to include both compiling and failing papers.

Local only: it needs docker and the pinned image, like every other grader.

  check_oracle_equivalence.py --repo . [--corpus $LP_REAL_CORPUS] \\
      [--real 10] [--out corpora/oracle_baseline/equivalence.json]
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

INNER = r'''
import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import _oracle
o = _oracle.get_oracle()
assert o.backend == "native", o.backend
work, top, td = Path(sys.argv[2]), sys.argv[3], sys.argv[4]
r = o.run_to_fixpoint(work, top, o.tex_env(td), int(sys.argv[5]))
print(json.dumps({"backend": o.backend, "rc": r.rc, "passes": r.passes,
                  "pdf": r.pdf, "first_error":
                  _oracle.first_error_block(_oracle.job_output(work, top, ".log"), 1)}))
'''


def stage(src: Path, top: str, dst: Path, whole_dir: bool) -> None:
    if whole_dir:
        shutil.copytree(src.parent if src.is_file() else src, dst)
    else:
        dst.mkdir(parents=True)
        shutil.copy(src, dst / top)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--corpus", default=None)
    ap.add_argument("--real", type=int, default=10)
    ap.add_argument("--timeout", type=int, default=240)
    ap.add_argument("--out", default=None)
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    try:
        o = _oracle.get_oracle()
    except _oracle.OracleError as e:
        print(f"[oracle-equiv] FATAL: {e}", file=sys.stderr)
        return 2
    if o.backend != "container":
        print("[oracle-equiv] FATAL: run this on a host, not inside the image",
              file=sys.stderr)
        return 2

    docs: list[tuple[str, Path, str, bool]] = []  # (label, src, toplevel, whole_dir)
    bat = repo / "corpora/strict_battery"
    for t in sorted(bat.glob("*.tex")):
        docs.append((f"strict_battery/{t.name}", t, t.name, False))
    for t in sorted(bat.glob("*/main.tex")):
        docs.append((f"strict_battery/{t.parent.name}", t.parent, "main.tex", True))
    cc = repo / "corpora/compile_check"
    for t in sorted(cc.glob("*.tex")):
        if t.name.endswith("_part.tex"):
            continue
        # compile_check documents may \input a sibling *_part.tex: stage the dir
        docs.append((f"compile_check/{t.name}", cc, t.name, True))
    if ns.corpus and ns.real:
        res = json.loads((repo / "corpora/real_roots/results.json").read_text())
        fails = [d for d in res["docs"] if d.get("pdflatex_rc") not in (0, None)]
        oks = [d for d in res["docs"] if d.get("pdflatex_rc") == 0]
        pick = fails[: ns.real // 2] + oks[: ns.real - min(len(fails), ns.real // 2)]
        for d in pick:
            docs.append((f"real/{d['arxiv_id']}", Path(ns.corpus) / d["arxiv_id"],
                         d["toplevel"], True))

    # A copy of the oracle module and its pin, INSIDE the mounted work root, so
    # the native run executes the same bytes the host imported.
    rows, bad = [], 0
    with o.tempdir(prefix="equiv-") as root:
        root = Path(root)
        mod = root / "repo/scripts/tools"
        mod.mkdir(parents=True)
        shutil.copy(Path(_oracle.__file__), mod / "_oracle.py")
        (root / "repo/.github/workflows").mkdir(parents=True)
        shutil.copy(_oracle.WORKFLOW, root / "repo/.github/workflows/tex-oracle.yml")
        for i, (label, src, top, whole) in enumerate(docs, 1):
            a, b = root / f"a{i}", root / f"b{i}"
            stage(src, top, a / "w", whole)
            stage(src, top, b / "w", whole)
            ra = o.run_to_fixpoint(a / "w", top, o.tex_env(a), ns.timeout)
            ea = _oracle.first_error_block(_oracle.job_output(a / "w", top, ".log"), 1)
            p = subprocess.run(
                [o.docker, "exec", "-e", "HOME=/tmp", "-e",
                 f"LP_ORACLE_IN_IMAGE={_oracle.IMAGE}", o.name, "python3", "-c",
                 INNER, str(mod), str(b / "w"), top, str(b), str(ns.timeout)],
                capture_output=True, text=True, timeout=ns.timeout * 5 + 60)
            if p.returncode != 0:
                print(f"[oracle-equiv] FATAL: native run failed for {label}: "
                      f"{p.stderr[-600:]}", file=sys.stderr)
                return 2
            nb = json.loads(p.stdout.strip().splitlines()[-1])
            same = (ra.rc, ra.passes, ra.pdf, ea) == (nb["rc"], nb["passes"],
                                                     nb["pdf"], nb["first_error"])
            bad += not same
            rows.append({"doc": label, "container": {"rc": ra.rc, "passes": ra.passes,
                                                     "pdf": ra.pdf, "first_error": ea},
                         "native_in_image": {k: nb[k] for k in
                                             ("rc", "passes", "pdf", "first_error")},
                         "agree": same})
            print(f"  [{i}/{len(docs)}] {label:48s} container rc={ra.rc} p={ra.passes} "
                  f"pdf={ra.pdf} | native rc={nb['rc']} p={nb['passes']} "
                  f"pdf={nb['pdf']} {'OK' if same else 'DIFFER'}", flush=True)
            shutil.rmtree(a, ignore_errors=True)
            shutil.rmtree(b, ignore_errors=True)

    summary = {"documents": len(rows), "agree": len(rows) - bad, "disagree": bad,
               "failing_documents": sum(1 for r in rows if r["container"]["rc"] != 0),
               "compiling_documents": sum(1 for r in rows if r["container"]["rc"] == 0)}
    print(f"[oracle-equiv] {summary}")
    if ns.out:
        out = repo / ns.out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps({
            "produced_by": "scripts/tools/check_oracle_equivalence.py",
            "oracle": o.provenance(),
            "compared": "container backend from the host vs _oracle.py native "
                        "backend run inside the same image (docker exec with "
                        "LP_ORACLE_IN_IMAGE); rc, passes, PDF and first error line",
            "summary": summary, "rows": rows}, indent=1) + "\n")
    if len(rows) < 20:
        print("[oracle-equiv] FATAL: fewer than 20 documents compared", file=sys.stderr)
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
