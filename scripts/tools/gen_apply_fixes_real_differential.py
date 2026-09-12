#!/usr/bin/env python3
"""Produce corpora/apply_fixes_real/results.json — the REAL-paper differential
for the auto-fix channel.

WHY THIS FILE EXISTS (OPEN-071).

`--apply-fixes` broke 63.3% of real compiling papers on the morning of
2026-09-07 and 6.7% by the end of that day. Neither number had an artefact.
No file under corpora/ held the sample, no committed script reproduced it, and
no oracle record existed -- the whole trajectory lived in PROJECT_STATE prose
and two commit messages. A number with no artefact cannot be re-run, cannot be
regression-gated, and decays silently the moment a producer changes.

Meanwhile the BLOCKING gate that exists to catch exactly this,
check_apply_fixes_roundtrip, asserts the right invariant over the wrong
corpus: 78 in-house documents in which grep for `xymatrix`, `elsarticle`,
`DeclareMathSymbol` or `chardef` returns ZERO hits, and which exclude `\\input`
children by construction. Every fixture in it was written by someone who
already knew which bug they were guarding. That is why five destructive
producers in one week were all found by hand, not by CI.

WHAT THIS MEASURES. For each sampled real root that COMPILES at the pin:
apply the default fixer to the root AND to every `.tex` in its tree (the
STRUCT-001 lesson: a fix applied to a child can kill the parent, and a
root-only differential cannot see it), then recompile under the identical
protocol. A paper that compiled before and does not after is a BREAK, and
breaks are the number this project must not let rise.

Papers that do not compile before are EXCLUDED, not counted as passes: the
fixer cannot be blamed for a document pdflatex already refuses, and folding
them in would flatter the rate. That exclusion is why the headline is
"k of the n that compile", never "k of 40".

DETERMINISM. Same frame and same ordering as the real-paper corpus
(`sha256(arxiv_id)` ascending over the pdflatex/single-toplevel frame), taken
at an OFFSET so the sample is disjoint from the 400 documents the verdict
channel is tuned against. Sample 1 is ranks 1-200 and sample 2 is 201-400;
this window starts at 2000 and has never been used to tune anything.
"""
import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from diff_real_roots import (  # noqa: E402
    ORACLE, PIN, build_frame, run_to_fixpoint,
)

DEFAULT_OFFSET = 2000
DEFAULT_N = 40


def sha256_file(p: pathlib.Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def first_error(work: pathlib.Path, toplevel: str) -> str:
    """The first `! ...` line pdflatex logged, or "" if none."""
    log = work / (pathlib.Path(toplevel).stem + ".log")
    if not log.is_file():
        return ""
    for raw in log.read_bytes().split(b"\n"):
        if raw.startswith(b"!"):
            return raw.decode("utf-8", "replace").strip()[:200]
    return ""


def apply_fixes_tree(work: pathlib.Path, cli: pathlib.Path, timeout: int):
    """Apply the DEFAULT fixer to every .tex in the tree, in place.

    Every .tex, not just the root: STRUCT-001 inserted a preamble into `\\input`
    FRAGMENTS and killed their parents, and a root-only differential is blind
    to that whole class by construction.
    """
    changed = []
    for tex in sorted(work.rglob("*.tex")):
        before = tex.read_bytes()
        try:
            r = subprocess.run([str(cli), "--apply-fixes", str(tex)],
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            continue
        # BYTES, never text=True: real papers carry latin-1 and the CLI echoes
        # source fragments, so strict decoding raises mid-sweep (C-9 family).
        if r.returncode in (0, 1) and r.stdout and r.stdout != before:
            tex.write_bytes(r.stdout)
            changed.append(str(tex.relative_to(work)))
    return changed


def run_one(rec, root, cli, timeout):
    pkg = root / rec["arxiv_id"]
    out = {"arxiv_id": rec["arxiv_id"], "toplevel": rec["toplevel"]}
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        tex_env = dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                       TEXMFVAR=str(pathlib.Path(td) / "tv"),
                       openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")
        # ⚠ SNAPSHOT THE SHIPPED FILE SET FIRST. The two compiles must start
        # from byte-identical trees or the differential measures the harness.
        # The first draft of this function cleared by-products with
        # rglob("*.pdf"), which DELETED THE FIGURES: 2507.04187v1 compiles rc 0,
        # and the "break" it produced was
        # `! Package pdftex.def Error: File 'figs/ppo_motivation.pdf' not found`
        # -- 34 figure PDFs removed by the instrument, not by the fixer. A
        # jobname-based allowlist would have been wrong too (LaTeX writes an
        # .aux per \include'd child, and .bcf/.run.xml/.nav/.snm by package).
        # Recording the pre-compile file set and deleting exactly what appeared
        # is the only rule that cannot touch a shipped asset. (C-30: the
        # verifier gets the adversarial pass first.)
        shipped = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        rc0, _ = run_to_fixpoint(work, rec["toplevel"], tex_env, timeout)
        out["rc_before"] = rc0
        out["first_error_before"] = first_error(work, rec["toplevel"])
        if rc0 != 0:
            out["cell"] = "excluded-did-not-compile"
            return out
        # Delete exactly what pdflatex created, so the post-fix compile cannot
        # inherit state the fixed document never produced.
        for q in sorted((x for x in work.rglob("*") if x.is_file()),
                        key=lambda x: -len(x.parts)):
            if q.relative_to(work) not in shipped:
                q.unlink(missing_ok=True)
        out["changed_files"] = apply_fixes_tree(work, cli, timeout)
        after_fix = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        if after_fix != shipped:
            out["cell"] = "instrument-error-file-set-changed"
            out["file_set_delta"] = sorted(
                str(x) for x in after_fix.symmetric_difference(shipped))
            return out
        rc1, _ = run_to_fixpoint(work, rec["toplevel"], tex_env, timeout)
        out["rc_after"] = rc1
        out["first_error_after"] = first_error(work, rec["toplevel"])
        out["cell"] = "preserved" if rc1 == 0 else "broken"
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--repo", default=".")
    ap.add_argument("--out", default="corpora/apply_fixes_real/results.json")
    ap.add_argument("--offset", type=int, default=DEFAULT_OFFSET)
    ap.add_argument("--n", type=int, default=DEFAULT_N)
    ap.add_argument("--timeout", type=int, default=180)
    ns = ap.parse_args()

    repo = pathlib.Path(ns.repo).resolve()
    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    if not cli.is_file():
        print(f"[apply-fixes-real] FATAL: {cli} not built", file=sys.stderr)
        return 2
    if not ns.corpus_root:
        print("[apply-fixes-real] FATAL: no --corpus-root and LP_REAL_CORPUS "
              "unset. The corpus is not in this repo and is not "
              "redistributable; see corpora/real_roots/README.md",
              file=sys.stderr)
        return 2
    root = pathlib.Path(ns.corpus_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[apply-fixes-real] FATAL: {root} does not exist",
              file=sys.stderr)
        return 2
    # Engine skew is its own failure: a differential graded by the wrong
    # pdflatex is not a soundness result, it is a different experiment.
    try:
        banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                                text=True).stdout.split("\n")[0]
    except FileNotFoundError:
        print("[apply-fixes-real] FATAL: pdflatex not on PATH", file=sys.stderr)
        return 2
    if PIN not in banner:
        print(f"[apply-fixes-real] FATAL: engine skew: local is {banner!r}, "
              f"pinned is {PIN!r}", file=sys.stderr)
        return 3

    frame = build_frame(root)
    ordered = sorted(frame, key=lambda r: hashlib.sha256(
        r["arxiv_id"].encode()).hexdigest())
    window = ordered[ns.offset:ns.offset + ns.n]
    if len(window) < ns.n:
        print(f"[apply-fixes-real] FATAL: frame has {len(ordered)} papers; "
              f"offset {ns.offset} + n {ns.n} runs past the end. Widening the "
              f"window silently would change what the number means.",
              file=sys.stderr)
        return 2

    rows = []
    for i, rec in enumerate(window, 1):
        r = run_one(rec, root, cli, ns.timeout)
        rows.append(r)
        print(f"  [{i}/{len(window)}] {r['arxiv_id']:<16} {r['cell']}",
              flush=True)

    compiled = [r for r in rows if r["cell"] in ("preserved", "broken")]
    broken = [r for r in compiled if r["cell"] == "broken"]
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                         capture_output=True, text=True).stdout.strip()
    doc = {
        "provenance": {
            "produced_by": "scripts/tools/gen_apply_fixes_real_differential.py",
            "measured_at_sha": sha,
            "cli_sha256": sha256_file(cli),
            "frame": {"corpus": str(root.name), "frame_size": len(frame),
                      "selection": "sha256(arxiv_id) ascending",
                      "offset": ns.offset, "n": ns.n},
            "oracle": ORACLE,
            "fix_scope": "every .tex in the tree, root and children",
        },
        "summary": {
            "sampled": len(rows),
            "compiled_before": len(compiled),
            "excluded_did_not_compile": len(rows) - len(compiled),
            "preserved": len(compiled) - len(broken),
            "broken": len(broken),
        },
        "rows": rows,
    }
    outp = repo / ns.out
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")
    s = doc["summary"]
    pct = (100.0 * s["broken"] / s["compiled_before"]) if s["compiled_before"] else 0.0
    print(f"[apply-fixes-real] wrote {ns.out}: {s['broken']}/"
          f"{s['compiled_before']} = {pct:.1f}% of real COMPILING papers "
          f"broken by the default fixer "
          f"({s['excluded_did_not_compile']} excluded, did not compile)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
