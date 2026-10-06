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

RE-GRADING AN ARTEFACT (OPEN-128 (7)/(8)). `--regrade --cli-checkout DIR`
re-runs every row of the artefact at --out with the CLI built in DIR, which
must be the engine tree the artefact records (src_tree_sha): the CLI side is
the recorded one, so every moved cell is the ORACLE's. The CLI provenance
(measured_at_sha, src_tree_sha, measured_at_note) is carried; the oracle
block (identity, clock, grading code) and `oracle_regraded_at_sha` are this
run's, stamped when it STARTS (_oracle.RunStamp); `--diff-out` writes the
per-row before/after. The grading code is this file, diff_real_roots.py (the
pass protocol) and _oracle.py.
"""
import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from diff_real_roots import (  # noqa: E402
    PIN, build_frame, oracle_record, run_to_fixpoint_full,
)
from _oracle import OracleError, RunStamp, get_oracle, job_output  # noqa: E402
from _measurement_provenance import cli_build_root, cli_platform  # noqa: E402

GRADER_FILES = ("scripts/tools/gen_apply_fixes_real_differential.py",
                "scripts/tools/diff_real_roots.py")
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
    log = job_output(work, toplevel, ".log")  # pdfTeX's job name (C-95)
    if not log.is_file():
        return ""
    for raw in log.read_bytes().split(b"\n"):
        if raw.startswith(b"!"):
            return raw.decode("utf-8", "replace").strip()[:200]
    return ""


# The CLI flag for each fixer scope. "all" applies every rule's fix, which is
# what every recorded artefact measured (the unqualified --apply-fixes before
# the OPEN-105 allow-list); "default" is the allow-list the CLI now applies.
SCOPE_FLAG = {"all": "--apply-fixes-all", "default": "--apply-fixes"}


def apply_fixes_tree(work: pathlib.Path, cli: pathlib.Path, timeout: int,
                     failures: list | None = None, scope: str = "all"):
    """Apply the fixer of the given SCOPE to every .tex in the tree, in place.

    scope "all" is the full fixer every recorded artefact measured; callers
    that do not pass it (simulate_fix_guard) keep that meaning.

    Every .tex, not just the root: STRUCT-001 inserted a preamble into `\\input`
    FRAGMENTS and killed their parents, and a root-only differential is blind
    to that whole class by construction.
    """
    changed = []
    for tex in sorted(work.rglob("*.tex")):
        before = tex.read_bytes()
        try:
            r = subprocess.run([str(cli), SCOPE_FLAG[scope], str(tex)],
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            if failures is not None:
                failures.append(f"{tex.relative_to(work)}: timeout")
            continue
        # ⚠ A NON-ZERO, NON-ONE EXIT IS A CRASH, NOT "NO EDITS". Before
        # 2026-09-25 this branch was skipped silently, so a fixer that raised
        # (measured: a relocated binary exits 2 with Rule_contracts_missing)
        # left every file untouched and the paper scored PRESERVED.
        if r.returncode not in (0, 1) and failures is not None:
            failures.append(f"{tex.relative_to(work)}: exit {r.returncode}")
        # BYTES, never text=True: real papers carry latin-1 and the CLI echoes
        # source fragments, so strict decoding raises mid-sweep (C-9 family).
        if r.returncode in (0, 1) and r.stdout and r.stdout != before:
            tex.write_bytes(r.stdout)
            changed.append(str(tex.relative_to(work)))
    return changed


def run_one(rec, root, cli, timeout, scope="all"):
    pkg = root / rec["arxiv_id"]
    out = {"arxiv_id": rec["arxiv_id"], "toplevel": rec["toplevel"]}
    # The work directory must be visible to the pinned-image oracle
    # (ADR-012 decision 7), so it comes from the oracle, never /private/tmp.
    with get_oracle().tempdir() as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        tex_env = get_oracle().tex_env(td)
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
        run0 = run_to_fixpoint_full(work, rec["toplevel"], tex_env, timeout)
        rc0 = run0.rc
        out["rc_before"] = rc0
        out["pdf_before"] = run0.pdf
        out["first_error_before"] = first_error(work, rec["toplevel"])
        if run0.timed_out:
            # A timeout is UNMEASURED, not "did not compile" (C-70's rule).
            out["cell"] = "instrument-error-timeout"
            return out
        # The §B.4 predicate (STRICT_TIER_DESIGN.md, E0): rc 0 AND a PDF.
        if not run0.compiles:
            out["cell"] = "excluded-did-not-compile"
            return out
        # Delete exactly what pdflatex created, so the post-fix compile cannot
        # inherit state the fixed document never produced.
        # Through the oracle (inside the container), not a host unlink: a
        # host-side delete leaves the container's view stale for about a
        # second and pdflatex then cannot re-create its log (measured,
        # _oracle.ContainerOracle.remove).
        get_oracle().remove(sorted(
            (x for x in work.rglob("*")
             if x.is_file() and x.relative_to(work) not in shipped),
            key=lambda x: -len(x.parts)))
        failures: list = []
        out["changed_files"] = apply_fixes_tree(work, cli, timeout, failures,
                                                scope)
        if failures:
            out["cell"] = "instrument-error-fixer-failed"
            out["fixer_failures"] = failures
            return out
        after_fix = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        if after_fix != shipped:
            out["cell"] = "instrument-error-file-set-changed"
            out["file_set_delta"] = sorted(
                str(x) for x in after_fix.symmetric_difference(shipped))
            return out
        run1 = run_to_fixpoint_full(work, rec["toplevel"], tex_env, timeout)
        rc1 = run1.rc
        out["rc_after"] = rc1
        out["pdf_after"] = run1.pdf
        out["first_error_after"] = first_error(work, rec["toplevel"])
        if run1.timed_out:
            out["cell"] = "instrument-error-timeout"
            return out
        out["cell"] = "preserved" if run1.compiles else "broken"
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--repo", default=".")
    ap.add_argument("--out", default="corpora/apply_fixes_real/results.json")
    ap.add_argument("--offset", type=int, default=DEFAULT_OFFSET)
    ap.add_argument("--n", type=int, default=DEFAULT_N)
    ap.add_argument("--timeout", type=int, default=180)
    # Default "all" for continuity with every recorded artefact, which measured
    # the full fixer. "default" measures the OPEN-105 allow-list. The choice
    # is recorded as provenance.fixer_scope so the two can never be confused.
    ap.add_argument("--fixer-scope", choices=sorted(SCOPE_FLAG),
                    default="all")
    ap.add_argument("--jobs", type=int, default=1,
                    help="papers graded in parallel")
    ap.add_argument("--cli-checkout", default=None,
                    help="run the CLI built in this checkout (its latex-parse/src "
                         "must be clean)")
    ap.add_argument("--regrade", action="store_true",
                    help="re-grade the artefact at --out (its window, its CLI "
                         "tree via --cli-checkout); carries its CLI provenance")
    ap.add_argument("--diff-out", default=None,
                    help="with --regrade: write the per-row before/after here")
    ns = ap.parse_args()

    repo = pathlib.Path(ns.repo).resolve()
    cli_root = pathlib.Path(ns.cli_checkout).resolve() if ns.cli_checkout else repo
    cli = cli_root / "_build/default/latex-parse/src/validators_cli.exe"
    if ns.cli_checkout and subprocess.run(
            ["git", "status", "--porcelain", "--", "latex-parse/src"], cwd=cli_root,
            capture_output=True, text=True).stdout.strip():
        print(f"[apply-fixes-real] FATAL: {cli_root}: latex-parse/src is dirty",
              file=sys.stderr)
        return 2
    old_doc = None
    if ns.regrade:
        if not ns.cli_checkout:
            print("[apply-fixes-real] FATAL: --regrade needs --cli-checkout (the "
                  "CLI tree the artefact records)", file=sys.stderr)
            return 2
        old_doc = json.loads((repo / ns.out).read_text())
        fr = old_doc["provenance"]["frame"]
        ns.offset, ns.n = fr["offset"], fr["n"]
        ns.fixer_scope = old_doc["provenance"].get("fixer_scope", ns.fixer_scope)
        tree = subprocess.run(["git", "--no-optional-locks", "rev-parse",
                               "HEAD:latex-parse/src"], cwd=cli_root,
                              capture_output=True, text=True).stdout.strip()
        if tree != old_doc["provenance"].get("src_tree_sha"):
            print(f"[apply-fixes-real] FATAL: the CLI checkout's engine tree {tree} "
                  f"is not the artefact's {old_doc['provenance'].get('src_tree_sha')}: "
                  f"a moved cell would not be the oracle's", file=sys.stderr)
            return 2
    try:
        stamp = RunStamp(GRADER_FILES, repo)
    except OracleError as e:
        print(f"[apply-fixes-real] FATAL: cannot stamp the grading code: {e}",
              file=sys.stderr)
        return 2
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
    # The ONE oracle: the pinned TeX Live image (ADR-012 decision 7). A host
    # pdflatex is never a substitute, so an unavailable oracle is exit 2.
    try:
        banner = get_oracle().banner
    except OracleError as e:
        print(f"[apply-fixes-real] FATAL: the pinned-image oracle is "
              f"unavailable: {e}", file=sys.stderr)
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

    # Papers are independent (each has its own work directory), so they may be
    # graded in parallel; rows keep the window's order.
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=max(1, ns.jobs)) as ex:
        rows = list(ex.map(
            lambda rec: run_one(rec, root, cli, ns.timeout, ns.fixer_scope),
            window))
    for i, r in enumerate(rows, 1):
        print(f"  [{i}/{len(window)}] {r['arxiv_id']:<16} {r['cell']}",
              flush=True)

    # An instrument error is an UNMEASURED row. Folding it into
    # "excluded_did_not_compile" (as len(rows) - len(compiled) did) would hide
    # it, so refuse to write the artefact at all.
    unmeasured = [r for r in rows if r["cell"].startswith("instrument-error")]
    if unmeasured:
        for r in unmeasured:
            print(f"[apply-fixes-real] FATAL: {r['arxiv_id']}: {r['cell']} "
                  f"{r.get('fixer_failures') or r.get('file_set_delta')}",
                  file=sys.stderr)
        print(f"[apply-fixes-real] FATAL: {len(unmeasured)} row(s) were not "
              f"measured; no artefact written.", file=sys.stderr)
        return 2
    compiled = [r for r in rows if r["cell"] in ("preserved", "broken")]
    broken = [r for r in compiled if r["cell"] == "broken"]
    why = stamp.check()
    if why:
        print(f"[apply-fixes-real] FATAL: nothing written: {why}", file=sys.stderr)
        return 2
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=cli_root,
                         capture_output=True, text=True).stdout.strip()
    doc = {
        "provenance": {
            "produced_by": "scripts/tools/gen_apply_fixes_real_differential.py",
            "measured_at_sha": sha,
            # Engine source anchor (C-64): comparable on any machine, unlike
            # cli_sha256, which only the producing machine can check.
            "src_tree_sha": subprocess.run(
                ["git", "--no-optional-locks", "rev-parse",
                 "HEAD:latex-parse/src"], cwd=cli_root, capture_output=True,
                text=True).stdout.strip() or None,
            "cli_sha256": sha256_file(cli),
            # The hash is only comparable on this platform (C-64).
            "cli_platform": cli_platform(),
            # And only within the checkout directory that built it (C-72).
            "cli_build_root": cli_build_root(cli),
            "frame": {"corpus": str(root.name), "frame_size": len(frame),
                      "selection": "sha256(arxiv_id) ascending",
                      "offset": ns.offset, "n": ns.n},
            # The oracle's identity, clock and grading code, stamped when the
            # run STARTED (OPEN-128 (4)/(8)).
            "oracle": dict(oracle_record(gc=stamp.gc)),
            "fix_scope": "every .tex in the tree, root and children",
            "fixer_scope": ns.fixer_scope,
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
    if old_doc is not None:
        # The CLI side is the recorded one (checked above): carry its
        # provenance, stamp the oracle side.
        for k in ("measured_at_sha", "measured_at_note", "src_tree_sha"):
            if k in old_doc["provenance"]:
                doc["provenance"][k] = old_doc["provenance"][k]
        doc["provenance"]["oracle_regraded_at_sha"] = stamp.head
        if ns.diff_out:
            before = {r["arxiv_id"]: r for r in old_doc["rows"]}
            diff_rows = []
            for r in rows:
                b = before.get(r["arxiv_id"], {})
                keys = sorted((set(b) | set(r)) - {"arxiv_id", "toplevel"})
                moved = [k for k in keys if b.get(k) != r.get(k)]
                diff_rows.append({"arxiv_id": r["arxiv_id"],
                                  "cell_before": b.get("cell"), "cell_after": r["cell"],
                                  "cell_changed": b.get("cell") != r["cell"],
                                  "fields_changed": moved,
                                  "before": {k: b.get(k) for k in moved},
                                  "after": {k: r.get(k) for k in moved}})
            dp = repo / ns.diff_out
            dp.parent.mkdir(parents=True, exist_ok=True)
            dp.write_text(json.dumps({
                "artefact": ns.out,
                "oracle_before": old_doc["provenance"].get("oracle"),
                "oracle_after": doc["provenance"]["oracle"],
                "regraded_at_sha": stamp.head,
                "summary": {"rows": len(diff_rows),
                            "cells_moved": sum(1 for d in diff_rows if d["cell_changed"]),
                            "rows_with_any_field_moved": sum(
                                1 for d in diff_rows if d["fields_changed"]),
                            "summary_before": old_doc.get("summary"),
                            "summary_after": doc["summary"]},
                "rows": diff_rows}, indent=1, ensure_ascii=False) + "\n")
            print(f"[apply-fixes-real] before/after diff written to {ns.diff_out}")
    outp = repo / ns.out
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")
    s = doc["summary"]
    pct = (100.0 * s["broken"] / s["compiled_before"]) if s["compiled_before"] else 0.0
    print(f"[apply-fixes-real] wrote {ns.out}: {s['broken']}/"
          f"{s['compiled_before']} = {pct:.1f}% of real COMPILING papers "
          f"broken by the {ns.fixer_scope!r}-scope fixer "
          f"({s['excluded_did_not_compile']} excluded, did not compile)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
