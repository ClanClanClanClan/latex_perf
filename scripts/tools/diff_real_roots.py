#!/usr/bin/env python3
"""Differential: --compile-check vs real pdflatex over REAL third-party papers.

Why this exists. The North-Star metric is "proven-verdict coverage at zero
false-READY on real papers", but every number the project quotes for it comes
from corpora/compile_check -- 66 hand-authored fixtures totalling 11,282 bytes,
mean 171 bytes, flat single files. A differential over that corpus measures the
corpus's own design. This one runs over whole arXiv source TREES: real
preambles, real package sets, real \\input siblings, real .bbl files.

WHY NOT extend diff_compile_check.sh. It globs a flat directory and compiles
each file in a mktemp holding only that file plus its *_part.tex siblings. A
real paper needs its whole tree, so every document would fail for missing-file
reasons and score FALSE-READY. And run_differential_test.py never invokes
pdflatex at all -- it diffs --layer ALL stdout between two git refs. This lifts
the DOCTRINE of diff_compile_check.sh (exit-code semantics, anti-vacuity,
timeout-is-not-a-failure) rather than its code.

THE CORPUS IS NOT IN THIS REPO and is not redistributable (arXiv source, mixed
licences). Point --corpus-root at it, or set LP_REAL_CORPUS. Only a manifest of
hashes is committed, so a run is reproducible-by-verification even though the
inputs cannot be shipped.

EXIT CODES, deliberately identical in meaning to diff_compile_check.sh:
  0  clean
  1  a NEW false-READY not in the allowlist          <- the cardinal bug
  2  infrastructure (missing binary, sha mismatch, ANY timeout, too many
     ungraded, or zero true-READY -- the anti-vacuity guard)
  3  oracle skew (the recorded grades came from a different oracle than
     the pinned image; see --rebaseline-oracle)
  4  over-rejection above the recorded baseline      <- the SAFE direction
Never conflate 1 and 4.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oracle import (  # noqa: E402
    IMAGE as ORACLE_IMAGE, OracleError, get_oracle, job_output)

PIN = "pdfTeX 3.141592653-2.6-1.40.29"
ORACLE = {
    "engine": "pdflatex",
    "distribution": "TeX Live 2026",
    "version": PIN,
    # Restricted shell-escape is pdflatex's default and has been the protocol
    # since OPEN-053; it was missing from this string (review of 2026-09-27).
    "protocol": ("-interaction=nonstopmode -halt-on-error, restricted "
                 "shell-escape (the pdflatex default, OPEN-053), up to 3 passes "
                 "(LaTeX is multi-pass; see run_to_fixpoint), PDF recorded "
                 "(compiles = rc 0 AND a PDF)"),
}


def oracle_record() -> dict:
    """ORACLE plus the pinned image's identity, as every artefact records it
    since the oracle-baseline change (ADR-012 decision 7): the image digest,
    the architecture the grade ran on, the TeX tree fingerprints and the
    backend. The banner alone pins the engine binary, never the macro layer."""
    prov = get_oracle().provenance()
    return dict(ORACLE, **{k: prov[k] for k in (
        "image", "arch", "tlpdb_sha256", "macro_layer_sha256", "fmt_sha256",
        "backend")})


def same_oracle(recorded: dict | None) -> bool:
    """True iff a recorded oracle block names the pinned image. A block with
    no `image` was graded before the oracle-baseline change, by whatever TeX
    Live the grading machine had, and is never carried forward."""
    recorded = recorded or {}
    return (recorded.get("image") == ORACLE_IMAGE
            and PIN in str(recorded.get("version", "")))

# A missing converted-EPS or graphics file is a property of how the paper was
# BUILT (arXiv ran epstopdf via shell-escape), not of the document's validity.
# Scoring it FAILS would invent false-READYs out of infrastructure.
INFRA = re.compile(
    r"-eps-converted-to\.pdf' not found"
    r"|Package pdftex\.def Error: File .* not found"
    r"|epstopdf")


REASON_TOKEN = re.compile(r"\b(T\d|[A-Z]{2,8}-\d{3})\b")


def scrape_reasons(stdout: str) -> list[str]:
    """The reason tokens of one `--compile-check` run, e.g. ["T5", "DELIM-003"].

    Scope (ADR-012, M0): the scrape reads the output UP TO the first line that
    starts with `TIER\t`. Everything before that line is the frozen surface
    (the MODEL-CONNECTED line, the READY/NOT-READY token line, the indented
    reasons) and is byte-identical to what the CLI printed before M0. The TIER
    line and the `why not strict:` lines after it are diagnostic: they quote
    file names and macro definitions from the author's source, and a name like
    `\\T1` or `sec-001.tex` would otherwise be recorded as a BLOCKING reason.
    On output with no TIER line (every binary before M0) this is exactly the
    old whole-buffer scrape, which is the compatibility argument; it is pinned
    by scripts/tools/check_compile_check_consumers.py.
    """
    head = []
    for line in stdout.split("\n"):
        if line.startswith("TIER\t"):
            break
        head.append(line)
    return sorted(set(REASON_TOKEN.findall("\n".join(head))))


def die(code: int, msg: str) -> int:
    print(f"[real-roots] FATAL: {msg}", file=sys.stderr)
    return code


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sha256_tree(d: Path) -> str:
    """Order-independent digest of every file in the package."""
    h = hashlib.sha256()
    for f in sorted(d.rglob("*")):
        if f.is_file():
            h.update(str(f.relative_to(d)).encode())
            h.update(hashlib.sha256(f.read_bytes()).digest())
    return h.hexdigest()


def declared_texlive(meta: dict):
    """arXiv records `texlive_version` at the TOP LEVEL of 00README.json.

    It was read as `meta["process"]["texlive_version"]`, and `process` carries
    exactly one key — `compiler` — so the lookup returned None on every paper
    ever sampled and `declared_texlive` was null on all 200 recorded rows.

    Measured over the 2,821 packages in the corpus: the key is present at the
    top level in 1,880 (66.6%) and absent in 941; `process.*` is `{"compiler"}`
    and nothing else, in all 2,821.

    ⚠ Every single declared value is **2023**. Not one paper declares the
    oracle's TL2026, so the drift control README.md asks for — "the matrix
    restricted to declared_texlive == 2026" — selects the empty set and cannot
    be computed from this corpus at all. See the README for what replaced it.
    """
    return meta.get("texlive_version")


def build_frame(root: Path) -> list[dict]:
    """Papers arXiv itself declares as pdflatex with exactly one toplevel.

    Root detection uses arXiv's 00README.json, never a \\documentclass scan:
    a substring scan counts commented-out declarations and is off by 66 files
    across this tree.
    """
    frame = []
    skipped: list[str] = []
    for d in sorted(root.iterdir()):
        readme = d / "00README.json"
        if not readme.is_file():
            continue
        try:
            meta = json.loads(readme.read_text())
        except (json.JSONDecodeError, OSError):
            # An unreadable 00README.json silently shrank the FRAME, and the
            # frame size is a published number ("frame 2719"). Count them so a
            # systematic corpus problem is visible instead of rounding away.
            skipped.append(d.name)
            continue
        if (meta.get("process") or {}).get("compiler") != "pdflatex":
            continue
        tops = [s["filename"] for s in meta.get("sources", [])
                if s.get("usage") == "toplevel"]
        if len(tops) != 1:
            continue
        top = d / tops[0]
        if not top.is_file():
            continue
        frame.append({
            "arxiv_id": d.name,
            "toplevel": tops[0],
            "declared_compiler": "pdflatex",
            "declared_texlive": declared_texlive(meta),
        })
    if skipped:
        print(f"[real-roots] WARNING: {len(skipped)} package(s) have an "
              f"unreadable 00README.json and are NOT in the frame: "
              f"{', '.join(skipped[:5])}{'...' if len(skipped) > 5 else ''}")
    return frame


def select(frame: list[dict], n: int) -> list[dict]:
    """Deterministic, and stable under corpus growth.

    Ordering by sha256(arxiv_id) rather than by name, mtime or filesystem order
    means extending N from 200 to 400 keeps the first 200 identical, so a later
    baseline stays comparable to an earlier one.
    """
    return sorted(frame, key=lambda r: hashlib.sha256(
        r["arxiv_id"].encode()).hexdigest())[:n]


def size_bucket(nbytes: int) -> str:
    if nbytes < 10_000:
        return "<10KB"
    return "10-100KB" if nbytes < 100_000 else ">100KB"


MAX_PASSES = 3


def run_to_fixpoint(work: Path, toplevel: str, env: dict, timeout: int,
                    max_passes: int = MAX_PASSES) -> tuple[int, int]:
    """Run pdflatex until it succeeds, up to [max_passes]. Returns (rc, passes).

    ⚠ THE ORACLE USED TO RUN EXACTLY ONE PASS, AND THAT MISCOUNTED REAL PAPERS.
    LaTeX is a multi-pass system by construction: `.aux` is written on one pass
    and read on the next, which is why every real build tool (latexmk, and
    arXiv's own AutoTeX) iterates. Judging a document on pass 1 alone marks a
    perfectly ordinary document as broken.

    Measured on the 11 recorded false-READYs: the THREE natbib papers
    (2507.10419v1, 2506.22536v1, 2506.17405v1) fail pass 1 with
    "! Package natbib Error: Bibliography not compatible with author-year
    citations." and compile **rc 0 with a PDF on pass 2**, unedited, in the same
    directory — natbib cannot know the citation style until it has read the
    `.bbl`/`.aux` that pass 1 produces. The other eight (the `\\c@<env>`
    collisions) fail identically on every pass, so this does not launder them.

    `-halt-on-error` is DELIBERATELY KEPT. The defect being corrected is the
    pass count, not the error policy; relaxing both at once would have quietly
    reclassified the `\\c@` class too.

    ⚠ SUCCESS IS NOT ENOUGH — IT MUST BE STABLE, AND THE FIRST VERSION OF THIS
    FUNCTION GOT THAT WRONG. Early-exiting on the first rc 0 misses a document
    that succeeds and then breaks ITSELF on the next run. Counterexample, in the
    corpus as `fr_toc_second_pass`:

        \\tableofcontents
        \\addcontentsline{toc}{section}{\\protect\\undefinedcmdxyz}
      -> pass 1 rc 0 with a PDF, pass 2 rc 1 "! Undefined control sequence"

    `\\addcontentsline` writes a raw token into `\\jobname.toc`; `\\tableofcontents`
    reads that file at the top of the body on the NEXT run. The `.aux` cannot do
    this — `\\enddocument` closes and immediately re-inputs it in the SAME run
    (latex.ltx:15483-15489), so aux poisoning always poisons its own run first.
    The write-once-read-next-run files are `.toc`/`.lof`/`.lot`.

    So this runs to the first success and then does ONE CONFIRMING PASS. A
    healthy document costs 2 runs, not 3; an unstable one is caught. The
    returned rc is the confirming pass's when it disagrees, because the LAST
    state is the one a real build tool would leave the author in.

    ONE ORACLE (ADR-012 decision 7). The runs go through `_oracle.get_oracle()`:
    the pinned TeX Live image, in a container locally and natively inside CI's
    image. Nothing here may call a host `pdflatex`. The flags are unchanged:
    `-interaction=nonstopmode -halt-on-error` and pdflatex's DEFAULT
    restricted shell-escape (OPEN-053: `-no-shell-escape` made 19 of 22
    affected frame papers grade as failures although they compile in the real
    world, and disagreed with the required tex-oracle gate). `work` must come
    from `get_oracle().tempdir()`, which is visible inside the container.
    """
    r = get_oracle().run_to_fixpoint(work, toplevel, env, timeout, max_passes)
    return r.rc, r.passes


def run_to_fixpoint_full(work: Path, toplevel: str, env: dict, timeout: int,
                         max_passes: int = MAX_PASSES):
    """As run_to_fixpoint, returning the `_oracle.OracleRun` (rc, passes, pdf)."""
    return get_oracle().run_to_fixpoint(work, toplevel, env, timeout, max_passes)


def row_compiles(d: dict) -> bool:
    """The oracle predicate on a recorded row: rc 0 AND a PDF (STRICT_TIER_DESIGN
    B.4, E0). Rows graded before the PDF was recorded carry no `pdflatex_pdf`
    and are read by rc alone, which is what they were graded by."""
    return d.get("pdflatex_rc") == 0 and d.get("pdflatex_pdf", True) is not False


def run_one(rec: dict, root: Path, cli: Path, timeout: int) -> dict:
    pkg = root / rec["arxiv_id"]
    out = dict(rec)
    with get_oracle().tempdir() as td:
        work = Path(td) / "w"
        # NEVER compile in the corpus directory: pdflatex writes .aux/.log/.pdf
        # next to the source, which would mutate the very bytes the manifest
        # hashes and make the run non-reproducible.
        shutil.copytree(pkg, work)
        top = work / rec["toplevel"]
        out["bytes"] = top.stat().st_size
        out["size_bucket"] = size_bucket(out["bytes"])

        env = dict(os.environ, L0_VALIDATORS="pilot")
        try:
            # BYTES, never text=True. Real papers carry latin-1 and other
            # non-UTF-8 bytes, and both the CLI and pdflatex echo source
            # fragments into their output; strict decoding raises mid-run and
            # kills the sweep. The same lesson is recorded for the fixer
            # round-trip gate. Decode for inspection only, with errors=replace.
            r = subprocess.run([str(cli), "--compile-check", str(top)],
                               capture_output=True, timeout=timeout, env=env)
            stdout = r.stdout.decode("utf-8", errors="replace")
            out["cli_rc"] = r.returncode
            out["cli_verdict"] = "READY" if r.returncode == 0 else "NOT-READY"
            out["cli_reasons"] = scrape_reasons(stdout)
        except subprocess.TimeoutExpired:
            out["cli_rc"] = -1
            out["cli_verdict"] = "TIMEOUT"
            out["cli_reasons"] = []

        tex_env = get_oracle().tex_env(td)
        run = run_to_fixpoint_full(work, rec["toplevel"], tex_env, timeout)
        out["pdflatex_rc"] = run.rc
        out["pdflatex_passes"] = run.passes
        out["pdflatex_pdf"] = run.pdf

        log = job_output(work, rec["toplevel"], ".log")  # pdfTeX's job name
        first_full = ""
        if log.is_file():
            loglines = log.read_text(errors="replace").split("\n")
            for i, line in enumerate(loglines):
                if line.startswith("!"):
                    # TeX WRAPS log lines at ~79 columns, so an error message is
                    # routinely split across several. Classifying on one line
                    # mis-scored 2507.08096v1 as FALSE-READY: its message is
                    # "! Package pdftex.def Error: File `...-eps-converted-to.pdf'
                    # not found" and the "not found" the infra pattern needs sits
                    # on the FOLLOWING line. Take the wrapped block.
                    # Join with NO separator: TeX's wrap is a hard column break,
                    # not a word break, so this message arrives as
                    #   "...-eps-converted-to.pdf' n"  +  "ot found: using draft"
                    # and a space-join yields "n ot found", which still does not
                    # match. Concatenation is the exact inverse of the wrap.
                    first_full = "".join(loglines[i:i + 4])
                    break
        # Classify on the FULL line, store a truncated copy. Matching the
        # truncated string mis-scored 2507.08096v1 as FALSE-READY: its error is
        # "! Package pdftex.def Error: File `...-eps-converted-to.pdf' not
        # found", and the "not found" the pattern needs falls past 160 chars.
        out["first_error"] = first_full[:160]

    if out["pdflatex_rc"] == -1 or out["cli_rc"] == -1:
        out["cell"] = "ungraded-timeout"
    elif out["pdflatex_rc"] != 0 and INFRA.search(first_full):
        out["cell"] = "ungraded-infra"
    else:
        compiles = row_compiles(out)
        ready = out["cli_rc"] == 0
        out["pdflatex_verdict"] = "COMPILES" if compiles else "FAILS"
        out["cell"] = ("true-READY" if (ready and compiles) else
                       "FALSE-READY" if (ready and not compiles) else
                       "false-NOT-READY" if compiles else "true-NOT-READY")
    return out


def refresh_cli_only(repo: Path, root: Path, outdir: Path, banner: str,
                     timeout: int, results_name: str = "results.json") -> int:
    """Recompute ONLY the CLI verdict, reusing the recorded pdflatex results.

    A full run recompiles 200 papers with pdflatex and takes ~20 minutes. That
    is the right thing when the CORPUS or the ENGINE changed. It is waste when
    only the tool changed — and the tool changes constantly, which is why
    results.json went three PRs stale and the published headline read 56.8%
    while main measured 65.8%.

    The shortcut is sound under exactly two conditions, and BOTH are asserted
    here rather than assumed:

      * the corpus is unchanged — every paper's sha256_tree still matches the
        manifest, so the documents are byte-identical;
      * the engine is unchanged — pdflatex --version still matches the pin.

    Given those, a pdflatex verdict is a property of the DOCUMENT, not of our
    binary, so it can be carried forward. The CLI verdict cannot, so it is
    recomputed. If either condition fails this refuses and tells you to run the
    full sweep.

    `results_name` picks the artefact; a sample drawn with --offset has its
    own manifest, named the way --record names it (results_sample3.json ->
    manifest_sample3.json). Sample 3 is the sealed VIRGIN sample (OPEN-119):
    refreshing its CLI side is a re-measurement, taken only after a change
    was validated on other documents.
    """
    results_path = outdir / results_name
    manifest_path = outdir / (
        "manifest.json" if results_name == "results.json"
        else results_name.replace("results", "manifest", 1))
    if not results_path.is_file() or not manifest_path.is_file():
        return die(2, "no recorded results to refresh — run a full sweep first")
    res = json.loads(results_path.read_text())
    man = {d["arxiv_id"]: d for d in json.loads(manifest_path.read_text())["docs"]}

    if not same_oracle(res.get("oracle")):
        return die(3, f"oracle skew: the recorded pdflatex grades were taken by "
                      f"{res.get('oracle', {}).get('image') or 'a host TeX Live (no image recorded)'}, "
                      f"not the pinned image {ORACLE_IMAGE}. A CLI-only refresh "
                      f"cannot carry them forward; re-grade with --repass "
                      f"--repass-scope all --rebaseline-oracle.")

    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    env = dict(os.environ, L0_VALIDATORS="pilot")
    changed = []
    for i, d in enumerate(res["docs"], 1):
        rec = man.get(d["arxiv_id"])
        if rec is None:
            return die(2, f"{d['arxiv_id']} missing from the manifest")
        if sha256_tree(root / d["arxiv_id"]) != rec["sha256_tree"]:
            return die(2, f"{d['arxiv_id']}: tree sha differs from the manifest — "
                          f"the corpus changed, so pdflatex verdicts cannot be "
                          f"carried forward. Run the full sweep.")
        top = root / d["arxiv_id"] / d["toplevel"]
        try:
            r = subprocess.run([str(cli), "--compile-check", str(top)],
                               capture_output=True, timeout=timeout, env=env)
            rc = r.returncode
            reasons = scrape_reasons(r.stdout.decode("utf-8", "replace"))
        except subprocess.TimeoutExpired:
            return die(2, f"{d['arxiv_id']}: CLI timeout — the run is void")
        before = d["cell"]
        d["cli_rc"], d["cli_verdict"] = rc, ("READY" if rc == 0 else "NOT-READY")
        d["cli_reasons"] = reasons
        # The ungraded classes are STICKY, but only while they still apply.
        # `ungraded-infra` is assigned iff pdflatex_rc != 0 AND the first error
        # matches INFRA; `ungraded-timeout` iff an rc is -1. A re-grade that
        # makes the document COMPILE (rc 0) therefore invalidates the label,
        # and an unconditional `pass` here made it permanent: OPEN-053 flipped
        # 2507.08096v1 from rc 1 to rc 0 and the row kept `ungraded-infra`,
        # keeping a compiling, READY, PREMISE-CERTIFIED document out of the
        # published metric for two commits. Re-derive when rc == 0.
        if d["cell"].startswith("ungraded") and d.get("pdflatex_rc", -1) != 0:
            pass                                   # still genuinely ungraded
        else:
            compiles = row_compiles(d)
            ready = rc == 0
            d["cell"] = ("true-READY" if (ready and compiles) else
                         "FALSE-READY" if (ready and not compiles) else
                         "false-NOT-READY" if compiles else "true-NOT-READY")
        if d["cell"] != before:
            changed.append((d["arxiv_id"], before, d["cell"]))
        print(f"  [{i}/{len(res['docs'])}] {d['arxiv_id']:16s} {d['cell']}",
              flush=True)

    res["counts"] = dict(collections.Counter(d["cell"] for d in res["docs"]))
    res["measured_at_sha"] = git_head(repo)
    res["src_tree_sha"] = engine_tree(repo)
    res["measured_at"] = "cli-only refresh; pdflatex verdicts carried forward"
    results_path.write_text(json.dumps(res, indent=1) + "\n")
    print(f"\n[real-roots] refreshed: {len(changed)} cell change(s)")
    for a, b, c in changed:
        print(f"    {a:16s} {b} -> {c}")
    print(f"[real-roots] measured_at_sha = {res['measured_at_sha']}")
    return 0


def git_head(repo: Path) -> str:
    r = subprocess.run(["git", "--no-optional-locks", "rev-parse", "HEAD"],
                       cwd=repo, capture_output=True, text=True)
    return r.stdout.strip() or "unknown"


def engine_tree(repo: Path) -> str:
    """git tree id of latex-parse/src at HEAD. See C-64 / OPEN-101.

    Recorded alongside measured_at_sha so a checker can establish that the
    engine source is UNCHANGED since the measurement, rather than merely
    bounding how many commits have gone by. Unlike cli_sha256 it is comparable
    on any machine: CI builds ubuntu-22.04 ELF, artefacts are produced by a
    maintainer's macOS arm64 binary, and those hashes can never agree.
    """
    r = subprocess.run(["git", "--no-optional-locks", "rev-parse",
                        "HEAD:latex-parse/src"],
                       cwd=repo, capture_output=True, text=True)
    return r.stdout.strip() or "unknown"


def repass_failures(repo: Path, root: Path, outdir: Path, banner: str,
                    timeout: int, scope: str = "failures",
                    results_name: str = "results.json",
                    sample_offset: int | None = None,
                    rebaseline: bool = False, diff_out: str | None = None,
                    jobs: int = 1) -> int:
    """Re-grade recorded rows under the multi-pass oracle. `scope` picks which.

    ⚠ THE DEFAULT SCOPE IS THE ONE DIRECTION THAT CANNOT FIND A FALSE-READY,
    AND FOR A LONG TIME IT WAS THE ONLY SCOPE THIS TOOL HAD (OPEN-103, C-63).
    `failures` re-runs documents already recorded as failing, so its outcomes
    are "still fails" or "actually compiles" — it can only ever move a verdict
    toward true-READY/false-NOT-READY. A document recorded rc 0 on a single
    pass was never revisited. That is why `results.json` read "APPLIED TO
    18/200 rows": 13 failures re-passed here, 5 successes from an earlier run,
    and 180 true-READY rows carrying an unconfirmed single-pass grade — with
    100% of the protocol deficit sitting on the soundness side, where the only
    direction a row can move is INTO false-READY.

    The paragraph below this one already said so ("run the full sweep before
    publishing a headline number"), and the headline was published anyway.
    `scope="unmeasured"` is that instruction made executable without paying for
    a full re-sweep: it re-grades every row that has never had the protocol
    applied, which is the honest way to take the APPLIED-TO clause to n/n.

      failures    rows with pdflatex_rc not in (0, None)   — the legacy default
      unmeasured  rows with no pdflatex_passes             — completes the protocol
      all         every row                                — a full re-grade

    The single-pass oracle marked as failures documents that merely needed a
    second pass. Correcting that does not require re-running the whole sweep:
    extra passes can turn a failure into a success, never the reverse, so a
    document already recorded `pdflatex_rc == 0` cannot change. Only the
    failures are re-run.

    ⚠ The one shape that assumption misses is a document whose SECOND pass is
    broken by the `.aux` its first pass wrote (the `fr_corrupt_aux` fixture is
    exactly this). Such a paper would have passed on one pass and would now
    fail. It cannot be detected without the full sweep, so run the full sweep
    before publishing a headline number; this mode is for correcting a recorded
    baseline in place, and it says so in `results.json`.

    ORACLE-BASELINE CHANGE (ADR-012 decision 7). A recorded grade is carried or
    re-used only when it was taken by the pinned image (`same_oracle`). Grades
    from before the change name no image: they came from the grading machine's
    own TeX Live. `rebaseline=True` is the one sanctioned way across that line:
    it requires scope `all` (every row re-graded, nothing carried), keeps the
    CLI verdicts (they do not depend on pdflatex), and writes a per-row
    before/after diff to `diff_out`, because the diff IS the finding.

    SAMPLE 2. `results_name` picks the artefact; sample 2
    (`results_sample2.json`) has no hash manifest, so `sample_offset` names its
    window in the frame and the ids are asserted equal to that window before
    anything is graded; each row then records the `sha256_tree` it was graded
    on.

    Asserts the corpus (per-paper `sha256_tree`) and the oracle first: a
    verdict carried forward from a different corpus or oracle is not evidence.
    """
    results_path = outdir / results_name
    manifest_path = outdir / "manifest.json"
    if not results_path.is_file():
        return die(2, "no recorded results to re-pass — run a full sweep first")
    res = json.loads(results_path.read_text())
    if sample_offset is None:
        if not manifest_path.is_file():
            return die(2, "no manifest.json to verify the corpus against")
        man = {d["arxiv_id"]: d for d in json.loads(manifest_path.read_text())["docs"]}
    else:
        frame = build_frame(root)
        ordered = select(frame, len(frame))
        window = ordered[sample_offset:sample_offset + len(res["docs"])]
        want_ids = {d["arxiv_id"] for d in window}
        have_ids = {d["arxiv_id"] for d in res["docs"]}
        if want_ids != have_ids:
            return die(2, f"{results_name}: its {len(have_ids)} ids are not ranks "
                          f"{sample_offset}..{sample_offset + len(res['docs']) - 1} "
                          f"of the frame ({len(want_ids ^ have_ids)} differ)")
        man = {d["arxiv_id"]: dict(d, sha256_tree=d.get("sha256_tree")) for d in window}

    if not same_oracle(res.get("oracle")) and not rebaseline:
        return die(3, f"oracle skew: {results_name} was graded by "
                      f"{(res.get('oracle') or {}).get('image') or 'a host TeX Live (no image recorded)'}, "
                      f"not the pinned image {ORACLE_IMAGE}. Re-grading under a "
                      f"different oracle is not a correction, it is a new "
                      f"measurement: pass --rebaseline-oracle with "
                      f"--repass-scope all.")
    if rebaseline and scope != "all":
        return die(2, "--rebaseline-oracle re-grades EVERY row; use --repass-scope all")

    SCOPES = {
        "failures": lambda d: d.get("pdflatex_rc") not in (0, None),
        "unmeasured": lambda d: not d.get("pdflatex_passes"),
        "all": lambda d: True,
    }
    if scope not in SCOPES:
        return die(2, f"unknown --repass-scope {scope!r}; pick one of "
                      f"{sorted(SCOPES)}")
    failures = [d for d in res["docs"] if SCOPES[scope](d)]
    print(f"[real-roots] re-passing {len(failures)} row(s) of {results_name} in "
          f"scope {scope!r} under up to {MAX_PASSES} passes "
          f"(run-to-success plus ONE CONFIRMING PASS), oracle "
          f"{get_oracle().backend}:{ORACLE_IMAGE}, jobs={jobs}")
    for d in failures:
        rec = man.get(d["arxiv_id"])
        if rec is None:
            return die(2, f"{d['arxiv_id']} missing from the manifest")
        tree = sha256_tree(root / d["arxiv_id"])
        if rec.get("sha256_tree") and tree != rec["sha256_tree"]:
            return die(2, f"{d['arxiv_id']}: tree sha differs from the manifest — "
                          f"the corpus changed under the baseline. Run the sweep.")
        if d.get("sha256_tree") and tree != d["sha256_tree"]:
            return die(2, f"{d['arxiv_id']}: tree sha differs from the one this "
                          f"row was graded on")
        d["_tree"] = tree

    lower = any(str(d.get("pdflatex_verdict", "")).islower() and d.get("pdflatex_verdict")
                for d in res["docs"])

    def grade(d):
        oracle = get_oracle()
        with oracle.tempdir() as td:
            work = Path(td) / "w"
            shutil.copytree(root / d["arxiv_id"], work)
            run = run_to_fixpoint_full(work, d["toplevel"], oracle.tex_env(td),
                                       timeout)
            first = ""
            log = job_output(work, d["toplevel"], ".log")  # pdfTeX's job name
            if log.is_file():
                ll = log.read_text(errors="replace").split("\n")
                for i, line in enumerate(ll):
                    if line.startswith("!"):
                        first = "".join(ll[i:i + 4])
                        break
        return run, first

    with ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
        graded = list(ex.map(grade, failures))

    changed, diff_rows = [], []
    for i, (d, (run, first_full)) in enumerate(zip(failures, graded), 1):
        rc, passes = run.rc, run.passes
        before = {"cell": d["cell"], "pdflatex_rc": d.get("pdflatex_rc"),
                  "pdflatex_verdict": d.get("pdflatex_verdict"),
                  "first_error": d.get("first_error", "")}
        tree = d.pop("_tree")
        if sample_offset is not None:
            d["sha256_tree"] = tree
        d["pdflatex_rc"], d["pdflatex_passes"] = rc, passes
        d["pdflatex_pdf"] = run.pdf
        if "passes" in d:
            d["passes"] = passes
        if "graded_by" in d:
            d["graded_by"] = "pinned-image oracle (ADR-012 decision 7)"
        d["first_error"] = first_full[:160]
        cell_before = d["cell"]
        if rc == -1:
            d["cell"] = "ungraded-timeout"
        elif rc != 0 and INFRA.search(first_full):
            d["cell"] = "ungraded-infra"
        else:
            compiles, ready = row_compiles(d), d["cli_rc"] == 0
            v = "COMPILES" if compiles else "FAILS"
            d["pdflatex_verdict"] = v.lower() if lower else v
            d["cell"] = ("true-READY" if (ready and compiles) else
                         "FALSE-READY" if (ready and not compiles) else
                         "false-NOT-READY" if compiles else "true-NOT-READY")
        after = {"cell": d["cell"], "pdflatex_rc": rc,
                 "pdflatex_verdict": d.get("pdflatex_verdict"),
                 "pdflatex_pdf": run.pdf, "first_error": d["first_error"]}
        diff_rows.append({"arxiv_id": d["arxiv_id"], "toplevel": d["toplevel"],
                          "cli_rc": d.get("cli_rc"), "before": before,
                          "after": after, "passes": passes,
                          "cell_changed": d["cell"] != cell_before})
        if d["cell"] != cell_before:
            changed.append((d["arxiv_id"], cell_before, d["cell"], passes))
        print(f"  [{i}/{len(failures)}] {d['arxiv_id']:16s} "
              f"rc={rc} passes={passes} pdf={run.pdf} {d['cell']}", flush=True)

    if any(d["cell"] == "ungraded-timeout" for d in res["docs"]):
        return die(2, "a pdflatex TIMEOUT occurred during the re-grade; nothing "
                      "written. A timeout would score as FAILS and could "
                      "manufacture a false-READY.")

    res["counts"] = dict(collections.Counter(d["cell"] for d in res["docs"]))

    # ⚠ DO NOT PUBLISH A PROTOCOL THAT WAS NOT APPLIED TO EVERY ROW. This used
    # to assign `res["oracle"] = ORACLE` wholesale, so results.json advertised
    # "up to 3 passes" while only the FAILURES had been re-run — 182 of 200 rows
    # still carried their original single-pass grade and a null
    # `pdflatex_passes`. gen_project_state.py prints that protocol string
    # verbatim into the published block, so the overstatement propagated into
    # the headline. Record what was actually measured, per row and in aggregate.
    remeasured = sum(1 for d in res["docs"] if d.get("pdflatex_passes"))
    # ⚠ The "remainder" clause is only TRUE while a remainder exists. Caught by
    # the scope=unmeasured pilot: at 3/3 it still published "the remainder carry
    # a single-pass grade from an earlier run", which is a false sentence about
    # an empty set — and this string is printed verbatim into the published
    # block by gen_project_state.py, so it would have become the next
    # corrections-log entry. State the full-coverage case as its own sentence.
    _n = len(res["docs"])
    rec_oracle = oracle_record()
    res["oracle"] = dict(rec_oracle, protocol=(
        f"{ORACLE['protocol']} — APPLIED TO ALL {_n}/{_n} rows"
        if remeasured == _n else
        f"{ORACLE['protocol']} — APPLIED TO {remeasured}/{_n} rows; "
        f"the remainder carry a single-pass grade from an earlier run"))
    if sample_offset is None:
        res["measured_at_sha"] = git_head(repo)
        res["src_tree_sha"] = engine_tree(repo)
    else:
        # Sample 2's CLI verdicts still have no in-repo producer (OPEN-081), so
        # its measured_at_sha stays as it was; only the oracle side is stamped.
        res["oracle_regraded_at_sha"] = git_head(repo)
    _scope_note = {
        "failures": ("recorded FAILURES only; documents already recorded "
                     "pdflatex_rc 0 were NOT revisited, so this pass cannot "
                     "discover a false-READY (OPEN-103)"),
        "unmeasured": ("every row that had never had the multi-pass protocol "
                       "applied, INCLUDING recorded successes, so a document "
                       "that compiles on pass 1 and breaks itself on pass 2 "
                       "is detectable"),
        "all": "every row, regardless of prior grade",
    }[scope]
    measured = (f"multi-pass re-grade, scope={scope}: {_scope_note} "
                f"(<= {MAX_PASSES} passes, {remeasured}/{len(res['docs'])} "
                f"rows now carry a pdflatex_passes count); CLI verdicts "
                f"carried forward from the prior run")
    if rebaseline:
        measured = ("ORACLE-BASELINE CHANGE (ADR-012 decision 7): every row "
                    "re-graded under the pinned TeX Live image "
                    f"{ORACLE_IMAGE} ({rec_oracle['arch']}, "
                    f"{rec_oracle['backend']} backend); " + measured)
    res["measured_at"] = measured
    results_path.write_text(json.dumps(res, indent=1) + "\n")
    if rebaseline and sample_offset is None:
        # The frame manifest carries the same oracle block; it names who
        # graded the sample, so it moves with the re-grade.
        mdoc = json.loads(manifest_path.read_text())
        mdoc["oracle"] = dict(rec_oracle, protocol=mdoc["oracle"].get(
            "protocol", rec_oracle["protocol"]))
        manifest_path.write_text(json.dumps(mdoc, indent=2) + "\n")
    if diff_out:
        Path(diff_out).parent.mkdir(parents=True, exist_ok=True)
        Path(diff_out).write_text(json.dumps({
            "artefact": str(results_path.relative_to(repo)),
            "oracle_after": rec_oracle,
            "rows": diff_rows}, indent=1) + "\n")
        print(f"[real-roots] per-row before/after diff written to {diff_out}")
    print(f"\n[real-roots] {len(changed)} cell(s) changed:")
    for aid, a, b, p in changed:
        print(f"    {aid:16s} {a} -> {b}  (passes {p})")
    # A row entering FALSE-READY is the cardinal bug, and under scope=unmeasured
    # it is the EXPECTED direction of discovery, not a surprise. Per ADR-011 a
    # rise is a publication event, not a regression — say it loudly here so it
    # cannot be scrolled past. The exit code stays 0 on purpose: this is a
    # measurement command, and the gates downstream are what enforce.
    new_fr = [c for c in changed if c[2] == "FALSE-READY"]
    if new_fr:
        print(f"\n[real-roots] ⚠ {len(new_fr)} NEW FALSE-READY row(s) — the "
              f"cardinal bug, found by confirming a grade nobody had confirmed:")
        for aid, a, b, p in new_fr:
            print(f"    {aid:16s} {a} -> {b}  (failed on pass {p})")
        print("[real-roots] Publish it. ADR-011 decision 3.")
    print(f"[real-roots] counts now: {res['counts']}")
    return 0


def refresh_metadata_only(root: Path, outdir: Path) -> int:
    """Re-read the DECLARED metadata into manifest.json. No pdflatex, no CLI.

    `declared_texlive` is descriptive metadata copied out of 00README.json; it
    is never a filter (build_frame selects on `process.compiler` and the
    toplevel count, and select() orders by sha256 of the arxiv id), so
    backfilling it cannot move the frame or the sample. Only the recorded value
    changes.

    The per-paper `sha256_tree` is still asserted before anything is rewritten:
    if the corpus moved under the baseline, the metadata in it is not the
    metadata that was measured, and silently refreshing would launder that.
    """
    manifest_path = outdir / "manifest.json"
    if not manifest_path.is_file():
        return die(2, "no manifest to refresh — run a full sweep first")
    man = json.loads(manifest_path.read_text())
    had_before = sum(1 for d in man["docs"] if d.get("declared_texlive") is not None)
    changed = 0
    for d in man["docs"]:
        if sha256_tree(root / d["arxiv_id"]) != d["sha256_tree"]:
            return die(2, f"{d['arxiv_id']}: tree sha differs from the manifest "
                          f"— the corpus changed under the baseline, so its "
                          f"metadata is not what was measured. Run the sweep.")
        meta = json.loads((root / d["arxiv_id"] / "00README.json").read_text())
        was, now = d.get("declared_texlive"), declared_texlive(meta)
        if was != now:
            d["declared_texlive"] = now
            changed += 1
    # ⚠ CHECK BEFORE WRITING. This used to write the manifest and THEN test the
    # result, so a broken extraction destroyed the recorded metadata before the
    # guard could fire — the guard exited 2 with the damage already on disk.
    # And it only caught TOTAL loss (`have == 0`), so a 131 -> 1 degradation
    # wrote itself out and exited 0 reporting success.
    have = sum(1 for d in man["docs"] if d["declared_texlive"] is not None)
    if have < had_before:
        return die(2, f"refusing to write: {had_before} row(s) carried a "
                      f"declared version before, only {have} would after. The "
                      f"extraction regressed; the manifest is UNCHANGED on disk.")
    manifest_path.write_text(json.dumps(man, indent=1) + "\n")
    print(f"[real-roots] metadata refreshed: {changed} row(s) changed; "
          f"{have}/{len(man['docs'])} now carry a declared TeX Live version")
    if have == 0:
        return die(2, "still 0 rows with a declared version — the extraction is "
                      "wrong again; refusing to report success")
    return 0


def main() -> int:  # noqa: C901
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--n", type=int, default=200)
    ap.add_argument("--offset", type=int, default=0,
                    help="first frame rank of the sample (0 = sample 1; sample 2 "
                         "is 200; sample 3, the virgin North-Star sample, is 720: "
                         "400-719 is the OPEN-110 fixer window, see OPEN-118)")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--record", action="store_true",
                    help="write the frame manifest and the results baseline")
    ap.add_argument("--out", default="corpora/real_roots")
    ap.add_argument("--refresh-cli", action="store_true",
                    help="recompute only the CLI verdict, carrying the recorded "
                         "pdflatex results forward (asserts corpus + engine "
                         "unchanged)")
    ap.add_argument("--repass", action="store_true",
                    help="re-grade recorded rows under the multi-pass oracle "
                         "(asserts corpus + engine unchanged); see --repass-scope")
    ap.add_argument("--repass-scope", default="failures",
                    choices=["failures", "unmeasured", "all"],
                    help="which rows --repass re-grades. 'failures' (default, "
                         "legacy) cannot discover a false-READY because it never "
                         "revisits a recorded success. 'unmeasured' re-grades "
                         "every row lacking a pdflatex_passes count, which is "
                         "what takes the published APPLIED-TO clause to n/n "
                         "(OPEN-103).")
    ap.add_argument("--results", default="results.json",
                    help="the results artefact under --out that --repass "
                         "re-grades (results_sample2.json for sample 2)")
    ap.add_argument("--sample-offset", type=int, default=None,
                    help="with --repass on an artefact that has no hash "
                         "manifest (sample 2): its first frame rank (200)")
    ap.add_argument("--rebaseline-oracle", action="store_true",
                    help="the one-time ORACLE-BASELINE CHANGE (ADR-012 "
                         "decision 7): re-grade every row of an artefact graded "
                         "by a host TeX Live under the pinned image; requires "
                         "--repass --repass-scope all")
    ap.add_argument("--diff-out", default=None,
                    help="with --repass: write the per-row before/after diff here")
    ap.add_argument("--jobs", type=int, default=1,
                    help="parallel pdflatex gradings for --repass")
    ap.add_argument("--refresh-metadata", action="store_true",
                    help="re-read declared metadata into manifest.json; runs "
                         "neither pdflatex nor the CLI (asserts corpus "
                         "unchanged)")
    ns = ap.parse_args()

    repo = Path(ns.repo).resolve()
    outdir = repo / ns.out
    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    # --refresh-metadata reads 00README.json and writes the manifest; it runs
    # neither the CLI nor pdflatex, so it must not require either to be present.
    if not cli.is_file() and not ns.refresh_metadata:
        return die(2, f"{cli} not built")
    if not ns.corpus_root:
        return die(2, "no --corpus-root and LP_REAL_CORPUS unset. The corpus is "
                      "not in this repo and is not redistributable; see "
                      "corpora/real_roots/README.md")
    root = Path(ns.corpus_root).expanduser().resolve()
    if not root.is_dir():
        return die(2, f"corpus root {root} does not exist")

    if ns.refresh_metadata:
        return refresh_metadata_only(root, outdir)

    # The ONE oracle (ADR-012 decision 7): the pinned image, never a host
    # pdflatex. Unavailable is an infrastructure failure, not a skip.
    try:
        banner = get_oracle().banner
    except OracleError as e:
        return die(2, f"the pinned-image oracle is unavailable: {e}")
    if PIN not in banner:
        return die(3, f"engine skew: the oracle reports {banner!r}, pinned is {PIN!r}")

    if ns.repass:
        return repass_failures(repo, root, outdir, banner, ns.timeout,
                               scope=ns.repass_scope, results_name=ns.results,
                               sample_offset=ns.sample_offset,
                               rebaseline=ns.rebaseline_oracle,
                               diff_out=ns.diff_out, jobs=ns.jobs)
    if ns.rebaseline_oracle:
        return die(2, "--rebaseline-oracle needs --repass --repass-scope all")

    if ns.refresh_cli:
        return refresh_cli_only(repo, root, outdir, banner, ns.timeout,
                                results_name=ns.results)

    frame = build_frame(root)
    if len(frame) < ns.offset + ns.n:
        return die(2, f"frame has only {len(frame)} papers, need "
                      f"{ns.offset + ns.n}")
    sample = select(frame, ns.offset + ns.n)[ns.offset:]

    # A sample other than sample 1 gets its OWN results and manifest files, and
    # recording never overwrites one: a drawn sample is graded exactly once
    # (ADR-012 decision 7 -- sample 3 is the virgin North-Star sample).
    if ns.offset:
        if ns.results == "results.json":
            return die(2, "--offset needs its own --results file, e.g. "
                          "results_sample3.json; results.json is sample 1")
        manifest_path = outdir / ns.results.replace("results", "manifest", 1)
        if ns.record and ((outdir / ns.results).exists() or manifest_path.exists()):
            return die(2, f"{ns.results} or {manifest_path.name} already exists; "
                          f"a drawn sample is graded once and never re-drawn")
    else:
        manifest_path = outdir / "manifest.json"
    prior = json.loads(manifest_path.read_text()) if manifest_path.is_file() else None

    rows = []
    for i, rec in enumerate(sample, 1):
        rec["sha256_toplevel"] = sha256_file(root / rec["arxiv_id"] / rec["toplevel"])
        rec["sha256_tree"] = sha256_tree(root / rec["arxiv_id"])
        if prior:
            want = {d["arxiv_id"]: d for d in prior["docs"]}.get(rec["arxiv_id"])
            if want and want["sha256_tree"] != rec["sha256_tree"]:
                return die(2, f"{rec['arxiv_id']}: tree sha differs from the "
                              f"manifest — the corpus changed under the baseline")
        rows.append(run_one(rec, root, cli, ns.timeout))
        print(f"  [{i}/{len(sample)}] {rec['arxiv_id']:16s} {rows[-1]['cell']}",
              flush=True)

    counts = collections.Counter(r["cell"] for r in rows)
    graded = sum(v for k, v in counts.items() if not k.startswith("ungraded"))
    ungraded = len(rows) - graded

    print()
    print(f"[real-roots] oracle : {banner} ({get_oracle().backend}:{ORACLE_IMAGE})")
    print(f"[real-roots] frame  : {len(frame)} papers, sampled {len(sample)} "
          f"by sha256(arxiv_id) ascending")
    for k in ("true-READY", "true-NOT-READY", "FALSE-READY", "false-NOT-READY",
              "ungraded-infra", "ungraded-timeout"):
        print(f"[real-roots]   {k:18s} {counts.get(k, 0)}")
    if graded:
        print(f"[real-roots] over-rejection: {counts.get('false-NOT-READY', 0)}"
              f"/{graded} graded = "
              f"{100 * counts.get('false-NOT-READY', 0) / graded:.1f}%")
        print(f"[real-roots] correct verdicts: "
              f"{counts.get('true-READY', 0) + counts.get('true-NOT-READY', 0)}"
              f"/{graded} = "
              f"{100 * (counts.get('true-READY', 0) + counts.get('true-NOT-READY', 0)) / graded:.1f}%")

    fnr = collections.Counter()
    for r in rows:
        if r["cell"] == "false-NOT-READY":
            for reason in r["cli_reasons"]:
                fnr[reason] += 1
    if fnr:
        print("[real-roots] over-rejection drivers (reason -> documents):")
        for reason, k in fnr.most_common(12):
            print(f"[real-roots]   {reason:12s} {k}")

    fr = collections.Counter()
    for r in rows:
        if r["cell"] == "FALSE-READY":
            key = re.sub(r"`[^']*'", "`...'", r["first_error"])[:70]
            fr[key] += 1
    if fr:
        print("[real-roots] false-READY classes:")
        for key, k in fr.most_common():
            print(f"[real-roots]   x{k}  {key}")

    for r in rows:
        if r["cell"] == "FALSE-READY":
            print(f"[real-roots] FALSE-READY {r['arxiv_id']}: {r['first_error']}")

    # Record the corpus by its LAST TWO path components, not the absolute path:
    # the identity that matters for reproducibility is which corpus snapshot was
    # used, and the rest is one machine's home directory.
    corpus_tag = "/".join(root.parts[-3:])
    rec_oracle = oracle_record()
    result = {"oracle": rec_oracle,
              "frame": {"corpus": corpus_tag, "frame_size": len(frame),
                        "selection": "sha256(arxiv_id) ascending", "n": len(sample),
                        "offset": ns.offset},
              "counts": dict(counts), "docs": rows}

    if ns.record:
        outdir.mkdir(parents=True, exist_ok=True)
        result["measured_at_sha"] = git_head(repo)
        result["src_tree_sha"] = engine_tree(repo)
        (outdir / ns.results).write_text(json.dumps(result, indent=1) + "\n")
        manifest_path.write_text(json.dumps(
            {"oracle": rec_oracle,
             "frame": result["frame"],
             "docs": [{k: d[k] for k in ("arxiv_id", "toplevel", "bytes",
                                         "sha256_toplevel", "sha256_tree",
                                         "declared_compiler", "declared_texlive")}
                      for d in rows]}, indent=1) + "\n")
        print(f"[real-roots] recorded {len(rows)} rows to {ns.out}/")

    # ── anti-vacuity, before any verdict ──────────────────────────────────
    if any(r["cell"] == "ungraded-timeout" for r in rows):
        return die(2, "a pdflatex or CLI TIMEOUT occurred. A timeout scores as "
                      "FAILS against a READY verdict and would MANUFACTURE a "
                      "false-READY, so the whole run is void.")
    if ungraded > len(rows) // 10:
        return die(2, f"{ungraded}/{len(rows)} ungraded (>10%) — the run is not "
                      f"measuring what it claims")
    if counts.get("true-READY", 0) == 0:
        return die(2, "zero true-READY: the CLI is rejecting everything, so a "
                      "green matrix would be meaningless")

    if counts.get("FALSE-READY", 0):
        print(f"[real-roots] FAIL: {counts['FALSE-READY']} false-READY — the "
              f"cardinal bug. Triage each BY HAND; never auto-populate an "
              f"allowlist from a bulk run.", file=sys.stderr)
        return 1
    print("[real-roots] PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
