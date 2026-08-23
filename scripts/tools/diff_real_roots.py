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
  3  engine skew (local pdflatex != the pinned oracle)
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
import tempfile
from pathlib import Path

PIN = "pdfTeX 3.141592653-2.6-1.40.29"
ORACLE = {
    "engine": "pdflatex",
    "distribution": "TeX Live 2026",
    "version": PIN,
    "protocol": "-interaction=nonstopmode -halt-on-error -no-shell-escape",
}

# A missing converted-EPS or graphics file is a property of how the paper was
# BUILT (arXiv ran epstopdf via shell-escape), not of the document's validity.
# Scoring it FAILS would invent false-READYs out of infrastructure.
INFRA = re.compile(
    r"-eps-converted-to\.pdf' not found"
    r"|Package pdftex\.def Error: File .* not found"
    r"|epstopdf")


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


def run_one(rec: dict, root: Path, cli: Path, timeout: int) -> dict:
    pkg = root / rec["arxiv_id"]
    out = dict(rec)
    with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
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
            out["cli_reasons"] = sorted(set(re.findall(r"\b(T\d|[A-Z]{2,8}-\d{3})\b",
                                                       stdout)))
        except subprocess.TimeoutExpired:
            out["cli_rc"] = -1
            out["cli_verdict"] = "TIMEOUT"
            out["cli_reasons"] = []

        tex_env = dict(os.environ,
                       TEXMFHOME=str(Path(td) / "th"),
                       TEXMFVAR=str(Path(td) / "tv"),
                       openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")
        try:
            t = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", rec["toplevel"]],
                cwd=work, env=tex_env, capture_output=True, timeout=timeout)
            out["pdflatex_rc"] = t.returncode
        except subprocess.TimeoutExpired:
            out["pdflatex_rc"] = -1

        log = work / (Path(rec["toplevel"]).stem + ".log")
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
        compiles = out["pdflatex_rc"] == 0
        ready = out["cli_rc"] == 0
        out["pdflatex_verdict"] = "COMPILES" if compiles else "FAILS"
        out["cell"] = ("true-READY" if (ready and compiles) else
                       "FALSE-READY" if (ready and not compiles) else
                       "false-NOT-READY" if compiles else "true-NOT-READY")
    return out


def refresh_cli_only(repo: Path, root: Path, outdir: Path, banner: str,
                     timeout: int) -> int:
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
    """
    results_path = outdir / "results.json"
    manifest_path = outdir / "manifest.json"
    if not results_path.is_file() or not manifest_path.is_file():
        return die(2, "no recorded results to refresh — run a full sweep first")
    res = json.loads(results_path.read_text())
    man = {d["arxiv_id"]: d for d in json.loads(manifest_path.read_text())["docs"]}

    if res["oracle"]["version"] not in banner:
        return die(3, f"engine skew: recorded {res['oracle']['version']!r}, local "
                      f"{banner!r}. A CLI-only refresh cannot carry pdflatex "
                      f"verdicts across an engine change — run the full sweep.")

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
            reasons = sorted(set(re.findall(r"\b(T\d|[A-Z]{2,8}-\d{3})\b",
                                            r.stdout.decode("utf-8", "replace"))))
        except subprocess.TimeoutExpired:
            return die(2, f"{d['arxiv_id']}: CLI timeout — the run is void")
        before = d["cell"]
        d["cli_rc"], d["cli_verdict"] = rc, ("READY" if rc == 0 else "NOT-READY")
        d["cli_reasons"] = reasons
        if d["cell"].startswith("ungraded"):
            pass                                   # infra/timeout stays as recorded
        else:
            compiles = d["pdflatex_rc"] == 0
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
    manifest_path.write_text(json.dumps(man, indent=1) + "\n")
    have = sum(1 for d in man["docs"] if d["declared_texlive"] is not None)
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
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--record", action="store_true",
                    help="write the frame manifest and the results baseline")
    ap.add_argument("--out", default="corpora/real_roots")
    ap.add_argument("--refresh-cli", action="store_true",
                    help="recompute only the CLI verdict, carrying the recorded "
                         "pdflatex results forward (asserts corpus + engine "
                         "unchanged)")
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

    # Engine skew is its OWN exit code: a mismatch is not a soundness result.
    try:
        banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                                text=True).stdout.split("\n")[0]
    except FileNotFoundError:
        return die(2, "pdflatex not on PATH")
    if PIN not in banner:
        return die(3, f"engine skew: local is {banner!r}, pinned is {PIN!r}")

    if ns.refresh_cli:
        return refresh_cli_only(repo, root, outdir, banner, ns.timeout)

    frame = build_frame(root)
    if len(frame) < ns.n:
        return die(2, f"frame has only {len(frame)} papers, need {ns.n}")
    sample = select(frame, ns.n)

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
    print(f"[real-roots] oracle : {banner}")
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
    result = {"oracle": ORACLE,
              "frame": {"corpus": corpus_tag, "frame_size": len(frame),
                        "selection": "sha256(arxiv_id) ascending", "n": len(sample)},
              "counts": dict(counts), "docs": rows}

    if ns.record:
        outdir.mkdir(parents=True, exist_ok=True)
        (outdir / "results.json").write_text(json.dumps(result, indent=1) + "\n")
        (outdir / "manifest.json").write_text(json.dumps(
            {"oracle": ORACLE,
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
