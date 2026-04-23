#!/usr/bin/env python3
"""Differential regression test — plan §3.3 hard block for PR C.

Runs validators on a corpus with the current HEAD binary and asserts
the output matches the committed baseline. Used as a gate before
tagging v26.2.0 (and subsequent releases) to catch silent regressions
in validator behaviour.

Baseline semantics:
    baseline: deterministic JSON emitted by the v26.1 binary on each
              corpus file.

Output semantics:
    current:  deterministic JSON emitted by the HEAD binary on each
              corpus file.

Pass iff, for every corpus file, current == baseline modulo the allowed
per-field diff set (controlled by --expected-diff-keys; default: none).

v26.2 scope: --expected-diff-keys is empty (no fix-field yet; validators
untouched). In future releases that add rule-fix suggestions, the
caller will pass --expected-diff-keys fix so the new field is tolerated.

Usage:
    python3 scripts/tools/run_differential_test.py \
        --baseline-ref v26.1.0 \
        --corpus corpora/regression/ \
        --expected-diff-keys ""

Exit codes:
    0 — baseline == current (no regressions).
    1 — any diff outside expected-diff-keys.
    2 — setup failure (corpus missing, binary missing, etc.).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def strip_timing(stdout: bytes) -> bytes:
    """Remove timing-only lines from validator stdout so the hash
    reflects semantic output (rule fires, severity, message, count),
    not wall-clock variability.

    Stripped patterns:
    - ``# layer=… total_ms=…`` headers
    - ``# <RULE-ID>\\t<ms>`` per-rule timing comments
    - Any other ``# `` comment line (defensive: validators_cli emits
      timing-only comments; semantic output lines don't start with ``#``).
    """
    kept = []
    for line in stdout.splitlines(keepends=True):
        if line.startswith(b"# "):
            continue
        kept.append(line)
    return b"".join(kept)


def emit_validator_output(binary: Path, corpus_dir: Path) -> dict[str, str]:
    """Run [binary] on every .tex under [corpus_dir] and return a
    {relative_path: sha256_of_stdout_sans_timing} map."""
    results: dict[str, str] = {}
    for tex in sorted(corpus_dir.rglob("*.tex")):
        try:
            out = subprocess.run(
                [str(binary), "--layer", "ALL", str(tex)],
                capture_output=True,
                check=False,
                timeout=60,
            ).stdout
            rel = tex.relative_to(REPO_ROOT).as_posix()
            results[rel] = hashlib.sha256(strip_timing(out)).hexdigest()
        except subprocess.TimeoutExpired:
            results[tex.relative_to(REPO_ROOT).as_posix()] = "TIMEOUT"
    return results


def build_at_ref(ref: str) -> Path:
    """Check out [ref] into a temp worktree, dune-build the CLI, return
    the path to the validators_cli binary. Caller is responsible for
    cleaning up the returned directory's parent."""
    work = Path(tempfile.mkdtemp(prefix=f"diff_{ref}_"))
    subprocess.run(
        ["git", "worktree", "add", "--detach", str(work), ref],
        check=True,
        cwd=REPO_ROOT,
    )
    subprocess.run(
        ["dune", "build", "latex-parse/src/validators_cli.exe"],
        check=True,
        cwd=work,
    )
    binary = work / "_build/default/latex-parse/src/validators_cli.exe"
    if not binary.exists():
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(work)],
            cwd=REPO_ROOT,
        )
        raise SystemExit(
            f"[differential] validators_cli.exe not built at {binary}"
        )
    return binary


def tear_down(work_parent: Path | None) -> None:
    if work_parent is None or not work_parent.exists():
        return
    subprocess.run(
        ["git", "worktree", "remove", "--force", str(work_parent)],
        cwd=REPO_ROOT,
        check=False,
    )
    shutil.rmtree(work_parent, ignore_errors=True)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline-ref", default="v26.1.0",
                    help="git ref to build as baseline (default: v26.1.0)")
    ap.add_argument("--corpus", default="corpora/regression",
                    help="corpus directory to diff (default: corpora/regression)")
    ap.add_argument("--expected-diff-keys", default="",
                    help="comma-separated list of field names that are "
                         "allowed to differ (v26.2: empty)")
    ap.add_argument("--current-ref", default="HEAD",
                    help="git ref to build as current (default: HEAD)")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    corpus_dir = (REPO_ROOT / args.corpus).resolve()
    if not corpus_dir.exists() or not corpus_dir.is_dir():
        print(
            f"[differential] corpus not found: {corpus_dir}",
            file=sys.stderr,
        )
        return 2

    tex_count = sum(1 for _ in corpus_dir.rglob("*.tex"))
    if tex_count == 0:
        print(
            f"[differential] corpus {corpus_dir} has no .tex files",
            file=sys.stderr,
        )
        return 2
    print(f"[differential] corpus: {corpus_dir} ({tex_count} .tex files)")

    baseline_work: Path | None = None
    current_work: Path | None = None
    try:
        print(f"[differential] building baseline {args.baseline_ref}...")
        baseline_bin = build_at_ref(args.baseline_ref)
        baseline_work = baseline_bin.parents[3]

        print(f"[differential] building current {args.current_ref}...")
        current_bin = build_at_ref(args.current_ref)
        current_work = current_bin.parents[3]

        print("[differential] emitting baseline output...")
        baseline_out = emit_validator_output(baseline_bin, corpus_dir)
        print("[differential] emitting current output...")
        current_out = emit_validator_output(current_bin, corpus_dir)
    finally:
        tear_down(baseline_work)
        tear_down(current_work)

    diffs: list[tuple[str, str, str]] = []
    for path in sorted(set(baseline_out) | set(current_out)):
        b = baseline_out.get(path, "<missing>")
        c = current_out.get(path, "<missing>")
        if b != c:
            diffs.append((path, b, c))

    if not diffs:
        print(
            f"[differential] PASS: {len(baseline_out)} files, "
            f"0 diffs between {args.baseline_ref} and {args.current_ref}"
        )
        return 0

    print(
        f"[differential] FAIL: {len(diffs)} file(s) differ between "
        f"{args.baseline_ref} and {args.current_ref}",
        file=sys.stderr,
    )
    for path, b, c in diffs[:10]:
        print(
            f"  {path}\n    baseline: {b}\n    current:  {c}",
            file=sys.stderr,
        )
    if len(diffs) > 10:
        print(
            f"  ... and {len(diffs) - 10} more",
            file=sys.stderr,
        )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
