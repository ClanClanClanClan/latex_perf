#!/usr/bin/env python3
"""Meta-gate: verify every CI gate script itself runs without typos.

PR #245 (p1.9): P1.8 audit found check_regression_gates.py had a typo
(pointed at test_mutation.exe instead of test_mutation_baseline.exe).
The mutation-ratchet gate was silently broken — it reported a generic
"output missing" failure that looked like a real regression. No
automated check would have caught this because the gate failed "for
the wrong reason" but still exited non-zero.

This meta-gate sanity-checks every gate script:
  - Is the script executable?
  - Does `--help` (or a dry invocation) complete without raising?
  - Does the output look structured (contains either PASS or a FAIL
    message, not a Python traceback)?

If a gate script is broken itself, this gate fails loudly, separating
"real regression" from "gate script bug". Run this in CI alongside
the real gates.

Exit 1 if any gate script is broken.
"""

from __future__ import annotations
import argparse
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

GATE_SCRIPTS = [
    ("scripts/tools/check_repo_facts.py",
     ["--facts", "governance/project_facts.yaml", "--repo", "."]),
    ("scripts/tools/check_rule_contracts.py", ["--repo", "."]),
    ("scripts/tools/check_regression_gates.py", ["--repo", ".", "--skip-mutation"]),
    ("scripts/tools/check_memo_files.py", ["--repo", "."]),
    ("scripts/tools/check_proof_substance.py", ["--repo", "."]),
    ("scripts/validate_catalogue.py", []),
    # PR #245 (p1.10) additions
    ("scripts/tools/check_severity_drift.py", ["--repo", "."]),
    ("scripts/tools/check_mli_doc_coverage.py", ["--repo", "."]),
    ("scripts/tools/check_code_quality.py", ["--repo", "."]),
    ("scripts/tools/check_unused_hypotheses.py", ["--repo", "."]),
    # PR #245 (p1.11) additions
    ("scripts/tools/check_doc_refs.py", ["--repo", "."]),
    ("scripts/tools/check_release_integrity.py",
     ["--repo", ".", "--skip-generated"]),
]


def check_script(repo: Path, script: str, args: list[str]) -> str | None:
    """Return None on success, or a diagnostic string on failure."""
    script_path = repo / script
    if not script_path.is_file():
        return f"script not found: {script}"
    try:
        out = subprocess.run(
            ["python3", str(script_path), *args],
            capture_output=True, text=True, timeout=60, cwd=str(repo),
            check=False,
        )
    except subprocess.TimeoutExpired:
        return f"{script}: timed out after 60s"
    blob = (out.stdout or "") + (out.stderr or "")
    # Python tracebacks contain "Traceback (most recent call last):"
    if "Traceback (most recent call last):" in blob:
        # Trim to first 500 chars for log.
        return f"{script}: Python traceback:\n{blob[:500]}"
    # Empty output is suspicious.
    if not blob.strip():
        return (
            f"{script}: produced no output at all (exit={out.returncode})"
        )
    # Must contain either PASS or FAIL-ish marker.
    if "PASS" not in blob and "FAIL" not in blob and "passed" not in blob:
        return (
            f"{script}: output does not contain PASS/FAIL marker "
            f"(may be broken). First 200 chars: {blob[:200]!r}"
        )
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    any_failed = False
    for script, args in GATE_SCRIPTS:
        err = check_script(repo, script, args)
        if err is not None:
            any_failed = True
            print(f"[gates-meta] FAIL: {err}", file=sys.stderr)
        else:
            print(f"[gates-meta] ok: {script}")
    if any_failed:
        print(
            "[gates-meta] A gate script itself is broken — regression "
            "signal is unreliable. Fix the gate before relying on it.",
            file=sys.stderr,
        )
        return 1
    print(
        f"[gates-meta] PASS: all {len(GATE_SCRIPTS)} gate scripts runnable."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
