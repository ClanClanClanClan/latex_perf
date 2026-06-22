#!/usr/bin/env python3
"""Pre-release uber-gate (PR #245 p1.11).

A single command that verifies EVERY gate + clean tree + fresh
regeneration. Call from release.sh before tag creation, or manually
to sanity-check the current state.

Runs (in order):
  0. git status --porcelain: working tree must be clean.
  1. Every gate script via check_gates_meta.
  2. Each gate script independently (full run, not just meta-check).
  3. Full `dune build`.
  4. `dune build proofs` with zero admits/axioms.
  5. `dune runtest latex-parse/src --force`.

Exit 0 iff everything passes. Any failure = not ready to tag.
"""

from __future__ import annotations
import argparse
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Local-only environment overlay for the build/test steps — load tolerances for
# the two wall-clock-sensitive tests that spuriously trip on a dev machine under
# load (Dropbox sync + concurrent builds), with NO change to the CI bar (CI runs
# `dune runtest` without this overlay):
#   - CST_PERF_ADVISORY: downgrades test_cst_perf's hard 900 ms ratchet (CI ~646 ms)
#     to an advisory note. See latex-parse/src/test_cst_perf.ml.
#   - STRESS_WATCHDOG_SCALE: multiplies test_validators_stress's infinite-loop
#     watchdog budget (5 s/10 s) so CPU starvation does not fire a false "possible
#     Str corruption"; a genuine hang still blows past the scaled bound and fails.
#     See latex-parse/src/test_validators_stress.ml.
#   - L2_GATE_ADVISORY: downgrades test_l2_gate's hard 4KB p95 < 5 ms latency bar
#     (sub-ms on CI) to an advisory note. See latex-parse/src/test_l2_gate.ml.
# These are the suite's only hard wall-clock gates (test_throughput prints but
# never fails; parser-corpus is a correctness-rate test, not timing-sensitive).
LOCAL_TEST_ENV = {
    "CST_PERF_ADVISORY": "1",
    "STRESS_WATCHDOG_SCALE": "12",
    "L2_GATE_ADVISORY": "1",
}

GATES = [
    ("python3", "scripts/tools/check_repo_facts.py",
     "--facts", "governance/project_facts.yaml", "--repo", "."),
    ("python3", "scripts/tools/check_rule_contracts.py", "--repo", "."),
    ("python3", "scripts/tools/check_regression_gates.py", "--repo", "."),
    ("python3", "scripts/tools/check_memo_files.py", "--repo", "."),
    ("python3", "scripts/tools/check_proof_substance.py", "--repo", "."),
    ("python3", "scripts/validate_catalogue.py"),
    ("python3", "scripts/tools/check_severity_drift.py", "--repo", "."),
    ("python3", "scripts/tools/check_mli_doc_coverage.py", "--repo", "."),
    ("python3", "scripts/tools/check_code_quality.py", "--repo", "."),
    ("python3", "scripts/tools/check_unused_hypotheses.py", "--repo", "."),
    ("python3", "scripts/tools/check_doc_refs.py", "--repo", "."),
    ("python3", "scripts/tools/check_version_labels.py", "--repo", "."),
    ("python3", "scripts/tools/check_release_integrity.py", "--repo", "."),
    ("python3", "scripts/tools/check_gates_meta.py", "--repo", "."),
    ("python3", "scripts/tools/check_perf_ratchet.py", "--repo", "."),
    ("python3", "scripts/tools/check_result_helpers.py"),
    ("python3", "scripts/tools/check_fix_integration_wired.py"),
    ("python3", "scripts/tools/check_cst_structure_lossless.py"),
    ("python3", "scripts/tools/check_fix_producer_ledger.py"),
]

# Each entry: (cmd, label, env_overlay). env_overlay is applied on top of
# os.environ for that step only (None = inherit unchanged).
BUILD_CHECKS = [
    (["dune", "build"], "full build", None),
    (["dune", "build", "proofs"], "proofs build", None),
    # Unit tests carry the local cst-perf advisory overlay (see LOCAL_TEST_ENV):
    # the perf ratchet is CI-calibrated and flaps on a loaded dev box; CI keeps
    # the strict bar, this only de-flakes the local uber-gate.
    (["dune", "runtest", "latex-parse/src", "--force"], "unit tests", LOCAL_TEST_ENV),
    # Runs after the build so validators_cli.exe exists. Corpus-wide --apply-fixes
    # safety: every file must converge to valid output (no producer oscillation /
    # corruption). The lint-only differential cannot see fix output.
    (["python3", "scripts/tools/check_apply_fixes_safety.py", "--repo", "."],
     "apply-fixes safety", None),
]


def run_step(cmd: list[str], label: str, cwd: Path, env_overlay: dict | None = None) -> bool:
    print(f"[pre-release] running: {label} ...")
    env = None
    if env_overlay:
        env = dict(os.environ, **env_overlay)
    try:
        out = subprocess.run(
            cmd, capture_output=True, text=True, timeout=900,
            check=False, cwd=str(cwd), env=env,
        )
    except FileNotFoundError as e:
        print(f"[pre-release] FAIL: {label}: command not found: {e}",
              file=sys.stderr)
        return False
    except subprocess.TimeoutExpired:
        print(f"[pre-release] FAIL: {label}: timed out after 15 min",
              file=sys.stderr)
        return False
    if out.returncode != 0:
        print(f"[pre-release] FAIL: {label} (exit {out.returncode})",
              file=sys.stderr)
        if out.stdout:
            print(out.stdout[-1500:], file=sys.stderr)
        if out.stderr:
            print(out.stderr[-1500:], file=sys.stderr)
        return False
    print(f"[pre-release] ok:      {label}")
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ap.add_argument(
        "--allow-dirty",
        action="store_true",
        help="Skip the git-status clean check (for local smoke testing).",
    )
    ap.add_argument(
        "--skip-build",
        action="store_true",
        help="Skip dune build / runtest steps (gate-only mode).",
    )
    ns = ap.parse_args()
    repo = Path(ns.repo)

    # Step 0: clean tree
    if not ns.allow_dirty:
        out = subprocess.run(
            ["git", "status", "--porcelain"],
            capture_output=True, text=True, cwd=str(repo), check=False,
        )
        dirty = [
            l for l in (out.stdout or "").splitlines()
            if not l.startswith("?? ")
        ]
        if dirty:
            print(
                "[pre-release] FAIL: working tree has uncommitted changes:",
                file=sys.stderr,
            )
            for l in dirty[:10]:
                print(f"  {l}", file=sys.stderr)
            return 1
        print("[pre-release] ok:      clean tree")

    ok = True
    for gate in GATES:
        if not run_step(list(gate), gate[1], repo):
            ok = False
    if not ns.skip_build:
        for cmd, label, env_overlay in BUILD_CHECKS:
            if not run_step(cmd, label, repo, env_overlay):
                ok = False

    if not ok:
        print("[pre-release] NOT READY: fix failures above before tag push.",
              file=sys.stderr)
        return 1
    print("[pre-release] ALL CHECKS PASSED — safe to tag.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
