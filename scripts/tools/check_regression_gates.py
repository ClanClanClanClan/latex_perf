#!/usr/bin/env python3
"""PR #241 (p1.6) regression gates.

Three gates that prevent previously-closed issues from reopening:

  1. _CoqProject lists every non-archive proof file.
     Rationale: P1.5 found 7 v26 proofs missing from _CoqProject — editor
     LSP silently lost them. This gate catches future additions.

  2. Rule IDs in rule_contracts.yaml follow FAMILY-NNN (uppercase, hyphen).
     Rationale: P1.4 caught five lowercase "internal utility" IDs
     (no_tabs, unmatched_braces, ...) that bypassed the contract check
     via an ad-hoc filter. The filter is gone; this gate ensures it
     doesn't need to come back.

  3. Mutation-uncovered rule count doesn't ratchet up.
     Rationale: test_mutation.ml reports which rules have no mutation
     fixture. As rules are added without mutation cases, this number
     drifts up. Locking a ceiling ratchets coverage.

Exit non-zero on any regression. Summary at end.
"""

from __future__ import annotations
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MUTATION_UNCOVERED_CEILING = 35  # P1.4 baseline; includes 5 STRUCT + 30 others


def gate_coqproject_completeness(repo: Path) -> list[str]:
    """Every non-archive proofs/*.v must appear in _CoqProject."""
    failures: list[str] = []
    coq_project = repo / "_CoqProject"
    if not coq_project.is_file():
        return [f"missing file: {coq_project}"]
    listed = set()
    for line in coq_project.read_text().splitlines():
        line = line.strip()
        if line.startswith("proofs/") and line.endswith(".v"):
            listed.add(line)
    actual = set()
    proofs_dir = repo / "proofs"
    for v in proofs_dir.glob("*.v"):
        if "archive" in v.parts:
            continue
        rel = f"proofs/{v.name}"
        actual.add(rel)
    missing = actual - listed
    if missing:
        for m in sorted(missing):
            failures.append(
                f"_CoqProject missing entry: {m} "
                f"(add to list under 'Active proof set' so editor LSP finds it)"
            )
    return failures


def gate_rule_id_format(repo: Path) -> list[str]:
    """Every rule_id in rule_contracts.yaml matches FAMILY-NNN."""
    import yaml

    failures: list[str] = []
    path = repo / "specs/rules/rule_contracts.yaml"
    if not path.is_file():
        return [f"missing file: {path}"]
    contracts = yaml.safe_load(path.read_text())["rules"]
    pattern = re.compile(r"^[A-Z][A-Z0-9]{1,7}-[0-9]{1,4}$")
    bad = [c["rule_id"] for c in contracts if not pattern.match(c["rule_id"])]
    if bad:
        for rid in bad[:10]:
            failures.append(
                f"rule_id {rid!r} does not match FAMILY-NNN "
                f"(memo §10: every rule id must be uppercase-family hyphen number)"
            )
        if len(bad) > 10:
            failures.append(
                f"... and {len(bad) - 10} more ID(s) with invalid format"
            )
    return failures


def gate_mutation_coverage_ratchet(repo: Path) -> list[str]:
    """test_mutation.ml reports `uncovered rules (N)`; lock N <= ceiling."""
    failures: list[str] = []
    try:
        out = subprocess.run(
            ["dune", "exec", "--no-build",
             "latex-parse/src/test_mutation.exe"],
            capture_output=True, text=True, timeout=60, cwd=str(repo),
            check=False,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        return [f"could not run test_mutation: {e}"]
    blob = (out.stdout or "") + (out.stderr or "")
    m = re.search(r"uncovered rules \((\d+)\)", blob)
    if not m:
        return [f"test_mutation output missing 'uncovered rules (N)' line"]
    n = int(m.group(1))
    if n > MUTATION_UNCOVERED_CEILING:
        failures.append(
            f"mutation-uncovered count {n} exceeds ceiling "
            f"{MUTATION_UNCOVERED_CEILING}. Add mutation fixtures for new "
            f"rules, or bump the ceiling in this script with justification."
        )
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ap.add_argument(
        "--skip-mutation",
        action="store_true",
        help="Skip mutation coverage gate (takes ~60s)",
    )
    ns = ap.parse_args()
    repo = Path(ns.repo)

    all_failures: list[tuple[str, list[str]]] = []
    all_failures.append(
        ("_CoqProject completeness", gate_coqproject_completeness(repo))
    )
    all_failures.append(("Rule ID format", gate_rule_id_format(repo)))
    if not ns.skip_mutation:
        all_failures.append(
            ("Mutation coverage ratchet", gate_mutation_coverage_ratchet(repo))
        )

    any_failed = False
    for name, failures in all_failures:
        if failures:
            any_failed = True
            for f in failures:
                print(f"[regression-gates] {name}: FAIL: {f}",
                      file=sys.stderr)
        else:
            print(f"[regression-gates] {name}: PASS")

    if any_failed:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
