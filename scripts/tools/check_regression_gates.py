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
MUTATION_UNCOVERED_CEILING = 30  # P1.7 baseline after STRUCT-001..005 fixtures


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


def gate_runtime_ids_catalogued(repo: Path) -> list[str]:
    """Every `id = "..."` and `mk_rule "..."` literal in validator
    sources must appear as a rule_id in rule_contracts.yaml. Catches
    future uncatalogued rules before they drift into production."""
    import yaml

    failures: list[str] = []
    # Collect all ID literals
    src = repo / "latex-parse/src"
    patterns = [
        re.compile(r'id\s*=\s*"([A-Za-z_][A-Za-z_0-9-]*)"'),
        re.compile(r'mk_rule\s+"([A-Za-z_][A-Za-z_0-9-]*)"'),
        re.compile(r'mk_lang_rule\s+"([A-Za-z_][A-Za-z_0-9-]*)"'),
    ]
    runtime_ids: set[str] = set()
    for p in src.glob("validators*.ml"):
        if "conflicted" in p.name:
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        for pat in patterns:
            for m in pat.finditer(text):
                runtime_ids.add(m.group(1))
    # Filter to plausible rule IDs: must contain hyphen to be a catalogued
    # ID, OR match a known-internal-lowercase-pattern that should be
    # renamed (caught by the lowercase gate below).
    plausible = {r for r in runtime_ids if "-" in r}
    # Contract ids
    contracts_path = repo / "specs/rules/rule_contracts.yaml"
    if not contracts_path.is_file():
        return [f"missing: {contracts_path}"]
    contracts = yaml.safe_load(contracts_path.read_text())["rules"]
    contract_ids = {c["rule_id"] for c in contracts}
    orphans = sorted(plausible - contract_ids)
    if orphans:
        for rid in orphans[:10]:
            failures.append(
                f"rule id {rid!r} emitted at runtime but not in "
                f"specs/rules/rule_contracts.yaml. Add to rules_v3.yaml "
                f"+ regenerate, or remove the runtime emission."
            )
        if len(orphans) > 10:
            failures.append(f"... and {len(orphans) - 10} more")
    return failures


def gate_no_lowercase_runtime_ids(repo: Path) -> list[str]:
    """Prevent reintroduction of lowercase `id = "foo_bar"` in validator
    sources. Catches the pattern early, before rule-contracts drift."""
    failures: list[str] = []
    src = repo / "latex-parse/src"
    # FAMILY-NNN is uppercase-letters hyphen digits.
    good = re.compile(r'^[A-Z][A-Z0-9]{1,7}-[0-9]{1,4}$')
    bad_pattern = re.compile(
        r'(?:^|\s)(?:id\s*=|mk_rule|mk_lang_rule)\s+"([a-z_][A-Za-z_0-9]*)"'
    )
    for p in sorted(src.glob("validators*.ml")):
        if "conflicted" in p.name:
            continue
        for i, line in enumerate(
            p.read_text(encoding="utf-8", errors="replace").splitlines(), 1
        ):
            m = bad_pattern.search(line)
            if m:
                rid = m.group(1)
                # Allow some known-safe lowercase helpers (event bus keys)
                # — but a validator ID never.
                if good.match(rid):
                    continue
                failures.append(
                    f"{p.name}:{i}: lowercase rule id {rid!r}. Use "
                    f"FAMILY-NNN convention. See STRUCT-001..005 in "
                    f"P1.4 for the canonical rename pattern."
                )
    return failures


def gate_mutation_coverage_ratchet(repo: Path) -> list[str]:
    """test_mutation.ml reports `uncovered rules (N)`; lock N <= ceiling."""
    failures: list[str] = []
    try:
        out = subprocess.run(
            ["dune", "exec", "--no-build",
             "latex-parse/src/test_mutation_baseline.exe"],
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
    all_failures.append(
        ("Runtime IDs catalogued", gate_runtime_ids_catalogued(repo))
    )
    all_failures.append(
        ("No lowercase runtime IDs", gate_no_lowercase_runtime_ids(repo))
    )
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
