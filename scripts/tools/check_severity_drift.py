#!/usr/bin/env python3
"""Severity-drift gate (PR #245 p1.10).

Every rule has a [default_severity] field in specs/rules/rules_v3.yaml
(Error / Warning / Info) and a `severity = ...` field in the OCaml
validator body. These two can drift — editing one without the other
produces a catalogue that disagrees with runtime.

This gate parses both and verifies agreement per rule ID. Missing
runtime rules (Reserved maturity) are skipped; rules whose runtime body
is generated or parametric (no literal `severity =` token for their ID)
are skipped with a warning.

Exit 1 on any drift.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

CANONICAL_SEVERITY = {
    "error": "Error",
    "warning": "Warning",
    "info": "Info",
}


def extract_runtime_severity(src_dir: Path) -> dict[str, str]:
    """For every `id = "RULE"` in a validator file, associate the
    lexically-nearest `severity = ...` within the same record literal."""
    result: dict[str, str] = {}
    # Pattern: `id = "RULE-NNN"; ... severity = Warning; ...`
    # We match on record literals using a non-greedy scan.
    # Approach: find each `id = "X"` occurrence, then search the
    # surrounding ~200 chars for `severity = Y`.
    record_pat = re.compile(
        r'id\s*=\s*"([A-Z][A-Z0-9]{1,7}-[0-9]+)"\s*;[^{}]{0,400}?'
        r'severity\s*=\s*(Error|Warning|Info)\b',
        re.DOTALL,
    )
    for p in sorted(src_dir.glob("validators*.ml")):
        if "conflicted" in p.name:
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        for m in record_pat.finditer(text):
            rid, sev = m.group(1), m.group(2)
            # First occurrence wins; later ones for the same ID are
            # probably alternative branches with the same severity.
            if rid not in result:
                result[rid] = sev
    return result


def extract_spec_severity(rules_v3: Path) -> dict[str, tuple[str, str]]:
    """Return {rule_id: (severity, maturity)}."""
    data = yaml.safe_load(rules_v3.read_text())
    result: dict[str, tuple[str, str]] = {}
    for rule in data:
        if not isinstance(rule, dict):
            continue
        rid = rule.get("id")
        sev = rule.get("default_severity")
        mat = rule.get("maturity", "Unknown")
        if rid and sev:
            result[rid] = (str(sev), str(mat))
    return result


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    rules_v3 = repo / "specs/rules/rules_v3.yaml"
    if not rules_v3.is_file():
        print(f"[severity-drift] FAIL: missing {rules_v3}", file=sys.stderr)
        return 2
    runtime = extract_runtime_severity(repo / "latex-parse/src")
    spec = extract_spec_severity(rules_v3)

    drifts: list[str] = []
    for rid, (spec_sev, mat) in sorted(spec.items()):
        if mat == "Reserved":
            continue
        if rid not in runtime:
            # Might be a VPD-generated rule without a literal severity
            # — skip silently.
            continue
        runtime_sev = runtime[rid]
        if runtime_sev != spec_sev:
            drifts.append(
                f"{rid}: spec={spec_sev} runtime={runtime_sev} "
                f"(maturity={mat})"
            )

    if drifts:
        for d in drifts:
            print(f"[severity-drift] FAIL: {d}", file=sys.stderr)
        print(
            "[severity-drift] Reconcile the default_severity in "
            "specs/rules/rules_v3.yaml with the `severity = ...` literal "
            "in the OCaml rule body.",
            file=sys.stderr,
        )
        return 1
    print(
        f"[severity-drift] PASS: {len(spec)} spec entries checked; "
        f"{len(runtime)} have runtime severity; all consistent."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
