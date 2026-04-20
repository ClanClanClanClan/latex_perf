#!/usr/bin/env python3
from __future__ import annotations
import argparse
import sys
from pathlib import Path
import yaml

CHECKS = [
    ("README.md", ["version", "rules.total_specified", "rules.total_shipped", "proofs.formal_faithful_count", "proofs.formal_conservative_count"]),
    ("docs/index.md", ["rules.total_specified", "rules.total_shipped", "proofs.per_rule_soundness_count", "proofs.formal_faithful_count", "proofs.formal_conservative_count"]),
    ("CHANGELOG.md", ["version"]),
    ("specs/README.md", ["rules.total_specified", "rules.total_non_reserved", "rules.total_reserved"]),
    ("specs/rules/README.md", ["rules.total_specified", "rules.total_non_reserved", "rules.total_reserved"]),
    ("specs/rules/rules_v3.yaml", ["rules.total_specified"]),
    # PR #238 (memo §12): machine-readable support matrix must be referenced
    # from the human-readable doc, and the proof taxonomy prose must match
    # canonical counts.
    ("docs/SUPPORT_MATRIX.md", ["support_matrix_yaml_path", "proofs.formal_faithful_count", "proofs.formal_conservative_count"]),
    ("docs/PROOF_CLASSES.md", ["proofs.formal_faithful_count", "proofs.formal_conservative_count"]),
]

def load_yaml(path: Path):
    return yaml.safe_load(path.read_text(encoding='utf-8'))

def get_nested(d: dict, path: str):
    cur = d
    for part in path.split('.'):
        cur = cur[part]
    return cur

def render_candidates(key: str, facts: dict):
    if key == 'version':
        return [str(facts['version'])]
    if key == 'rules.total_specified':
        n = facts['rules']['total_specified']
        return [str(n), f"{n} rules", f"{n} spec entries"]
    if key == 'rules.total_shipped':
        n = facts['rules']['total_shipped']
        total = facts['rules']['total_specified']
        return [str(n), f"{n} / {total}", f"{n} shipped / {total}"]
    if key == 'rules.total_non_reserved':
        n = facts['rules']['total_non_reserved']
        return [str(n), f"{n} non-reserved"]
    if key == 'rules.total_reserved':
        n = facts['rules']['total_reserved']
        return [str(n), f"{n} reserved"]
    if key == 'proofs.per_rule_soundness_count':
        n = facts['proofs']['per_rule_soundness_count']
        return [str(n), f"{n} per-rule", f"{n} soundness"]
    if key == 'proofs.formal_faithful_count':
        return [str(facts['proofs']['formal_faithful_count'])]
    if key == 'proofs.formal_conservative_count':
        return [str(facts['proofs']['formal_conservative_count'])]
    if key == 'proofs.formal_conditional_count':
        n = facts['proofs'].get('formal_conditional_count', 0)
        return [str(n)]
    if key == 'support_matrix_yaml_path':
        # Literal path reference to the machine-readable source.
        return ['specs/v26/support_matrix.yaml']
    return [str(get_nested(facts, key))]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--facts', required=True)
    ap.add_argument('--repo', default='.')
    ns = ap.parse_args()
    facts = load_yaml(Path(ns.facts))
    repo = Path(ns.repo)
    failures = []
    for relpath, keys in CHECKS:
        p = repo / relpath
        if not p.exists():
            failures.append(f"Missing file: {relpath}")
            continue
        text = p.read_text(encoding='utf-8', errors='replace')
        for key in keys:
            candidates = render_candidates(key, facts)
            if not any(c in text for c in candidates):
                failures.append(f"{relpath}: expected one of {candidates} for {key}")
    if failures:
        print('PROJECT FACTS DRIFT DETECTED', file=sys.stderr)
        for f in failures:
            print(f' - {f}', file=sys.stderr)
        return 1
    print('Project facts check passed.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
