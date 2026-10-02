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
    # PR #245 (p1.9): P1.8 audit found docs/PROOFS.md and docs/PROOF_GUIDE.md
    # theorem totals drifted from governance (1,157 vs 1,181). Gate them now.
    ("docs/PROOFS.md", ["proofs.theorem_count_reported"]),
    ("docs/PROOF_GUIDE.md", ["proofs.theorem_count_reported"]),
    # 2026-09-30 honesty sweep: a doc that quotes the theorem total must quote
    # the split beside it — how many are the generated shared-body theorems
    # (`qed_text_sound`) and how many are anything else.
    ("README.md", ["proofs.theorem_count_reported",
                   "proofs.theorem_count_generated_shared_body",
                   "proofs.theorem_count_other", "proofs.proof_files_total"]),
    ("docs/PROOFS.md", ["proofs.theorem_count_generated_shared_body",
                        "proofs.theorem_count_other", "proofs.proof_files_total"]),
    ("docs/PROOF_GUIDE.md", ["proofs.theorem_count_generated_shared_body",
                             "proofs.theorem_count_other"]),
    ("docs/index.md", ["proofs.theorem_count_reported",
                       "proofs.theorem_count_generated_shared_body",
                       "proofs.theorem_count_other", "proofs.proof_files_total"]),
]

# The positive CHECKS above only ask that the right number appear SOMEWHERE in
# a file, so a stale "1,599 theorems" three lines below the right one passed
# (README carried 180 files / 1,599 theorems in three places while the tree had
# 192 / 1,591). In these files EVERY "<N> theorems" and "<N> Coq|proof files"
# must be a current fact.
STRICT_MENTION_FILES = ["README.md", "docs/index.md", "docs/PROOFS.md",
                        "docs/PROOF_GUIDE.md", "docs/ARCH.md"]
_THM_MENTION = r"(\d[\d,]*)\s+(?:theorems|theorems/lemmas)\b"
_FILE_MENTION = r"(\d[\d,]*)\s+(?:Coq|proof|\.v)\s+files\b"


def stale_mentions(relpath: str, text: str, facts: dict) -> list[str]:
    import re
    pr = facts["proofs"]
    ok_thm = {pr["theorem_count_reported"], pr["theorem_count_generated_shared_body"],
              pr["theorem_count_other"], pr["theorem_count_over_false_predicates"]}
    ok_files = {pr["proof_files_total"]} | set(pr["proof_files_by_dir"].values())
    out = []
    for lineno, line in enumerate(text.splitlines(), 1):
        for m in re.finditer(_THM_MENTION, line):
            n = int(m.group(1).replace(",", ""))
            if n >= 100 and n not in ok_thm:  # <100: a per-file/per-section count
                out.append(f"{relpath}:{lineno}: '{m.group(0)}' is not a current "
                           f"theorem fact {sorted(ok_thm)}")
        for m in re.finditer(_FILE_MENTION, line):
            n = int(m.group(1).replace(",", ""))
            if n not in ok_files:
                out.append(f"{relpath}:{lineno}: '{m.group(0)}' is not a current "
                           f"proof-file fact {sorted(ok_files)}")
    return out

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
    if key == 'proofs.theorem_count_reported':
        # Match either the bare number or "1,181" comma-grouped form.
        n = facts['proofs']['theorem_count_reported']
        comma = f"{n:,}"
        return [str(n), comma, f"{comma} theorems", f"{n} theorems",
                f"{comma} theorems/lemmas"]
    if key in ('proofs.theorem_count_generated_shared_body',
               'proofs.theorem_count_other', 'proofs.proof_files_total'):
        n = get_nested(facts, key)
        return [str(n), f"{n:,}"]
    if key == 'support_matrix_yaml_path':
        # Literal path reference to the machine-readable source.
        return ['docs/SUPPORT_MATRIX.yaml']
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
    for relpath in STRICT_MENTION_FILES:
        p = repo / relpath
        if p.exists():
            failures.extend(stale_mentions(
                relpath, p.read_text(encoding='utf-8', errors='replace'), facts))
    if failures:
        print('PROJECT FACTS DRIFT DETECTED', file=sys.stderr)
        for f in failures:
            print(f' - {f}', file=sys.stderr)
        return 1
    print('Project facts check passed.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
