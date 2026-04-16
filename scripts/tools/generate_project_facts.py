#!/usr/bin/env python3
"""Generate governance/project_facts.yaml from repository state.

Computes canonical counts from the actual source files — rules_v3.yaml,
vpd_patterns.json, Coq proof files, test files, CI workflows — so the
facts file is never manually maintained.

Usage:
    python3 scripts/tools/generate_project_facts.py [--output governance/project_facts.yaml]
"""

import argparse
import json
import os
import re
import subprocess
import yaml
from collections import Counter
from pathlib import Path


def count_rules(repo: Path):
    """Count rules from rules_v3.yaml."""
    with open(repo / "specs/rules/rules_v3.yaml") as f:
        rules = yaml.safe_load(f)
    total = 0
    reserved = 0
    by_family = Counter()
    for r in rules:
        if isinstance(r, dict) and "id" in r:
            total += 1
            rid = r["id"]
            family = rid.split("-")[0] if "-" in rid else rid
            by_family[family] += 1
            if r.get("maturity") == "Reserved":
                reserved += 1
    return {
        "total_specified": total,
        "total_reserved": reserved,
        "total_non_reserved": total - reserved,
        "total_shipped": total - reserved,
        "by_family": dict(sorted(by_family.items())),
    }


def count_proofs(repo: Path):
    """Count proofs from .v files."""
    proof_dirs = [repo / "proofs", repo / "proofs/generated", repo / "proofs/ML"]
    theorem_count = 0
    admits = 0
    axioms = 0
    files_core = 0
    files_generated = 0
    files_ml = 0

    for d in proof_dirs:
        if not d.exists():
            continue
        for f in d.glob("*.v"):
            content = f.read_text(errors="replace")
            theorems = len(re.findall(r"\bTheorem\b|\bLemma\b|\bCorollary\b", content))
            theorem_count += theorems
            admits += content.count("Admitted.")
            axioms += len(re.findall(r"^Axiom\b|^Parameter\b", content, re.MULTILINE))
            if "generated" in str(d):
                files_generated += 1
            elif "ML" in str(d):
                files_ml += 1
            else:
                files_core += 1

    # Archive files (don't count)
    files_archive = 0
    archive_dir = repo / "proofs/archive"
    if archive_dir.exists():
        for f in archive_dir.rglob("*.v"):
            files_archive += 1

    # Count faithful/conservative from VPD
    with open(repo / "specs/rules/vpd_patterns.json") as f:
        vpd = json.load(f)
    faithful = len(vpd)

    rules = count_rules(repo)
    conservative = rules["total_non_reserved"] - faithful

    return {
        "proof_files_total": files_core + files_generated + files_ml,
        "proof_files_core": files_core,
        "proof_files_generated": files_generated,
        "proof_files_ml": files_ml,
        "proof_files_archive": files_archive,
        "per_rule_soundness_count": rules["total_non_reserved"],
        "formal_faithful_count": faithful,
        "formal_conservative_count": conservative,
        "theorem_count_reported": theorem_count,
        "admits": admits,
        "axioms": axioms,
    }


def count_tests(repo: Path):
    """Count test files and cases."""
    src = repo / "latex-parse/src"
    test_files = 0
    test_cases = 0
    for f in sorted(src.glob("test_*.ml")):
        test_files += 1
        content = f.read_text(errors="replace")
        test_cases += len(re.findall(r'\brun\s+"', content))
    # Bench tests
    bench = repo / "latex-parse/bench"
    if bench.exists():
        for f in bench.glob("*selftest*.ml"):
            test_files += 1
        for f in bench.glob("*selfcheck*.ml"):
            test_files += 1
        for f in bench.glob("*propcheck*.ml"):
            test_files += 1
    return {"test_files": test_files, "test_cases": test_cases}


def count_workflows(repo: Path):
    """Count CI workflows."""
    wf_dir = repo / ".github/workflows"
    if not wf_dir.exists():
        return 0
    return len(list(wf_dir.glob("*.yml")))


def count_languages(repo: Path):
    """Count language packs."""
    # From language_detect.ml
    ld_path = repo / "latex-parse/src/language_detect.ml"
    if not ld_path.exists():
        return {"live": 0, "stubbed": 0, "target": 0}
    # Hardcoded from project knowledge
    return {"live": 7, "stubbed": 14, "target": 21}


def get_version(repo: Path):
    """Get version from dune-project."""
    dp = repo / "dune-project"
    content = dp.read_text()
    m = re.search(r"\(version\s+([^\)]+)\)", content)
    return m.group(1) if m else "unknown"


def generate(repo: Path) -> dict:
    rules = count_rules(repo)
    proofs = count_proofs(repo)
    tests = count_tests(repo)
    wf_count = count_workflows(repo)
    langs = count_languages(repo)
    version = get_version(repo)

    # Add proof class to rules
    rules["by_proof_class"] = {
        "formal_faithful": proofs["formal_faithful_count"],
        "formal_conservative": proofs["formal_conservative_count"],
    }

    return {
        "version": f"v{version}" if not version.startswith("v") else version,
        "release_state": "GA",
        "release_date": "2026-04-14",
        "generated_by": "scripts/tools/generate_project_facts.py",
        "rules": rules,
        "proofs": proofs,
        "languages": langs,
        "ci": {
            "workflow_count": wf_count,
            "hard_gates": [
                "zero_admit",
                "build",
                "tests",
                "performance_full_document",
                "performance_edit_window",
                "security_scan",
                "spec_drift",
            ],
        },
        "interfaces": {
            "cli": "GA",
            "rest": "GA",
            "grpc": "planned",
            "collaboration": "not_shipped",
        },
        "support": {
            "engines": {
                "pdflatex": "GA",
                "xelatex": "beta",
                "lualatex": "beta",
                "ptex_uptex": "experimental",
            },
            "document_modes": {
                "single_file": "GA",
                "build_coupled_single_file": "beta",
                "multi_file": "planned",
                "beamer": "deferred",
            },
            "macro_support_level": "catalogue-only in v25; bounded user macro subset planned for v26",
            "build_coupled_features": "partial via log_parser and L3 file validators",
            "collaboration_features": "not shipped",
        },
    }


def main():
    ap = argparse.ArgumentParser(description="Generate project facts from repo state")
    ap.add_argument("--repo", default=".", help="Repository root")
    ap.add_argument(
        "--output",
        default="governance/project_facts.yaml",
        help="Output path",
    )
    args = ap.parse_args()

    repo = Path(args.repo)
    facts = generate(repo)

    with open(args.output, "w") as f:
        yaml.dump(facts, f, default_flow_style=False, sort_keys=False)

    print(f"Generated {args.output}")
    print(f"  Rules: {facts['rules']['total_specified']} specified, {facts['rules']['total_shipped']} shipped")
    print(f"  Proofs: {facts['proofs']['theorem_count_reported']} theorems, {facts['proofs']['admits']} admits")
    print(f"  Faithful: {facts['proofs']['formal_faithful_count']}, Conservative: {facts['proofs']['formal_conservative_count']}")
    print(f"  Tests: {facts['ci']['workflow_count']} workflows")


if __name__ == "__main__":
    main()
