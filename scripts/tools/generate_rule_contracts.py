#!/usr/bin/env python3
"""Generate specs/rules/rule_contracts.yaml from rules_v3.yaml + runtime.

Produces the machine-readable rule-contract manifest consumed at runtime
by Rule_contract_loader (OCaml). Each rule receives deterministic defaults
based on its family; the 17 Class C rules from
latex-parse/src/execution_class.ml are handled explicitly.

Per PR #237 (memo §10, §15.4):
- Every rule gets phase, execution_class, proof_class, evidence_class,
  consumes, provides, depends_on, conflicts_with, fix_scope, project_scope.
- Output replaces Validator_dag.default_meta in validators.ml.

Usage:
    python3 scripts/tools/generate_rule_contracts.py [--output specs/rules/rule_contracts.yaml]
"""

from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

# Class C rule IDs — sourced from latex-parse/src/execution_class.ml.
# Kept in sync with runtime list; drift-checked by check_rule_contracts.py.
CLASS_C_RULE_IDS = {
    "FIG-020",
    "LAY-001", "LAY-002", "LAY-003", "LAY-004",
    "LAY-006", "LAY-009", "LAY-011",
    "LAY-017", "LAY-018", "LAY-021",
    "MATH-026", "MATH-027",
    "TIKZ-002",
    "LAY-025", "LAY-026", "LAY-027",
}

# Rules with formal_conditional proofs (BuildLog.v conditional theorems).
CONDITIONAL_PROOF_RULE_IDS = {"LAY-025", "LAY-026", "LAY-027"}

# Rules with formal_conservative proofs (L3 file-based rules).
CONSERVATIVE_PROOF_RULE_IDS = {
    "FIG-004", "FIG-006", "FIG-016", "FIG-021", "FIG-023",
    "COL-001", "COL-002", "COL-003", "COL-004", "COL-005", "COL-007",
    "PDF-006", "PDF-007", "PDF-008", "PDF-009", "PDF-011", "PDF-012",
    "TIKZ-002", "TIKZ-008", "CJK-007",
}

# ML-statistically-validated ambiguous rules.
ML_STATISTICAL_RULE_IDS = {
    "TYPO-001", "TYPO-005", "TYPO-012", "TYPO-028",
    "TYPO-048", "TYPO-052", "TYPO-056", "TYPO-062",
}

# Phase A (keystroke-critical) families: fast, local, deterministic.
PHASE_A_FAMILIES = {"TYPO", "CHAR", "ENC", "SPC", "DELIM", "VERB"}

# Phase D (advisory) families: style, ML-gated, language-specific heuristics.
PHASE_D_FAMILIES = {"STYLE"}

# PR #241 (p1.1-#4): PRJ-001..004 + PRT-001/002 + CMD-015/016/017 are
# now included in rules_v3.yaml (spec catch-up). No runtime-only back
# door needed.


def rule_family(rule_id: str) -> str:
    return rule_id.split("-", 1)[0] if "-" in rule_id else rule_id


def pick_phase(rule_id: str, precondition: str | None) -> str:
    """Choose execution class. Explicit Class C first; then by family."""
    if rule_id in CLASS_C_RULE_IDS:
        return "C"
    family = rule_family(rule_id)
    if family in PHASE_D_FAMILIES:
        return "D"
    if family in PHASE_A_FAMILIES:
        return "A"
    # Default heuristic by layer: L0/L1 → B (debounce); L2/L3 → B; L4 already D.
    return "B"


def pick_proof_class(rule_id: str) -> str:
    if rule_id in CONDITIONAL_PROOF_RULE_IDS:
        return "formal_conditional"
    if rule_id in CONSERVATIVE_PROOF_RULE_IDS:
        return "formal_conservative"
    return "formal_faithful"


def pick_evidence_class(rule_id: str) -> str:
    if rule_id in ML_STATISTICAL_RULE_IDS:
        return "statistical_ml_bounded"
    if rule_id in CONDITIONAL_PROOF_RULE_IDS:
        return "compile_log_evidence"
    if rule_id in CONSERVATIVE_PROOF_RULE_IDS:
        return "external_binary_evidence"
    return "source_pattern_evidence"


def pick_project_scope(rule_id: str, phase: str) -> str:
    """LP-Core / any. Rules that require full build context are project-wide."""
    if phase == "C":
        return "any"  # Class C rules apply across tiers when build log present
    family = rule_family(rule_id)
    if family in {"REF", "LAB"}:
        return "any"  # cross-file concern
    return "lp_core_or_extended"


def pick_fix_scope(rule_id: str, severity: str | None) -> str:
    """Local vs document. Default: local for Warning/Info, document for Error."""
    if severity and severity.lower() == "error":
        return "document"
    return "local"


def load_rules_v3(repo: Path) -> list[dict]:
    path = repo / "specs/rules/rules_v3.yaml"
    with open(path, encoding="utf-8") as f:
        data = yaml.safe_load(f)
    return [r for r in data if isinstance(r, dict) and "id" in r]


def build_contract(rule: dict) -> dict:
    rid = rule["id"]
    precondition = rule.get("precondition")
    phase = pick_phase(rid, precondition)
    proof_class = pick_proof_class(rid)
    evidence_class = pick_evidence_class(rid)
    project_scope = pick_project_scope(rid, phase)
    fix_scope = pick_fix_scope(rid, rule.get("default_severity"))

    # Layer from precondition: fed to Validator_dag.phase_of_string.
    # Default to L0 if missing (shouldn't happen for any current rule).
    layer = precondition or "L0_Lexer"

    return {
        "rule_id": rid,
        "layer": layer,
        "execution_class": phase,
        "proof_class": proof_class,
        "evidence_class": evidence_class,
        "consumes": [],        # capabilities this rule reads (populated hand-audited below)
        "provides": [rid],     # self-provision (matches default_meta behaviour)
        "depends_on": [],      # rules this must run after (hand-audited below)
        "conflicts_with": [],  # competing rules (hand-audited below)
        "fix_scope": fix_scope,
        "project_scope": project_scope,
    }


def _add_conflict(by_id: dict, a: str, b: str) -> None:
    """Symmetric conflict edge. Both rules declare the other."""
    for ra, rb in ((a, b), (b, a)):
        if ra in by_id:
            c = by_id[ra]
            if rb not in c["conflicts_with"]:
                c["conflicts_with"].append(rb)


def hand_audit_overrides(contracts: list[dict]) -> None:
    """Apply hand-audited overrides for rules with non-trivial edges.

    Additions here should be minimal and well-justified. Every override must
    reference either a spec section or a known runtime dependency.
    """
    by_id = {c["rule_id"]: c for c in contracts}

    # PR #241 (p1.3): real conflict edges derived from pattern overlap.
    # Each pair below has verifiable-from-source conflict: one rule's
    # pattern is a prefix/subset of the other's so both fire on the
    # same span if enabled simultaneously.
    _add_conflict(by_id, "TYPO-002", "TYPO-003")  # `--` vs `---` (en vs em dash)
    _add_conflict(by_id, "TYPO-003", "TYPO-030")  # `---` vs `----+` (em-dash vs 4+ hyphens)
    _add_conflict(by_id, "TYPO-002", "TYPO-030")  # `--` inside `----+`
    _add_conflict(by_id, "TYPO-001", "TYPO-004")  # straight quote vs backtick-apostrophe
    _add_conflict(by_id, "TYPO-013", "TYPO-004")  # lone backtick vs backtick-pair

    # Class C rules consume compile_log_context (produced by Log_parser).
    for rid in CLASS_C_RULE_IDS:
        if rid in by_id:
            if "compile_log_context" not in by_id[rid]["consumes"]:
                by_id[rid]["consumes"].append("compile_log_context")

    # L3 file validators consume binary file metadata.
    for rid in CONSERVATIVE_PROOF_RULE_IDS:
        if rid in by_id:
            c = by_id[rid]
            if rid.startswith(("FIG-", "COL-")):
                cap = "image_metadata"
            elif rid.startswith("PDF-"):
                cap = "pdf_structure"
            elif rid.startswith("TIKZ-"):
                cap = "tikz_compile_times"
            elif rid.startswith("CJK-"):
                cap = "font_glyph_coverage"
            else:
                cap = "external_binary"
            if cap not in c["consumes"]:
                c["consumes"].append(cap)

    # ML-gated rules consume ml_confidence_map.
    for rid in ML_STATISTICAL_RULE_IDS:
        if rid in by_id:
            c = by_id[rid]
            if "ml_confidence_map" not in c["consumes"]:
                c["consumes"].append("ml_confidence_map")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--output",
        default=str(REPO_ROOT / "specs/rules/rule_contracts.yaml"),
    )
    ap.add_argument(
        "--repo",
        default=str(REPO_ROOT),
    )
    ns = ap.parse_args()

    repo = Path(ns.repo)
    rules = load_rules_v3(repo)
    contracts = [build_contract(r) for r in rules]
    hand_audit_overrides(contracts)

    # Stable ordering: by rule_id for deterministic diffs.
    contracts.sort(key=lambda c: c["rule_id"])

    output = {
        "version": "v26.1",
        "source": "scripts/tools/generate_rule_contracts.py",
        "input": "specs/rules/rules_v3.yaml",
        "total_rules": len(contracts),
        "rules": contracts,
    }

    with open(ns.output, "w", encoding="utf-8") as f:
        f.write(
            "# =====================================================================\n"
            "# rule_contracts.yaml — per-rule execution/proof/project metadata\n"
            "# Source of truth: this file. Regenerated by generate_rule_contracts.py.\n"
            "# Consumed by: latex-parse/src/rule_contract_loader.ml (via JSON mirror)\n"
            "# Memo reference: specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md §10\n"
            "# =====================================================================\n"
        )
        yaml.safe_dump(output, f, sort_keys=False, allow_unicode=True, width=120)

    # Also emit JSON mirror next to the YAML for OCaml runtime consumption.
    json_path = Path(ns.output).with_suffix(".json")
    with open(json_path, "w", encoding="utf-8") as jf:
        json.dump(output, jf, ensure_ascii=False, indent=2)
        jf.write("\n")
    print(f"[rule_contracts] wrote JSON mirror to {json_path}", file=sys.stderr)

    print(
        f"[rule_contracts] wrote {len(contracts)} contracts to {ns.output}",
        file=sys.stderr,
    )
    # Summary counts by phase/proof_class for sanity.
    phases = {}
    proofs = {}
    for c in contracts:
        phases[c["execution_class"]] = phases.get(c["execution_class"], 0) + 1
        proofs[c["proof_class"]] = proofs.get(c["proof_class"], 0) + 1
    print(f"[rule_contracts] by execution_class: {phases}", file=sys.stderr)
    print(f"[rule_contracts] by proof_class:     {proofs}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
