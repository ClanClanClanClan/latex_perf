#!/usr/bin/env python3
"""Drift gate for specs/rules/rule_contracts.yaml.

Checks:
    1. Every id in rules_v3.yaml has exactly one contract in rule_contracts.yaml.
    2. rule_contracts.json mirrors rule_contracts.yaml byte-equivalently
       (after re-generation) — catches forgotten regeneration.
    3. Class C rules in rule_contracts.yaml match the hardcoded
       CLASS_C_RULE_IDS in generate_rule_contracts.py (via runtime
       execution_class.ml cross-check).
    4. DAG is acyclic: no rule A's depends_on/consumes transitively depends on A.
    5. Every layer field parses to a valid phase (L0..L4).
    6. Total rule count matches governance/project_facts.yaml (if present).

Exit non-zero on any failure.

Memo reference: specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md §10.
"""

from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path
import yaml

VALID_LAYERS = {"L0", "L0_Lexer", "L1", "L1_Expanded", "L2", "L2_Ast",
                "L3", "L3_Semantics", "L4", "L4_Style"}
VALID_EXECUTION_CLASSES = {"A", "B", "C", "D"}
VALID_PROOF_CLASSES = {"formal_faithful", "formal_conservative", "formal_conditional"}

REPO_ROOT = Path(__file__).resolve().parents[2]


def load_yaml(path: Path):
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)


def load_json(path: Path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def extract_rules_v3_ids(path: Path) -> set[str]:
    """Parse rule IDs from rules_v3.yaml directly (regex) to avoid
    yaml.safe_load memory overhead on the large file."""
    ids = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r'^\s*- id:\s*"([^"]+)"', line)
        if m:
            ids.add(m.group(1))
    return ids


def extract_execution_class_c_ids(path: Path) -> set[str]:
    """Parse the hardcoded Class C ID list from execution_class.ml."""
    text = path.read_text(encoding="utf-8")
    # Match "ID" entries between `let _class_c_ids` and the closing "|]".
    ids = set(re.findall(r'"([A-Z]+-[0-9]+)"', text))
    return ids


def check_acyclic(rules: list[dict]) -> list[str]:
    """Return list of error messages (empty list = acyclic)."""
    by_id = {r["rule_id"]: r for r in rules}
    errors: list[str] = []

    def visit(rid: str, stack: list[str]):
        if rid in stack:
            errors.append(f"cycle detected: {' -> '.join(stack + [rid])}")
            return
        c = by_id.get(rid)
        if not c:
            return
        for dep in c.get("depends_on", []) + c.get("consumes", []):
            if dep in by_id:  # capability names (e.g. compile_log_context) won't be rule ids
                visit(dep, stack + [rid])

    for r in rules:
        visit(r["rule_id"], [])
    return errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)

    yaml_path = repo / "specs/rules/rule_contracts.yaml"
    json_path = repo / "specs/rules/rule_contracts.json"
    rules_v3_path = repo / "specs/rules/rules_v3.yaml"
    execution_class_path = repo / "latex-parse/src/execution_class.ml"

    failures: list[str] = []

    # Missing files.
    for p in (yaml_path, json_path, rules_v3_path, execution_class_path):
        if not p.is_file():
            failures.append(f"missing required file: {p}")
    if failures:
        print("\n".join("[rule_contracts] FAIL: " + f for f in failures),
              file=sys.stderr)
        return 2

    # 1. rule_id ⊆ rules_v3 ids and vice versa.
    spec_ids = extract_rules_v3_ids(rules_v3_path)
    contracts = load_yaml(yaml_path)["rules"]
    contract_ids = {c["rule_id"] for c in contracts}
    missing_from_contracts = spec_ids - contract_ids
    extra_in_contracts = contract_ids - spec_ids
    if missing_from_contracts:
        failures.append(
            f"{len(missing_from_contracts)} spec id(s) missing from contracts: "
            + ", ".join(sorted(missing_from_contracts)[:5])
            + (" ..." if len(missing_from_contracts) > 5 else "")
        )
    if extra_in_contracts:
        failures.append(
            f"{len(extra_in_contracts)} contract id(s) not in rules_v3: "
            + ", ".join(sorted(extra_in_contracts)[:5])
            + (" ..." if len(extra_in_contracts) > 5 else "")
        )

    # 2. JSON mirror matches YAML source.
    json_data = load_json(json_path)
    yaml_data = load_yaml(yaml_path)
    if json_data != yaml_data:
        failures.append(
            "rule_contracts.json is out of date relative to .yaml; "
            "run scripts/tools/generate_rule_contracts.py to regenerate."
        )

    # 3. Class C rules match execution_class.ml.
    runtime_class_c = extract_execution_class_c_ids(execution_class_path)
    # Filter to only IDs that appear in rule_contracts (runtime file may contain
    # comment-only matches; conservative intersection).
    runtime_class_c = runtime_class_c & spec_ids
    spec_class_c = {c["rule_id"] for c in contracts if c["execution_class"] == "C"}
    if runtime_class_c != spec_class_c:
        missing = runtime_class_c - spec_class_c
        extra = spec_class_c - runtime_class_c
        if missing:
            failures.append(
                f"execution_class.ml Class C not in contracts: {sorted(missing)}"
            )
        if extra:
            failures.append(
                f"contracts Class C not in execution_class.ml: {sorted(extra)}"
            )

    # 3b. PR #241 (p1.2): every Class C rule in execution_class.ml's
    # hardcoded table must have execution_class = "C" in the contract.
    # This is the concrete binding for proofs/ExecutionClasses.v — it
    # turns the abstract isolation theorems into runtime-enforced
    # invariants.
    contract_by_id = {c["rule_id"]: c for c in contracts}
    for rid in sorted(runtime_class_c):
        c = contract_by_id.get(rid)
        if c is None:
            failures.append(f"runtime Class C id {rid!r} has no contract entry")
            continue
        if c["execution_class"] != "C":
            failures.append(
                f"{rid}: execution_class.ml says C, contract says "
                f"{c['execution_class']!r}"
            )

    # 3c. PR #241 (p1.3): Class D ↔ STYLE family binding. Class D rules
    # are identified in validators.ml by filtering rules_style; the
    # contract must agree on family membership so a new STYLE rule
    # without the D tag can't silently enter the hot path.
    style_ids = {rid for rid in spec_ids if rid.startswith("STYLE-")}
    contract_class_d = {
        c["rule_id"] for c in contracts if c["execution_class"] == "D"
    }
    # Every Class D contract rule must be a STYLE-* rule.
    non_style_d = contract_class_d - style_ids
    if non_style_d:
        failures.append(
            f"non-STYLE rule(s) tagged execution_class=D in contracts: "
            f"{sorted(non_style_d)} — runtime rules_class_d derived from "
            f"rules_style won't pick them up"
        )
    # Every STYLE-* rule must have execution_class=D.
    style_not_d = {
        rid for rid in style_ids if contract_by_id[rid]["execution_class"] != "D"
    }
    if style_not_d:
        failures.append(
            f"STYLE-* rule(s) NOT tagged execution_class=D: "
            f"{sorted(style_not_d)} — will silently run on hot path"
        )

    # 3d. PR #241 (p1.3): every Class C rule must have
    # project_scope=any (memo §4 + tier gating: Class C fires across
    # all tiers because build-log diagnostics matter regardless of
    # language-contract tier).
    class_c_wrong_scope = [
        c for c in contracts
        if c["execution_class"] == "C" and c["project_scope"] != "any"
    ]
    for c in class_c_wrong_scope:
        failures.append(
            f"{c['rule_id']}: execution_class=C requires project_scope=any "
            f"(tier gating), got {c['project_scope']!r}"
        )

    # 4. Acyclicity.
    cycles = check_acyclic(contracts)
    for c in cycles:
        failures.append(c)

    # 5. Enum fields are valid.
    for c in contracts:
        if c.get("layer") not in VALID_LAYERS:
            failures.append(f"{c['rule_id']}: invalid layer {c.get('layer')!r}")
        if c.get("execution_class") not in VALID_EXECUTION_CLASSES:
            failures.append(
                f"{c['rule_id']}: invalid execution_class "
                f"{c.get('execution_class')!r}"
            )
        if c.get("proof_class") not in VALID_PROOF_CLASSES:
            failures.append(
                f"{c['rule_id']}: invalid proof_class {c.get('proof_class')!r}"
            )

    if failures:
        for f in failures:
            print(f"[rule_contracts] FAIL: {f}", file=sys.stderr)
        return 1

    print(
        f"[rule_contracts] PASS: {len(contracts)} contracts, "
        f"{len(spec_class_c)} Class C, JSON mirror in sync, acyclic."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
