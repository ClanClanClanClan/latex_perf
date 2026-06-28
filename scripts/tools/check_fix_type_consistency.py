#!/usr/bin/env python3
"""check_fix_type_consistency.py — guard the rules_v3.yaml `fix:` field against
drift from the runtime reality recorded in rule_contracts.yaml `produces_fix`.

For every IMPLEMENTED rule (one whose contract has produces_fix == true or
false — i.e. it has a runtime `run`, as opposed to a pending rule whose
produces_fix is null), the spec's `fix:` field must agree with whether the rule
actually emits a fix:

    produces_fix: true   <=>  fix: <non-null token>
    produces_fix: false  <=>  fix: null

Pending/unimplemented rules (produces_fix == null) are exempt: their `fix:`
field records a PLANNED fix type and is allowed to be set before the impl
exists.

This closes the drift class found by the 2026-06-28 impl-vs-spec audit, where
~31 implemented rules had a `fix:` field that disagreed with the runtime
(e.g. TYPO-006/024 emitted a fix while the spec said `fix: null`, and several
diagnose-only rules carried a `fix:` token they never produced).
"""
import sys
import os

try:
    import yaml
except ImportError:
    print("[fix-type-consistency] SKIP: pyyaml not available", file=sys.stderr)
    sys.exit(0)


def main():
    repo = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    spec_path = os.path.join(repo, "specs/rules/rules_v3.yaml")
    cat_path = os.path.join(repo, "specs/rules/rule_contracts.yaml")

    spec_raw = yaml.safe_load(open(spec_path))
    spec = {r["id"]: r for r in spec_raw if isinstance(r, dict) and "id" in r}

    cat_raw = yaml.safe_load(open(cat_path))
    cat_list = cat_raw if isinstance(cat_raw, list) else cat_raw.get(
        "rules", cat_raw.get("contracts", [])
    )
    produces = {
        (r.get("rule_id") or r.get("id")): r.get("produces_fix")
        for r in cat_list
        if isinstance(r, dict)
    }

    def has_fix(rule):
        fx = rule.get("fix")
        return fx is not None and fx != "null"

    violations = []
    checked = 0
    for rid, rule in spec.items():
        pf = produces.get(rid)
        if pf is None:
            continue  # pending / not implemented — fix: is a plan, exempt
        checked += 1
        if pf is True and not has_fix(rule):
            violations.append(
                f"{rid}: produces_fix=true but spec fix: is null "
                f"(impl emits a fix the spec does not record)"
            )
        elif pf is False and has_fix(rule):
            violations.append(
                f"{rid}: produces_fix=false but spec fix: = {rule.get('fix')!r} "
                f"(spec prescribes a fix the impl does not produce)"
            )

    if violations:
        print(
            f"[fix-type-consistency] FAIL: {len(violations)} implemented "
            f"rule(s) drift between rules_v3.yaml fix: and rule_contracts "
            f"produces_fix:"
        )
        for v in violations:
            print(f"  - {v}")
        print(
            "  Fix: set rules_v3.yaml `fix:` to a fix-type token for "
            "fix-producing rules, or to null for diagnose-only rules."
        )
        sys.exit(1)

    print(
        f"[fix-type-consistency] PASS: {checked} implemented rules — "
        f"rules_v3.yaml fix: agrees with rule_contracts produces_fix."
    )


if __name__ == "__main__":
    main()
