#!/usr/bin/env python3
"""check_fix_type_consistency.py — guard the rules_v3.yaml `fix:` field against
drift from the runtime reality recorded in rule_contracts.yaml `produces_fix`.

⚠ THIS GATE USED TO BE WRONG ABOUT 18 OF THE 26 ROWS IT FLAGGED, and its
remediation hint prescribed exactly the repair that would have destroyed them.
It asserted a biconditional between two fields that measure DIFFERENT things:

    rules_v3.yaml `fix:`      = WHAT the remedy is
    rule_contracts produces_fix = whether the AUTO-APPLY channel ships it

`produces_fix` is not a runtime measurement. `generate_rule_contracts.py`
returns False whenever the id appears in the hand-written
FIX_PRODUCER_DEFERRED dict. Eighteen of those entries are the catalogue's
**Bucket C**: rules that deliberately emit their remedy through the CANDIDATE
channel (`mk_result_with_candidates`) rather than the auto-apply one. All 18
have a candidate producer in `validators*.ml`. Reporting them as "the impl does
not produce a fix" was false, and nulling their `fix:` tokens — which is what
the old hint told you to do — would have deleted 18 correct commitments to make
a wrong gate green.

The rule is therefore three-way, not two-way:

    produces_fix: true             =>  fix: <non-null token>
    produces_fix: false, Bucket C  =>  fix: <non-null token> AND a
                                       mk_result_with_candidates producer exists
    produces_fix: false, otherwise =>  fix: null

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
import re

try:
    import yaml
except ImportError:
    print("[fix-type-consistency] SKIP: pyyaml not available", file=sys.stderr)
    sys.exit(0)

# The Bucket C set is derived from prose in FIX_PRODUCER_DEFERRED, so a reworded
# reason string would silently shrink it and this gate would start demanding
# `fix: null` for rules that legitimately carry a token. Pin the size: a change
# must be deliberate, not a side effect of editing a comment.
BUCKET_C_PINNED = 18


def bucket_c_ids(repo):
    sys.path.insert(0, os.path.join(repo, "scripts", "tools"))
    from generate_rule_contracts import FIX_PRODUCER_DEFERRED
    return {r for r, why in FIX_PRODUCER_DEFERRED.items()
            if why.lstrip().startswith("Bucket C")}


def strip_ocaml_comments(s):
    """Blank `(* ... *)` comments, length-preserving, honouring NESTING.

    ⚠ WITHOUT THIS THE GATE IS COMMENT-BLIND, and a commented-out producer
    satisfies the Bucket C requirement. Measured on the shipped regex:

        (* TODO restore: mk_result_with_candidates ~id:"FAKE-999" ... *)
        -> matched 'FAKE-999'

    So a rule whose only producer had been commented out would still be
    reported as backed by one — the gate would certify an empty promise, which
    is precisely what the Bucket C arm exists to prevent.

    OCaml comments NEST, so a depth counter is required; a non-greedy
    `\\(\\*.*?\\*\\)` would stop at the first `*)` and leave the tail of an outer
    comment live. String literals are deliberately NOT tracked: `~id:"X-001"`
    inside a string is not a producer either, and blanking a comment can only
    make this scan see FEWER ids, which fails CLOSED (a real producer would
    have to be found elsewhere or the gate complains). Under-blanking would be
    the unsafe direction.
    """
    out, i, n, depth = list(s), 0, len(s), 0
    while i < n:
        if s.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        else:
            if depth and s[i] not in "\r\n":
                out[i] = " "
            i += 1
    return "".join(out)


def candidate_producers(repo):
    """Rule ids with a LIVE `mk_result_with_candidates` producer in the validators."""
    src = os.path.join(repo, "latex-parse", "src")
    pat = re.compile(r'mk_result_with_candidates[^;]*?~id:"([A-Z0-9]+-\d+)"', re.S)
    found, files = set(), 0
    for fn in sorted(os.listdir(src)):
        if fn.startswith("validators") and fn.endswith(".ml") and "test" not in fn:
            files += 1
            with open(os.path.join(src, fn), encoding="utf-8") as fh:
                found |= set(pat.findall(strip_ocaml_comments(fh.read())))
    # Anti-vacuity: an empty scan would make the Bucket C arm pass everything.
    if not files or not found:
        print("[fix-type-consistency] PROBE FAILED: scanned "
              f"{files} validator file(s), found {len(found)} candidate "
              "producers. The scan is broken; refusing to report success.")
        sys.exit(2)
    return found


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

    bucket_c = bucket_c_ids(repo)
    if len(bucket_c) != BUCKET_C_PINNED:
        print(f"[fix-type-consistency] PROBE FAILED: Bucket C is "
              f"{len(bucket_c)}, pinned at {BUCKET_C_PINNED}. A reason string "
              f"was reworded or a rule changed bucket. Update the pin "
              f"deliberately, after checking which rules moved.")
        sys.exit(2)
    producers = candidate_producers(repo)

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
                f"(the auto-apply channel ships a fix whose type is unrecorded)"
            )
        elif pf is False and rid in bucket_c:
            # Bucket C ships its remedy through the CANDIDATE channel, so a
            # token is REQUIRED here, not forbidden — and it must be backed by
            # a real producer, or the token is an empty promise.
            if not has_fix(rule):
                violations.append(
                    f"{rid}: Bucket C but spec fix: is null "
                    f"(record the remedy its candidate channel emits)"
                )
            elif rid not in producers:
                violations.append(
                    f"{rid}: Bucket C with fix: {rule.get('fix')!r} but NO "
                    f"mk_result_with_candidates producer in validators*.ml"
                )
        elif pf is False and has_fix(rule):
            violations.append(
                f"{rid}: deferred (not Bucket C) but spec fix: = "
                f"{rule.get('fix')!r} (spec prescribes a remedy nothing ships)"
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
            "  Fix: a rule that SHIPS a remedy needs a `fix:` token — through "
            "the auto-apply channel (produces_fix=true) or, for Bucket C, the "
            "candidate channel. Only a rule that ships NOTHING takes null. "
            "Do NOT null a Bucket C token to silence this gate."
        )
        sys.exit(1)

    print(
        f"[fix-type-consistency] PASS: {checked} implemented rules — "
        f"rules_v3.yaml fix: agrees with rule_contracts produces_fix."
    )


if __name__ == "__main__":
    main()
