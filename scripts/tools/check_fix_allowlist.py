#!/usr/bin/env python3
"""Every rule in the DEFAULT auto-fix set must carry measured evidence (OPEN-112).

    python3 scripts/tools/check_fix_allowlist.py [--repo .]

WHY. The default `--apply-fixes` applies only `Fix_policy.default_allowlist`
(latex-parse/src/fix_policy.ml). OPEN-110 measured that a rule with zero
compile breaks can still change what a paper SAYS -- CHEM-005 turned
`c_- > 0` into `c→ 0` inside a theorem and the paper compiled. So membership
in the default set is a CLAIM, and a claim about a user's document needs the
same provenance as any other number here. This gate refuses a list entry
unless the evidence says it is safe.

CHECKS, for each id in `default_allowlist`:
  1. it is not in `Fix_policy.implicated` (rules in a measured break repair
     set) -- the OCaml unit test checks this too; a Python copy costs nothing
     and fails in the pure spec-drift job;
  2. it is in NO repair set of corpora/apply_fixes_real/rule_attribution_*.json;
  3. corpora/apply_fixes_real/fix_meaning_review.json gives it verdict "safe"
     AND records a refutation attempt that found no damage;
  4. corpora/apply_fixes_real/fix_meaning_audit.json has >= 1 sampled build
     where the rule applied >= 1 edit ALONE and both builds compiled.
And globally: the list parses and is non-empty-or-explicitly-empty, has no
duplicates, and no reviewed-UNSAFE rule appears in it.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

POLICY = "latex-parse/src/fix_policy.ml"
REVIEW = "corpora/apply_fixes_real/fix_meaning_review.json"
AUDIT = "corpora/apply_fixes_real/fix_meaning_audit.json"
ATTR_GLOB = "corpora/apply_fixes_real/rule_attribution_*.json"


def ocaml_string_list(src: str, name: str) -> list[str] | None:
    m = re.search(r"let\s+" + re.escape(name) + r"\s*(?::[^=]*)?=\s*\[(.*?)\]",
                  src, re.S)
    if not m:
        return None
    body = re.sub(r"\(\*.*?\*\)", "", m.group(1), flags=re.S)
    return re.findall(r'"([^"]+)"', body)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ns = ap.parse_args()
    repo = pathlib.Path(ns.repo).resolve()
    findings: list[str] = []

    src = (repo / POLICY).read_text()
    allow = ocaml_string_list(src, "default_allowlist")
    implicated = ocaml_string_list(src, "implicated")
    if allow is None or implicated is None:
        print(f"[fix-allowlist] FAIL: could not parse default_allowlist / "
              f"implicated from {POLICY}", file=sys.stderr)
        return 2
    if len(implicated) < 20:
        # The measured set is 24; a truncated parse must not pass vacuously.
        findings.append(f"implicated parsed as only {len(implicated)} ids")
    dups = sorted({x for x in allow if allow.count(x) > 1})
    if dups:
        findings.append(f"duplicate ids in default_allowlist: {dups}")

    review = json.loads((repo / REVIEW).read_text())["rules"]
    audit = json.loads((repo / AUDIT).read_text())["results"]
    repair: dict[str, list[str]] = {}
    attr_files = sorted(repo.glob(ATTR_GLOB))
    if not attr_files:
        findings.append(f"no {ATTR_GLOB} artefact: repair sets cannot be checked")
    for f in attr_files:
        for shard in json.loads(f.read_text())["shards"]:
            for row in shard["rows"]:
                for rule in ((row.get("attribution") or {}).get("repair_set") or []):
                    repair.setdefault(rule, []).append(row["arxiv_id"])

    for rule in allow:
        if rule in implicated:
            findings.append(f"{rule} is in the default set but listed as "
                            f"implicated in a measured break")
        if rule in repair:
            findings.append(f"{rule} is in the repair set of "
                            f"{len(repair[rule])} measured break(s), e.g. "
                            f"{repair[rule][0]}")
        rv = review.get(rule)
        if rv is None:
            findings.append(f"{rule} has no entry in {REVIEW}")
        else:
            if rv.get("verdict") != "safe":
                findings.append(f"{rule} is reviewed {rv.get('verdict')!r}, "
                                f"not 'safe'")
            ref = rv.get("refutation")
            if not ref or ref.get("found_damage") is not False:
                findings.append(f"{rule} has no refutation attempt that found "
                                f"no damage")
        good = [r for r in audit if r.get("rule") == rule
                and r.get("edits_alone", 0) > 0
                and r.get("rc_pristine") == 0 and r.get("rc_fixed") == 0]
        if not good:
            findings.append(f"{rule} has no audited build where it applied an "
                            f"edit alone and both builds compiled")

    if findings:
        print(f"[fix-allowlist] FAIL: {len(findings)} problem(s)", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[fix-allowlist] PASS: {len(allow)} default rule(s), each unimplicated "
          f"in {sum(len(v) for v in repair.values())} measured repair-set "
          f"entries, reviewed safe, refutation found no damage, and audited "
          f"with a compiling standalone build: {', '.join(allow) or '(none)'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
