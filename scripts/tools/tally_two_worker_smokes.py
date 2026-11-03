#!/usr/bin/env python3
"""OPEN-135: tally the two-worker CI smokes before and after the OPEN-125 fix.

A run counts as POST-fix only if its head commit CONTAINS #632's merge
(6316cff5) -- by ancestry, not by timestamp: a branch that was not rebased
runs pre-fix code after the merge date. Runs created before the merge cannot
contain it. Ancestry is decided by local git when the object is present, else
by the GitHub compare API; a run neither can decide is counted UNKNOWN.

It prints, per workflow and in total, runs by (pre|post|unknown, conclusion),
the failing run ids, and the 95% upper bound on the post-fix failure rate
implied by zero post-fix failures (3/n, the rule of three). OPEN-125 (c) can
close on history only when that bound is below the pre-fix failure rate of
the pool class.

Usage: python3 scripts/tools/tally_two_worker_smokes.py [--since 2026-08-01]
Needs `gh` authenticated and a fetched clone.
"""
from __future__ import annotations

import argparse
import collections
import json
import subprocess
import sys

REPO = "ClanClanClanClan/latex_perf"
FIX = "6316cff543a00ac85387e445954daa3f3abffd1d"   # #632's merge
FIX_TIME = "2026-10-05T09:05:35Z"
# Every workflow that starts the service with L0_POOL_CORES=0,1.
WORKFLOWS = ["rust-proxy-smoke", "l1-smoke", "l1-nightly", "latency-nightly",
             "prometheus-smoke", "rest-schema", "rest-smoke", "unicode-smoke",
             "validators-pilot-smoke"]


def runs(wf: str, since: str) -> list[dict]:
    out = subprocess.run(
        ["gh", "run", "list", "--repo", REPO, "--workflow", f"{wf}.yml",
         "--limit", "1000", "--created", f">={since}", "--json",
         "databaseId,conclusion,createdAt,headSha,headBranch"],
        capture_output=True, text=True, check=True).stdout
    return json.loads(out)


_memo: dict[str, bool | None] = {}


def contains_fix(sha: str) -> bool | None:
    if sha not in _memo:
        rc = subprocess.run(["git", "merge-base", "--is-ancestor", FIX, sha],
                            capture_output=True).returncode
        if rc in (0, 1):
            _memo[sha] = rc == 0
        else:
            st = subprocess.run(
                ["gh", "api", f"repos/{REPO}/compare/{FIX}...{sha}", "-q", ".status"],
                capture_output=True, text=True).stdout.strip()
            _memo[sha] = {"ahead": True, "identical": True,
                          "behind": False, "diverged": False}.get(st)
    return _memo[sha]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--since", default="2026-08-01")
    ns = ap.parse_args()
    total = collections.Counter()
    for wf in WORKFLOWS:
        rs = runs(wf, ns.since)
        if not rs:
            print(f"FAIL: {wf}: zero runs listed -- the tally would be vacuous")
            return 1
        c = collections.Counter()
        fails = []
        for r in rs:
            if r["createdAt"] < FIX_TIME:
                cls = "pre"
            else:
                cls = {True: "post", False: "pre", None: "unknown"}[contains_fix(r["headSha"])]
            c[(cls, r["conclusion"])] += 1
            if r["conclusion"] == "failure":
                fails.append(f"{cls}:{r['databaseId']}")
        total.update(c)
        print(f"{wf:24s} {dict(sorted(c.items()))} failures={fails}")
    post = sum(v for (cls, concl), v in total.items()
               if cls == "post" and concl in ("success", "failure"))
    post_fail = total[("post", "failure")]
    pre = sum(v for (cls, concl), v in total.items()
              if cls == "pre" and concl in ("success", "failure"))
    print(f"TOTAL {dict(sorted(total.items()))}")
    print(f"pre-fix: {total[('pre', 'failure')]} failure(s) in {pre} completed run(s); "
          f"post-fix: {post_fail} failure(s) in {post} completed run(s)")
    if post and not post_fail:
        print(f"zero post-fix failures bound the post-fix rate below 3/{post} "
              f"= {3 / post:.4f} (95%); compare with the pre-fix rate of the POOL "
              f"class only (classify each pre-fix failure by its log first)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
