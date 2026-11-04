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


LIMIT = 1000
BAD = ("failure", "cancelled", "timed_out", "startup_failure")


def runs(wf: str, since: str) -> list[dict]:
    out = subprocess.run(
        ["gh", "run", "list", "--repo", REPO, "--workflow", f"{wf}.yml",
         "--limit", str(LIMIT), "--created", f">={since}", "--json",
         "databaseId,conclusion,status,createdAt,headSha,headBranch,attempt"],
        capture_output=True, text=True, check=True).stdout
    rs = json.loads(out)
    if len(rs) >= LIMIT:
        raise SystemExit(f"FAIL: {wf}: {len(rs)} runs = --limit {LIMIT}; the list is "
                         f"truncated and the tally would be partial")
    return rs


def attempts(r: dict) -> list[dict]:
    """Every attempt of a run: `gh run list` reports only the latest, and a
    re-run that passed hides the attempt that failed."""
    n = int(r.get("attempt") or 1)
    out = [dict(r, attempt=n)]
    for a in range(1, n):
        d = json.loads(subprocess.run(
            ["gh", "api", f"repos/{REPO}/actions/runs/{r['databaseId']}/attempts/{a}"],
            capture_output=True, text=True, check=True).stdout)
        out.append(dict(r, attempt=a, conclusion=d.get("conclusion"), status=d.get("status")))
    return out


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
    unknown = 0
    for wf in WORKFLOWS:
        rs = runs(wf, ns.since)
        if not rs:
            print(f"FAIL: {wf}: zero runs listed -- the tally would be vacuous")
            return 1
        c = collections.Counter()
        bad = []
        for r in rs:
            for a in attempts(r):
                if a.get("status") != "completed":
                    cls = "unknown"
                elif a["createdAt"] < FIX_TIME:
                    cls = "pre"
                else:
                    cls = {True: "post", False: "pre", None: "unknown"}[contains_fix(a["headSha"])]
                unknown += cls == "unknown"
                c[(cls, a.get("conclusion") or a.get("status"))] += 1
                if a.get("conclusion") in BAD:
                    bad.append(f"{cls}:{a['databaseId']}#{a['attempt']}:{a['conclusion']}")
        total.update(c)
        print(f"{wf:24s} {dict(sorted(c.items()))} not-success={bad}")
    print(f"TOTAL attempts {dict(sorted(total.items()))}")
    for cls in ("pre", "post"):
        n = sum(v for (k, _), v in total.items() if k == cls)
        nb = {b: total[(cls, b)] for b in BAD if total[(cls, b)]}
        print(f"{cls}-fix: {n} attempt(s); not-success {nb or 0}")
    if unknown:
        print(f"NO BOUND: {unknown} attempt(s) could not be classified (in progress, or "
              f"ancestry undecidable); refusing to print a rate bound")
        return 1
    post = sum(v for (k, _), v in total.items() if k == "post")
    post_bad = sum(total[("post", b)] for b in BAD)
    if post and not post_bad:
        print(f"zero post-fix failures/cancellations/time-outs bound the post-fix rate "
              f"below 3/{post} = {3 / post:.4f} (95%). A pool hang can surface as "
              f"`cancelled`, so cancellations count as bad here; compare with the "
              f"pre-fix rate of the POOL class only (classify each pre-fix "
              f"not-success attempt by its log first)")
    elif post_bad:
        print(f"{post_bad} post-fix not-success attempt(s): read their logs before any claim")
    return 0


if __name__ == "__main__":
    sys.exit(main())
