#!/usr/bin/env python3
"""Compare the opam packages two CI runs installed, job by job (C-180).

For a toolchain change (opam version, solver, installer), the question is
whether the jobs still resolve the SAME package versions. This reads the
`∗ installed NAME.VERSION` lines of each job's log in a branch run and in the
last successful run of the same workflow on main, and prints, per job, the
counts and every package whose version differs.

Two causes of a difference are NOT the solver: (1) opam-repository moved
between the runs (check when the newer version was added); (2) one run
restored its switch from cache, so it never printed the switch's packages.

Usage: compare_opam_installs.py BRANCH_RUN_ID WORKFLOW_FILE [BRANCH_RUN_ID WORKFLOW_FILE ...]
Needs `gh` authenticated. Exit 1 if any job printed no install line at all
(the comparison would be vacuous).
"""
from __future__ import annotations

import collections
import json
import re
import subprocess
import sys
import time

REPO = "ClanClanClanClan/latex_perf"
# `gh run view --log` prints the escape character as a literal `^[`.
ANSI = re.compile(r"(?:\x1b|\^\[)\[[0-9;]*m")
INSTALLED = re.compile(r"(?:∗|->)\s+installed\s+(\S+?)\.(\S+)$")


def installs(run: str) -> dict[str, dict[str, str]]:
    for attempt in range(3):            # the log endpoint fails transiently
        p = subprocess.run(["gh", "run", "view", run, "--repo", REPO, "--log"],
                           capture_output=True, text=True)
        if p.returncode == 0:
            break
        time.sleep(10)
    else:
        raise SystemExit(f"FAIL: could not fetch the log of run {run}: {p.stderr.strip()[:200]}")
    log = p.stdout
    by: dict[str, dict[str, str]] = collections.defaultdict(dict)
    for ln in log.splitlines():
        parts = ln.split("\t", 2)
        if len(parts) < 3:
            continue
        txt = ANSI.sub("", re.sub(r"^\S+Z ", "", parts[2])).strip()
        m = INSTALLED.search(txt)
        if m:
            by[parts[0]][m.group(1)] = m.group(2)
    return by


def main(argv: list[str]) -> int:
    if len(argv) < 2 or len(argv) % 2:
        print(__doc__)
        return 2
    empty = 0
    for br, wf in zip(argv[::2], argv[1::2]):
        main_run = json.loads(subprocess.run(
            ["gh", "run", "list", "--repo", REPO, "--workflow", wf, "--branch", "main",
             "--status", "success", "--limit", "1", "--json", "databaseId,createdAt",
             "-q", ".[0]"], capture_output=True, text=True, check=True).stdout)
        a, b = installs(str(main_run["databaseId"])), installs(br)
        for job in sorted(set(a) | set(b)):
            A, B = a.get(job, {}), b.get(job, {})
            empty += (not A) + (not B)
            diff = {k: (A.get(k), B.get(k)) for k in set(A) | set(B) if A.get(k) != B.get(k)}
            print(f"{wf:32s} {job:14s} main {main_run['databaseId']} "
                  f"({main_run['createdAt'][:10]}) n={len(A)} | branch {br} n={len(B)} "
                  f"| differ={len(diff)}")
            for k, (x, y) in sorted(diff.items()):
                print(f"      {k}: main={x} branch={y}")
    if empty:
        print(f"FAIL: {empty} job log(s) printed no install line")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
