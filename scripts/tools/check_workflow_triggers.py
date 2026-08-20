#!/usr/bin/env python3
"""Gate: the workflows behind REQUIRED status checks must be unambiguous.

Three failure modes, each of which has actually bitten this repo:

1. DUPLICATE REQUIRED CONTEXT (the reason this gate exists).
   A workflow with an unfiltered `push:` fires on every branch, so a commit
   on a PR branch runs it TWICE -- once on `push`, once on `pull_request` --
   publishing two check-runs under the SAME required-context name on the SAME
   sha. They do not cancel each other: the usual concurrency group key,
   `${{ github.workflow }}-${{ github.event.pull_request.number || github.ref }}`,
   falls back to `github.ref` when there is no pull_request number, so the two
   runs land in different groups. GitHub's status rollup then honours whichever
   check-run reported LAST rather than whichever passed.

   PR #531 was blocked exactly this way: the push-event `unit-tests` passed in
   11m50s while the duplicate pull_request-event run hit a 25-minute network
   timeout in setup-ocaml-env and was cancelled. One flake, zero real failures,
   a hard merge block -- and the check LIST looked green, because the failure is
   only visible in `gh pr view --json statusCheckRollup`.

2. COLLIDING JOB NAME. The job id IS the status-check context. Two workflow
   files declaring the same job id make a required context ambiguous: it can
   resolve to the wrong workflow, or hang pending forever. spec-drift.yml's own
   job comment records a prior instance ("renamed from the generic [check],
   which collided with another workflow's job of the same name"). At the time of
   writing, `build` is declared by BOTH ci.yml and spacy-container.yml -- which
   is why `build` cannot be promoted to required until one is renamed. This gate
   makes that prerequisite mechanical instead of remembered.

3. ORPHANED REQUIRED CONTEXT. Renaming a job that is in the required list
   orphans the requirement: no run ever publishes it, so every PR waits pending
   forever with no failing check to point at.

Authority: .github/required-status-checks.json. That file -- never the
branch-protection API -- is the source of truth; branch-protection.yml PUTs its
contents on every push to main, so an API patch is reverted on the next push.

Exit 1 on any violation.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import yaml

WORKFLOW_DIR = Path(".github/workflows")
REQUIRED_JSON = Path(".github/required-status-checks.json")

# A `push:` trigger counts as SCOPED if it carries any of these filters. Any one
# of them stops the workflow firing on every branch of every PR, which is all
# this gate cares about.
PUSH_FILTERS = ("branches", "branches-ignore", "tags", "tags-ignore", "paths",
                "paths-ignore")


def load_on_block(doc: dict) -> dict | list | None:
    """Return a workflow's trigger block.

    YAML 1.1 parses a bare `on:` key as the boolean True, so the block can be
    filed under either "on" or True depending on quoting. Check both.
    """
    if "on" in doc:
        return doc["on"]
    return doc.get(True)


def push_is_unfiltered(on_block: dict | list | None) -> bool:
    """True iff this workflow fires on a push to ANY branch."""
    if isinstance(on_block, str):
        return on_block == "push"
    if isinstance(on_block, list):
        # Flow style, e.g. `on: [push, pull_request]` -- no filters possible.
        return "push" in on_block
    if not isinstance(on_block, dict) or "push" not in on_block:
        return False
    push = on_block["push"]
    if push is None:  # bare `push:` with an empty body
        return True
    if isinstance(push, dict):
        return not any(k in push for k in PUSH_FILTERS)
    return False


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".", help="repository root")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    required_path = repo / REQUIRED_JSON
    if not required_path.is_file():
        print(f"FAIL: {REQUIRED_JSON} not found", file=sys.stderr)
        return 1
    required = [c["context"] for c in
                json.loads(required_path.read_text())["checks"]]

    # Non-vacuity, both halves. A gate that silently processes nothing is worse
    # than no gate: it reports PASS forever. This repo has one required check
    # that has SKIPped for 185 days for exactly that reason.
    if not required:
        print(f"FAIL: {REQUIRED_JSON} lists zero required checks", file=sys.stderr)
        return 1

    workflows = sorted((repo / WORKFLOW_DIR).glob("*.yml"))
    if not workflows:
        print(f"FAIL: no workflows found under {WORKFLOW_DIR}", file=sys.stderr)
        return 1

    # job id -> [workflow paths declaring it]. The job id is the context name;
    # a `name:` field would override it, so prefer that when present.
    publishers: dict[str, list[str]] = {}
    unfiltered: set[str] = set()

    for wf in workflows:
        try:
            doc = yaml.safe_load(wf.read_text()) or {}
        except yaml.YAMLError as exc:
            print(f"FAIL: {wf.relative_to(repo)} is not valid YAML: {exc}",
                  file=sys.stderr)
            return 1
        bare_push = push_is_unfiltered(load_on_block(doc))
        for job_id, job in (doc.get("jobs") or {}).items():
            name = job.get("name", job_id) if isinstance(job, dict) else job_id
            # A templated name is not a stable context; fall back to the id.
            context = job_id if "${{" in str(name) else str(name)
            publishers.setdefault(context, []).append(str(wf.relative_to(repo)))
            if bare_push:
                unfiltered.add(context)

    findings: list[str] = []

    for context in required:
        who = publishers.get(context, [])
        if not who:
            findings.append(
                f"ORPHANED: required context '{context}' is published by no job "
                f"in {WORKFLOW_DIR}. Every PR will wait pending forever with no "
                f"failing check to point at. Rename the job back, or drop the "
                f"context from {REQUIRED_JSON}.")
        elif len(who) > 1:
            findings.append(
                f"AMBIGUOUS: required context '{context}' is declared by "
                f"{len(who)} workflows ({', '.join(who)}). The job id IS the "
                f"status-check context; a collision resolves to the wrong "
                f"workflow or hangs pending. Rename one.")
        if context in unfiltered:
            findings.append(
                f"DUPLICATED: '{context}' is published by a workflow with an "
                f"unfiltered `push:`, so a PR branch publishes this required "
                f"context TWICE per commit under one name and the rollup "
                f"honours whichever finished last, not whichever passed. Scope "
                f"push to `branches: [main]` -- `pull_request:` already covers "
                f"every push to an open PR.")

    if findings:
        print(f"[workflow-triggers] FAIL: {len(findings)} violation(s)",
              file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print(f"[workflow-triggers] PASS: {len(required)} required context(s) each "
          f"resolve to exactly one job, none with an unfiltered push trigger "
          f"({len(workflows)} workflows scanned)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
