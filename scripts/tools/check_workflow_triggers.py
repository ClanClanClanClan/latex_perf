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

4. A RETRY LOOP THAT CANNOT FAIL (found 2026-09-13).
   The idiom

       for attempt in 1 2 3; do
         probe && break
         sleep 15
       done

   exits 0 when every attempt fails: under `bash -eo pipefail` a command that
   fails inside an `&&` list does not trip -e, and the loop's exit status is
   that of its last command -- `sleep`. Four of these were live at once, all
   of them readiness waits, all of them reporting READY when nothing was:
   setup-ocaml-env's dependency install, and the warmup loops in
   rust-proxy-smoke / rest-smoke / rest-schema. Measured before the fix: with
   every probe failing, all four exited 0. A bounded loop that `break`s on
   success must therefore be followed by an exhaustion guard that exits
   non-zero. This is a SHAPE check -- it proves a failing exit exists after the
   loop, not that it is reachable for the right reason.

5. A DRIFTED `uses:` RETRY PAIR.
   A `uses:` step cannot be wrapped in a shell retry loop, so retrying one means
   writing it twice: attempt 1 with `continue-on-error: true` and an `id`,
   attempt 2 guarded by `if: steps.<id>.outcome == 'failure'`. The two `with:`
   blocks are then a copy-paste pair that nothing keeps in step, and a retry
   that installs a DIFFERENT toolchain than the first attempt is worse than no
   retry. This gate pins them byte-equal.

Authority: .github/required-status-checks.json. That file -- never the
branch-protection API -- is the source of truth; branch-protection.yml PUTs its
contents on every push to main, so an API patch is reverted on the next push.

Exit 1 on any violation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import yaml

WORKFLOW_DIR = Path(".github/workflows")
ACTION_DIR = Path(".github/actions")
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


# ── Failure mode 4: bounded retry loops that cannot fail ──────────────

LOOP_HEAD = re.compile(r"^(\s*)(?:for|while|until)\b.*;\s*do\s*$")
# `exit 1`, `exit 2`, `exit $rc`, `exit "$rc"` -- anything but `exit 0`.
FAILING_EXIT = re.compile(r"\bexit\s+(?:[1-9]\d*|\$|\"\$)")
# An early exit from the loop on SUCCESS: bare `break`, `... && break`,
# `; break`, or an `exit 0` used the same way. Anchored on a command
# boundary so the word inside a longer token does not match.
EARLY_BREAK = re.compile(r"(?:^|[;&|]\s*|\bthen\s+)(?:break\b|exit\s+0\b)")


def strip_comment(line: str) -> str:
    """Drop a trailing `# ...` so prose about `break` is not read as code."""
    out, quote = [], None
    for ch in line:
        if quote:
            out.append(ch)
            if ch == quote:
                quote = None
        elif ch in "'\"":
            quote = ch
            out.append(ch)
        elif ch == "#" and (not out or out[-1].isspace()):
            break
        else:
            out.append(ch)
    return "".join(out).strip()


def iter_run_blocks(doc: dict, rel: str):
    """Yield (step_label, run_text) for every `run:` in a workflow or action."""
    if isinstance(doc.get("jobs"), dict):
        for job_id, job in doc["jobs"].items():
            if not isinstance(job, dict):
                continue
            for i, step in enumerate(job.get("steps") or []):
                if isinstance(step, dict) and step.get("run"):
                    label = step.get("name") or f"step {i}"
                    yield f"{rel} :: {job_id} :: {label}", step["run"]
    runs = doc.get("runs")
    if isinstance(runs, dict):
        for i, step in enumerate(runs.get("steps") or []):
            if isinstance(step, dict) and step.get("run"):
                label = step.get("name") or f"step {i}"
                yield f"{rel} :: {label}", step["run"]


def unguarded_retry_loops(run_text: str) -> list[int]:
    """Line numbers (1-based, within the block) of retry loops with no guard.

    A RETRY loop is a bounded loop whose body contains a bare `break` or a
    bare `exit 0` -- i.e. one that stops early on success. Its guard is a
    failing `exit` anywhere between its own `done` and the next retry loop
    (or the end of the run block).
    """
    lines = run_text.splitlines()
    heads = []
    for n, line in enumerate(lines):
        m = LOOP_HEAD.match(line)
        if m:
            heads.append((n, m.group(1)))

    bad = []
    for idx, (start, indent) in enumerate(heads):
        done = None
        for n in range(start + 1, len(lines)):
            if lines[n].rstrip() == f"{indent}done":
                done = n
                break
        if done is None:            # `done` on a shared line etc -- not our shape
            continue
        body = [strip_comment(ln) for ln in lines[start + 1:done]]
        # `break` is rarely on a line of its own: the compact form of this
        # idiom is `probe && break`, which is what the FIRST draft of this
        # detector missed -- on exactly the loop that prompted it.
        breaks_early = any(EARLY_BREAK.search(b) for b in body)
        if not breaks_early:
            continue                # a plain for-each, not a retry
        nxt = next((h for h, _ in heads[idx + 1:] if h > done), len(lines))
        window = lines[done + 1:nxt]
        if not any(FAILING_EXIT.search(ln) for ln in window):
            bad.append(start + 1)
    return bad


# ── Failure mode 5: drifted `uses:` retry pairs ───────────────────────

def drifted_retry_pairs(doc: dict, rel: str) -> list[str]:
    """A continue-on-error `uses:` step and its guarded twin must match."""
    steps = []
    if isinstance(doc.get("runs"), dict):
        steps += doc["runs"].get("steps") or []
    if isinstance(doc.get("jobs"), dict):
        for job in doc["jobs"].values():
            if isinstance(job, dict):
                steps += job.get("steps") or []

    out = []
    for step in steps:
        if not isinstance(step, dict):
            continue
        if not (step.get("continue-on-error") is True and step.get("uses")
                and step.get("id")):
            continue
        want = f"steps.{step['id']}.outcome == 'failure'"
        twin = next((t for t in steps if isinstance(t, dict)
                     and want in str(t.get("if", ""))
                     and t.get("uses") == step["uses"]), None)
        if twin is None:
            out.append(
                f"{rel}: step '{step.get('name', step['id'])}' is "
                f"continue-on-error, so its failure is SWALLOWED, but no later "
                f"step re-runs `{step['uses']}` under "
                f"`if: {want}`. Either add the retry or drop continue-on-error.")
            continue
        if (step.get("with") or {}) != (twin.get("with") or {}):
            out.append(
                f"{rel}: the two `{step['uses']}` attempts have DRIFTED -- "
                f"attempt 1 ('{step.get('name', step['id'])}') and its retry "
                f"('{twin.get('name', '?')}') pass different `with:` blocks, so "
                f"a retry would build a different toolchain than the attempt it "
                f"replaces. Keep them byte-identical.")
    return out


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

    # ── Failure modes 4 and 5: scan workflows AND composite actions. ──
    # Composite actions were previously invisible to this gate, which is
    # exactly where the worst instance lived (setup-ocaml-env is used by 28
    # workflows, so one silent success there is 28 silent successes).
    scanned = list(workflows) + sorted((repo / ACTION_DIR).rglob("action.yml"))
    loops_checked = 0
    for path in scanned:
        rel = str(path.relative_to(repo))
        try:
            doc = yaml.safe_load(path.read_text()) or {}
        except yaml.YAMLError as exc:
            findings.append(f"{rel} is not valid YAML: {exc}")
            continue
        for label, run_text in iter_run_blocks(doc, rel):
            loops_checked += 1
            for lineno in unguarded_retry_loops(run_text):
                findings.append(
                    f"SILENT-RETRY: {label}, line {lineno} of its `run:` block, "
                    f"is a bounded retry loop with no exhaustion guard. When "
                    f"every attempt fails the loop's exit status is its last "
                    f"command (usually `sleep`), so the step reports SUCCESS "
                    f"with the thing it was waiting for never ready. Track "
                    f"success in a flag and `exit 1` after `done`.")
        findings.extend(drifted_retry_pairs(doc, rel))

    if not loops_checked:
        print("FAIL: scanned zero `run:` blocks -- the mode-4 scan is vacuous",
              file=sys.stderr)
        return 1

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
          f"resolve to exactly one job, none with an unfiltered push trigger; "
          f"{loops_checked} `run:` block(s) across {len(scanned)} workflow/action "
          f"file(s) carry no unguarded retry loop and no drifted retry pair")
    return 0


if __name__ == "__main__":
    sys.exit(main())
