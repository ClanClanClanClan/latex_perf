#!/usr/bin/env python3
"""Gate: the workflows behind REQUIRED status checks must be unambiguous.

Nine failure modes, each of which has actually bitten this repo:

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

6. A CACHE CLIENT FOR THE RETIRED CACHE SERVICE (C-176, found 2026-11-03).
   ocaml/setup-ocaml@v2 bundles a cache client for GitHub's legacy cache
   service. After that service was retired every restore warned "Cache
   service responded with 400" and every save warned "Our services aren't
   available right now" -- six warnings per X64 job, every job GREEN, no opam
   cache restored for at least five weeks. A cache failure is only a warning,
   so nothing went red. Refused: actions/cache below v3.4.0 / v4.2.0. The
   version is the one .github/action-pins.json records for the pinned SHA:
   this mode TRUSTS that registry (and mode 8 requires the line's
   `# <version>` comment to equal it), so a lying comment fails, while a lying
   registry entry is a reviewed diff that `pin_actions.py --verify` re-derives.

7. A FLOATING RUNNER LABEL (C-177). `ubuntu-latest` moved to Ubuntu 26.04
   from 2026-10-19 (actions/runner-images#14748) and main's jobs changed OS
   with no commit. Every `runs-on:` label must be on an ALLOW-list of fixed
   images (ubuntu-NN.NN[-arm], macos-NN[...], windows-NNNN; compared
   case-insensitively, as GitHub does), a literal or a `${{ matrix.KEY }}`
   over literal values; any other expression is refused because it cannot be
   shown to be fixed.

8. A FLOATING TOOLCHAIN OR ACTION (C-179, C-200). setup-ocaml resolves opam
   to the newest upstream release at run time (2.1.6 under v2, 2.6.1 on
   2026-11-03); dtolnay/rust-toolchain@stable resolves rustc the same way; and
   a tag or branch ref (`@v4`, `@1.99`, `@release`) is mutable. Refused: any
   third-party `uses:` that is not `@<40-hex SHA> # <version>` with that pair
   in .github/action-pins.json; a docker:// ref without `@sha256:`;
   setup-ocaml at any ref; and a version-selecting `with:` input
   (toolchain, *-version, ...) that is not an exact X.Y.Z. `uses:` values are
   read THROUGH the YAML parse (aliases, quoting); one that is not also
   spelled on a plain `uses: VALUE` line, or a quoted `"uses"` key, is
   refused, since its comment could not be read.

9. OPAM FROM ANYWHERE BUT THE PIN (C-179, C-200). opam is installed only by
   setup-ocaml-env's step, whose run text (and the key and switch steps) must
   equal the canonical text in CANON below: an exact release URL, a checksum
   that fails the step before the binary is touched, the compiler from the
   one OCAML_VERSION. Any other `run:` that fetches or package-installs opam
   is refused. Composite actions are scanned wherever they live in the repo.

Authority: .github/required-status-checks.json. That file -- never the
branch-protection API -- is the source of truth; branch-protection.yml PUTs its
contents on every push to main, so an API patch is reverted on the next push.

Exit 1 on any violation.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
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
    # (OPEN-126's cross-pair compiler arm -- setup-ocaml v2 on X64, v3
    # elsewhere, must install the same OCaml -- was removed with C-179: no
    # setup-ocaml step remains, mode 8 refuses one at any ref, and the one
    # compiler is named once, in setup-ocaml-env's switch-create command.)
    return out


# ── Failure modes 6-9: cache clients, runner labels, toolchains, opam ──
#
# TRUST ROOT. A SHA says nothing about which release it is, so every
# third-party `uses:` must be `owner/repo[/path]@<40-hex> # <version>` AND
# that SHA -> version pair must be recorded in .github/action-pins.json.
# Modes 6 and 8 TRUST that registry (a reviewed, committed file written by
# scripts/tools/pin_actions.py, whose `--verify` re-derives every entry from
# GitHub). A comment that disagrees with the registry is refused, so a lying
# `# v4.3.0` on another SHA fails; a lying registry entry is a reviewed diff.

PIN_REGISTRY = Path(".github/action-pins.json")
SHA_REF = re.compile(r"^[0-9a-f]{40}$")
VERSION_REF = re.compile(r"^v?(\d+)(?:\.(\d+))?(?:\.(\d+))?$")
DIGEST_REF = re.compile(r"^docker://[^@\s]+@sha256:[0-9a-f]{64}$")
# Raw lines: a `uses:` written as a plain block-mapping key, and the
# spellings a YAML parser accepts that a line scan would not see.
RAW_USES = re.compile(
    r"^[ \t]*(?:-[ \t]+)?uses:[ \t]*(?P<v>[^\s#'\"]+|'[^']*'|\"[^\"]*\")"
    r"[ \t]*(?:#[ \t]*(?P<c>\S+))?[ \t]*$", re.M)
QUOTED_USES_KEY = re.compile(r"""^[ \t]*(?:-[ \t]+)?["']uses["'][ \t]*:""", re.M | re.I)
# actions/cache talks to the current cache service from v3.4.0 / v4.2.0
# (actions/cache README at v4.3.0); v5+ also.
CACHE_ACTION = "actions/cache"
# Runner labels: an ALLOW-list of fixed images (compared case-insensitively;
# GitHub matches labels case-insensitively). ubuntu-latest, ubuntu-slim and
# any unknown label are refused.
FIXED_RUNNER = re.compile(
    r"^(ubuntu-\d{2}\.\d{2}(-arm)?|macos-\d{2}(-(arm64|intel|large|xlarge))?"
    r"|windows-\d{4}(-arm)?)$")
# `with:` inputs that select a toolchain version.
VERSION_INPUT = re.compile(r"^(toolchain|version|ocaml-compiler|[a-z0-9-]+-version)$", re.I)
EXACT_VERSION = re.compile(r"^\d+\.\d+\.\d+(?:[.+-][0-9A-Za-z.]+)?$")
EXPR = re.compile(r"\$\{\{")
MATRIX_REF = re.compile(r"^\$\{\{\s*matrix\.([\w-]+)\s*\}\}$")
# opam installed by anything but setup-ocaml-env's pinned step.
OPAM_ELSEWHERE = re.compile(
    r"opam\.ocaml\.org/install|ocaml/opam/releases/|github\.com/ocaml/opam/"
    r"|\b(?:apt|apt-get|brew|dnf|yum|apk|snap|nix-env|port)\b[^\n]*\binstall\b[^\n]*\bopam\b",
    re.I)

OPAM_INSTALLER = ACTION_DIR / "setup-ocaml-env" / "action.yml"
OPAM_STEP = "Install opam (pinned, checksum-verified)"
OPAM_STEP_IF = "runner.os == 'Linux' && (runner.arch == 'X64' || runner.arch == 'ARM64')"
OPAM_ENV = {
    "OCAML_VERSION": re.compile(r"^\d+\.\d+\.\d+$"),
    "OPAM_VERSION": re.compile(r"^\d+\.\d+\.\d+$"),
    "OPAM_SHA256_X64": re.compile(r"^[0-9a-f]{64}$"),
    "OPAM_SHA256_ARM64": re.compile(r"^[0-9a-f]{64}$"),
}
# The steps whose text IS the pin: compared line for line (comment-only and
# blank lines dropped, whitespace trimmed). The download URL is exact, the
# checksum line fails the step (set -euo pipefail, nothing after it on the
# line), and nothing touches the binary before the check. Editing these steps
# means editing this constant: that is the point.
CANON = {
    OPAM_STEP: """
set -euo pipefail
case "${RUNNER_ARCH}" in
X64)   arch=x86_64; sum="${OPAM_SHA256_X64}" ;;
ARM64) arch=arm64;  sum="${OPAM_SHA256_ARM64}" ;;
*) echo "::error::[setup-ocaml-env] no pinned opam for ${RUNNER_ARCH}"; exit 1 ;;
esac
url="https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/opam-${OPAM_VERSION}-${arch}-linux"
curl -fsSL --retry 5 --retry-all-errors -o "${RUNNER_TEMP}/opam" "${url}"
echo "${sum}  ${RUNNER_TEMP}/opam" | sha256sum -c -
sudo install -m 0755 "${RUNNER_TEMP}/opam" /usr/local/bin/opam
test "$(opam --version)" = "${OPAM_VERSION}"
{
echo "LP_OPAM_VERSION=${OPAM_VERSION}"
echo "LP_OCAML_VERSION=${OCAML_VERSION}"
echo "OPAMROOT=${HOME}/.opam"
echo "OPAMCOLOR=always"
echo "OPAMCONFIRMLEVEL=unsafe-yes"
echo "OPAMDOWNLOADJOBS=$(nproc)"
echo "OPAMERRLOGLEN=0"
echo "OPAMEXTERNALSOLVER=builtin-0install"
echo "OPAMPRECISETRACKING=1"
echo "OPAMRETRIES=10"
echo "OPAMSOLVERTIMEOUT=600"
echo "OPAMYES=1"
echo "CLICOLOR_FORCE=1"
} >> "${GITHUB_ENV}"
""",
    "Compute the toolchain cache key": """
set -euo pipefail
h=$( { printf '%s\\n' "${PKGS}" "${REPOS}" "${SYSPKGS}"; \\
cat ./*.opam ./latex-parse/*.opam "${GITHUB_ACTION_PATH}/action.yml"; } \\
| sha256sum | cut -c1-16)
echo "key=lp-opam-v1-${ImageOS}-${RUNNER_ARCH}-opam${LP_OPAM_VERSION}-ocaml${LP_OCAML_VERSION}-${h}-$(date -u +%G-%V)" >> "${GITHUB_OUTPUT}"
""",
    "Initialise opam and the OCaml switch (cache miss)": """
ok=0
for attempt in 1 2; do
rm -rf "${OPAMROOT}" _opam
if opam init --bare --no-setup default https://opam.ocaml.org \\
&& opam switch create . --no-install --packages="ocaml-base-compiler.${LP_OCAML_VERSION}"; then
ok=1
break
fi
echo "::warning::[setup-ocaml-env] switch setup failed (attempt $attempt/2)"
sleep 15
done
if [ "$ok" -ne 1 ]; then
echo "::error::[setup-ocaml-env] opam init / switch create failed 2/2"
exit 1
fi
""",
}


def canon(text: str) -> list[str]:
    return [ln.strip() for ln in text.splitlines()
            if ln.strip() and not ln.strip().startswith("#")]


def all_steps(doc: dict):
    """(job id or None, step) for every step, plus job-level `uses:` jobs."""
    if isinstance(doc.get("runs"), dict):
        for st in doc["runs"].get("steps") or []:
            yield None, st
    for jid, job in (doc.get("jobs") or {}).items():
        if isinstance(job, dict):
            if "uses" in job:
                yield jid, {"uses": job["uses"], "with": job.get("with")}
            for st in job.get("steps") or []:
                yield jid, st


def cache_version_ok(ver: str) -> bool:
    m = VERSION_REF.match(ver)
    if not m:
        return False
    major, minor = int(m.group(1)), m.group(2)
    if major <= 2:
        return False
    if minor is None:              # bare major resolves to its newest release
        return True
    floor = {3: (3, 4), 4: (4, 2)}.get(major)
    return not (floor and (major, int(minor)) < floor)


def resolve_matrix(value: str, matrix) -> list[str] | None:
    """Literal values of a bare `${{ matrix.KEY }}`, else None (unresolvable)."""
    m = MATRIX_REF.match(value)
    if not (m and isinstance(matrix, dict)):
        return None
    vals = matrix.get(m.group(1))
    if not isinstance(vals, list):
        vals = [] if vals is None else None
    if vals is None:
        return None
    vals = list(vals)
    for inc in matrix.get("include") or []:
        if isinstance(inc, dict) and m.group(1) in inc:
            vals.append(inc[m.group(1)])
    if not vals or any(not isinstance(v, (str, int, float)) or EXPR.search(str(v))
                       for v in vals):
        return None
    return [str(v) for v in vals]


def uses_findings(doc: dict, text: str, rel: str, registry: dict) -> tuple[int, list[str]]:
    """Modes 6 and 8 over every `uses:` of one file, read THROUGH the YAML
    parse (aliases resolved, quoting undone), with each value's version
    comment looked up on the raw line that spells it."""
    out: list[str] = []
    if QUOTED_USES_KEY.search(text):
        out.append(f"UNSCANNED-USES: {rel} spells a `uses` key in quotes; write "
                   f"`uses:` plainly so its version comment can be read (C-200).")
    raw: dict[str, list[str | None]] = {}
    for m in RAW_USES.finditer(text):
        v = m.group("v").strip("'\"")
        raw.setdefault(v, []).append(m.group("c"))
    n = 0
    for jid, st in all_steps(doc):
        if not isinstance(st, dict) or "uses" not in st:
            continue
        n += 1
        full = st["uses"]
        if not isinstance(full, str):
            out.append(f"UNSCANNED-USES: {rel}: a `uses:` value {full!r} is not a string")
            continue
        if full not in raw:
            out.append(
                f"UNSCANNED-USES: {rel} has `uses: {full}` in its YAML but on no "
                f"line of the form `uses: VALUE` (an alias, a flow mapping or a "
                f"multi-line scalar); write it plainly (C-200).")
            continue
        comment = raw[full][0]
        if full.startswith("./"):
            continue
        if full.lower().startswith("docker://"):
            if not DIGEST_REF.match(full):
                out.append(f"FLOATING-TOOLCHAIN: {rel} uses `{full}`: a docker image "
                           f"must be pinned by `@sha256:<digest>` (C-200).")
            continue
        action, at, ref = full.partition("@")
        action_l = action.lower()
        repo_l = "/".join(action_l.split("/")[:2])
        if repo_l == "ocaml/setup-ocaml":
            out.append(
                f"FLOATING-TOOLCHAIN: {rel} uses `{full}`. Every setup-ocaml "
                f"release resolves opam to the newest upstream release at run "
                f"time (v2's bundled cache client also talks to the retired "
                f"cache service, C-176), whatever ref pins the action itself. "
                f"Use ./.github/actions/setup-ocaml-env, which pins opam (C-179).")
            continue
        if not at or not SHA_REF.match(ref):
            out.append(
                f"FLOATING-TOOLCHAIN: {rel} uses `{full}`: a third-party action "
                f"must be pinned by a 40-hex commit SHA with a `# <version>` "
                f"comment (tags and branches are mutable; run "
                f"scripts/tools/pin_actions.py --pin) (C-200).")
            continue
        recorded = registry.get(repo_l, {}).get(ref)
        if recorded is None:
            out.append(f"FLOATING-TOOLCHAIN: {rel} uses `{full}`, a SHA not recorded "
                       f"in {PIN_REGISTRY} (C-200).")
            continue
        if comment != recorded:
            out.append(f"FLOATING-TOOLCHAIN: {rel} uses `{full}` with comment "
                       f"`# {comment}`, but {PIN_REGISTRY} records that SHA as "
                       f"`{recorded}` (C-200).")
            continue
        if action_l.split("/")[:2] == ["actions", "cache"] and not cache_version_ok(recorded):
            out.append(
                f"LEGACY-CACHE: {rel} uses `{action}@{ref} # {recorded}`, which "
                f"talks to GitHub's retired legacy cache service: every restore "
                f"and save fails with only a WARNING, so the job stays green with "
                f"no cache (C-176). Use actions/cache >= v4.2.0 (or >= v3.4.0).")
        matrix = None
        if jid is not None:
            matrix = ((doc.get("jobs") or {}).get(jid, {}).get("strategy") or {}).get("matrix")
        for k, v in (st.get("with") or {}).items():
            if not VERSION_INPUT.match(str(k)):
                continue
            vals = [str(v)] if not EXPR.search(str(v)) else resolve_matrix(str(v).strip(), matrix)
            if vals is None:
                out.append(f"FLOATING-TOOLCHAIN: {rel}: `{action}` input `{k}: {v}` "
                           f"is an expression this gate cannot resolve (C-200).")
                continue
            for x in vals:
                if not EXACT_VERSION.match(x.strip()):
                    out.append(
                        f"FLOATING-TOOLCHAIN: {rel}: `{action}` input `{k}: {x}` "
                        f"is not an exact version (stable/nightly/latest, a bare "
                        f"major or a minor all resolve at run time) (C-200).")
    return n, out


def opam_findings(repo: Path, docs: dict[str, dict]) -> list[str]:
    """Mode 9: opam is installed only by setup-ocaml-env's pinned step, whose
    structure is exactly the canonical one."""
    out: list[str] = []
    key = str(OPAM_INSTALLER)
    doc = docs.get(key)
    if doc is None:
        return [f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} not found; nothing pins opam"]
    steps = {st.get("name"): st for st in (doc.get("runs") or {}).get("steps") or []
             if isinstance(st, dict)}
    for name, body in CANON.items():
        st = steps.get(name)
        if st is None:
            out.append(f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} has no step `{name}` (C-179)")
            continue
        if canon(str(st.get("run", ""))) != canon(body):
            out.append(
                f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} step `{name}` differs from "
                f"the canonical pinned text in check_workflow_triggers.py (exact "
                f"download URL, a checksum that fails the step before the binary "
                f"is touched, the switch built from LP_OCAML_VERSION); if the edit "
                f"is intended, update CANON there (C-179/C-200).")
    st = steps.get(OPAM_STEP)
    if st is not None:
        if str(st.get("if", "")).strip() != OPAM_STEP_IF:
            out.append(f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} step `{OPAM_STEP}` "
                       f"must be guarded by `if: {OPAM_STEP_IF}`")
        env = st.get("env") or {}
        if set(env) != set(OPAM_ENV) or any(not OPAM_ENV[k].match(str(env[k])) for k in OPAM_ENV if k in env):
            out.append(f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} step `{OPAM_STEP}` must "
                       f"set exactly {sorted(OPAM_ENV)}, each exact (an X.Y.Z "
                       f"version, a 64-hex sha256); found "
                       f"{ {k: str(v) for k, v in env.items()} } (C-179)")
    # The compiler/opam version is spelled ONCE (the opam step's env); any
    # other step value naming an X.Y.Z would be a second, unsynchronised copy.
    for st in (doc.get("runs") or {}).get("steps") or []:
        if not isinstance(st, dict):
            continue
        vals = [str(st.get("run", ""))] + [str(v) for v in (st.get("with") or {}).values()]
        if st.get("name") != OPAM_STEP:
            vals += [str(v) for v in (st.get("env") or {}).values()]
        for v in vals:
            for ln in v.splitlines():
                if re.search(r"\b\d+\.\d+\.\d+\b", strip_comment(ln)):
                    out.append(f"FLOATING-TOOLCHAIN: {OPAM_INSTALLER} step "
                               f"`{st.get('name')}` spells a version number "
                               f"(`{ln.strip()[:80]}`); derive it from OCAML_VERSION "
                               f"/ OPAM_VERSION (C-200)")
    for rel, d in docs.items():
        for label, run_text in iter_run_blocks(d, rel):
            if rel == key and label == f"{rel} :: {OPAM_STEP}":
                continue
            for ln in run_text.splitlines():
                if OPAM_ELSEWHERE.search(strip_comment(ln)):
                    out.append(f"FLOATING-TOOLCHAIN: {label} installs opam outside "
                               f"{OPAM_INSTALLER}'s pinned step: `{ln.strip()[:100]}` (C-200)")
    return out


def iter_runs_on(doc: dict):
    """(job id, label, resolved) for every runner label.

    Fail closed: a label that is an expression is resolved only when it is a
    bare `${{ matrix.KEY }}` over literal values (plus `include:` literals);
    anything else (matrix.cfg.os, inputs.os, fromJSON(...)) is yielded
    unresolved, and the caller refuses it.
    """
    for jid, job in (doc.get("jobs") or {}).items():
        if not isinstance(job, dict) or "runs-on" not in job:
            continue
        ro = job["runs-on"]
        if isinstance(ro, dict):
            ro = ro.get("labels", [])
            if not ro:
                yield jid, "<runs-on group with no labels>", False
                continue
        labels = ro if isinstance(ro, list) else [ro]
        matrix = (job.get("strategy") or {}).get("matrix")
        for lab in labels:
            lab = str(lab).strip()
            if not EXPR.search(lab):
                yield jid, lab, True
                continue
            vals = resolve_matrix(lab, matrix)
            if vals is None:
                yield jid, lab, False
                continue
            for v in vals:
                yield jid, v, True


PRUNE = {".git", "_build", "_opam", "node_modules", "target", ".claude", "__pycache__"}


def composite_actions(repo: Path) -> list[Path]:
    """Every action.yml / action.yaml in the repo (tracked files when git is
    available; otherwise a pruned walk), not only under .github/actions."""
    out = subprocess.run(["git", "-C", str(repo), "ls-files", "-z", "--",
                          "*action.yml", "*action.yaml"],
                         capture_output=True, text=True)
    if out.returncode == 0 and (repo / ".git").exists():
        names = [n for n in out.stdout.split("\0") if n]
        return sorted(repo / n for n in names
                      if Path(n).name in ("action.yml", "action.yaml"))
    found = []
    for root, dirs, files in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in PRUNE]
        for f in files:
            if f in ("action.yml", "action.yaml"):
                found.append(Path(root) / f)
    return sorted(found)


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

    workflows = sorted([*(repo / WORKFLOW_DIR).glob("*.yml"),
                        *(repo / WORKFLOW_DIR).glob("*.yaml")])
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
    scanned = list(workflows) + composite_actions(repo)
    reg_path = repo / PIN_REGISTRY
    try:
        registry = {k.lower(): v for k, v in json.loads(reg_path.read_text()).items()}
    except (OSError, ValueError) as exc:
        print(f"FAIL: {PIN_REGISTRY} unreadable ({exc}); every SHA pin would be "
              f"unverifiable", file=sys.stderr)
        return 1
    docs: dict[str, dict] = {}
    loops_checked = 0
    uses_checked = 0
    runners_checked = 0
    for path in scanned:
        rel = str(path.relative_to(repo))
        try:
            doc = yaml.safe_load(path.read_text()) or {}
        except yaml.YAMLError as exc:
            findings.append(f"{rel} is not valid YAML: {exc}")
            continue
        docs[rel] = doc
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
        n_uses, uf = uses_findings(doc, path.read_text(), rel, registry)
        uses_checked += n_uses
        findings.extend(uf)
        for jid, lab, resolved in iter_runs_on(doc):
            runners_checked += 1
            if not resolved:
                findings.append(
                    f"FLOATING-RUNNER: {rel} job '{jid}' runs on `{lab}`, an "
                    f"expression this gate cannot resolve to a fixed image; spell "
                    f"the label out, or use `${{{{ matrix.KEY }}}}` over literal "
                    f"values (C-177).")
            elif not FIXED_RUNNER.match(lab.lower()):
                findings.append(
                    f"FLOATING-RUNNER: {rel} job '{jid}' runs on `{lab}`, which is "
                    f"not a fixed image label (ubuntu-NN.NN[-arm], macos-NN[...], "
                    f"windows-NNNN; compared case-insensitively). `*-latest` and "
                    f"`ubuntu-slim` are re-pointed without a commit (ubuntu-latest "
                    f"became 26.04 from 2026-10-19) (C-177).")

    findings.extend(opam_findings(repo, docs))

    if not loops_checked:
        print("FAIL: scanned zero `run:` blocks -- the mode-4 scan is vacuous",
              file=sys.stderr)
        return 1
    # Floors for modes 6 and 7 (a stale walker would otherwise PASS on nothing).
    if uses_checked < 20 or runners_checked < 20:
        print(f"FAIL: scanned only {uses_checked} `uses:` ref(s) and "
              f"{runners_checked} runner label(s) -- the mode-6/7 scan is "
              f"probably vacuous (expected >= 20 of each)", file=sys.stderr)
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
          f"file(s) carry no unguarded retry loop and no drifted retry pair; "
          f"{uses_checked} `uses:` ref(s) are SHA-pinned and registered with no "
          f"legacy-cache client; {runners_checked} runner label(s) are fixed "
          f"images; opam comes only from the canonical pinned step")
    return 0


if __name__ == "__main__":
    sys.exit(main())
