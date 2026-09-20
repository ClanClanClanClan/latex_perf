#!/usr/bin/env python3
"""Shared staleness check for an artefact's `provenance.measured_at_sha`.

WHY THIS FILE EXISTS (OPEN-080, reopened; C-58).

Two required gates — `check_project_state.py` and
`check_apply_fixes_real_differential.py` — each carried their own copy of this
block:

    r = subprocess.run(["git", "rev-list", "--count", f"{sha}..HEAD",
                        "--", "latex-parse/src"], ...)
    if r.returncode == 0 and r.stdout.strip().isdigit():
        behind = int(r.stdout.strip())
        if behind > MAX_MEASUREMENT_LAG:
            findings.append(...)

There is no `else`. That single omission made BOTH ways of being blind read as
a pass, and both were live on main:

  * **Shallow clone.** `actions/checkout` defaults to `fetch-depth: 1`. As of
    2026-09-20 `grep -rn 'fetch-depth\\|fetch-tags' .github/workflows/` matched
    NOTHING across all 36 workflows, so every CI run got a one-commit clone in
    which `git rev-list <sha>..HEAD` exits 128 for any sha older than HEAD.
    Return code 128, no `else`, gate silently skips. The ratchet had never
    fired in CI — not once, on any PR.

  * **Non-ancestor sha.** A sha that git CAN resolve but that is not an
    ancestor of HEAD still yields a count, and the count is nonsense: it counts
    commits on HEAD's side that the other tip lacks. Five position artefacts
    stamped `52d850ef` — a pre-squash commit reachable only from two side
    branches — and the gate read "2 commits behind, limit 5" and passed. Had
    those branches been pruned, the sha would have become unresolvable and the
    gate would have gone right back to arm one: still green.

So the gate that exists to catch stale measurements could not distinguish
"fresh" from "I cannot see anything at all". That is the project's own named
defect shape — a gate nobody has seen fail is not a gate (process invariant 10)
— applied to the provenance of the published position itself.

This helper fails CLOSED and says WHICH kind of blindness it hit, so the
failure names its own remedy. Both arms are registered in
`check_gate_selftests.py`; per invariant 3 a gate is verified in both
directions or it is not verified.
"""

from __future__ import annotations

import subprocess

# A measurement more than this many commits behind HEAD on the engine source is
# presumed wrong. A commit count is only a proxy: `cli_sha256`, checked by the
# callers when a binary is present, is the fact.
MAX_MEASUREMENT_LAG = 5

WATCHED_PATH = "latex-parse/src"


def _git(repo, *args):
    return subprocess.run(
        ["git", "--no-optional-locks", *args],
        cwd=repo, capture_output=True, text=True)


def engine_tree_id(repo, rev="HEAD", path=WATCHED_PATH):
    """git's tree object id for the engine source at `rev`, or None.

    Platform-independent, content-exact, and free: git already stores it. This
    is the anchor `cli_sha256` cannot be (C-64) — a binary hash compares a
    macOS arm64 Mach-O against whatever CI's ubuntu-22.04 runner builds, so it
    can only ever be checked on the machine that produced the artefact.

    It is also SHARPER than the commit-distance proxy in the useful direction:
    the id is unchanged by any commit that does not touch `latex-parse/src`, so
    an artefact measured 40 commits ago whose engine source never moved is
    PROVABLY current rather than merely within a tolerance. The proxy can only
    bound staleness; this can establish freshness.

    Known blind spot, stated rather than hidden: it is taken from a COMMIT, so
    a measurement made against a dirty working tree records the committed tree
    and still looks clean. Catching that needs a content hash of the working
    files, which is a different and larger change.
    """
    r = _git(repo, "rev-parse", f"{rev}:{path}")
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else None


def check_measured_at_sha(repo, sha, label, howto,
                          limit=MAX_MEASUREMENT_LAG,
                          path=WATCHED_PATH,
                          src_tree_sha=None):
    """Return a list of findings about `sha`'s freshness. Empty means fresh.

    `label` names the artefact in the message; `howto` is the command that
    refreshes it. Every arm below returns a finding — there is no path through
    this function that is silent about a check it could not perform.
    """
    findings = []

    # Arm 1 — can this clone see the sha at all? A shallow checkout cannot, and
    # a gate that cannot see its own input must say so rather than pass.
    if _git(repo, "cat-file", "-e", f"{sha}^{{commit}}").returncode != 0:
        findings.append(
            f"{label} records measured_at_sha {sha[:12]}…, which cannot be "
            f"resolved in this clone. The staleness ratchet therefore checked "
            f"NOTHING. If this is CI, the checkout needs `fetch-depth: 0` — "
            f"actions/checkout defaults to a one-commit clone. If this is a "
            f"local run, the commit is gone: re-measure and re-stamp.\n"
            f"      {howto}")
        return findings

    # Arm 2 — is it on this history? A non-ancestor sha yields a meaningless
    # count rather than an error, which is how 52d850ef read as "2 behind".
    if _git(repo, "merge-base", "--is-ancestor", sha, "HEAD").returncode != 0:
        findings.append(
            f"{label} was measured at {sha[:12]}…, which is NOT an ancestor of "
            f"HEAD. The numbers it publishes were produced against a tree that "
            f"is not in this history, so the commit distance below it is "
            f"meaningless and the measurement is unreproducible. Re-measure on "
            f"a commit that is on this branch, or — if the content is identical "
            f"under a different sha (a squash) — re-stamp to that commit and "
            f"say so in provenance.measured_at_note.\n      {howto}")
        return findings

    # Arm 3 — if the artefact recorded the engine tree it was measured against
    # and that tree is still HEAD's, the measurement is CURRENT and the commit
    # distance is irrelevant: not one byte of `path` has changed since. This
    # can only ever turn a red green on evidence, never the reverse, and a
    # recorded id that DISAGREES falls through to the distance ratchet below
    # with the disagreement named.
    if src_tree_sha:
        head_tree = engine_tree_id(repo, "HEAD", path)
        if head_tree and src_tree_sha == head_tree:
            # Provably current: not one byte of `path` differs from HEAD, so
            # the commit distance cannot mean anything. Strict improvement —
            # this can only turn a red green ON EVIDENCE.
            return findings
        # ⚠ A mere DIFFERENCE is not a failure, and making it one was a defect
        # in the first version of this arm. The engine is supposed to change;
        # C-13 set MAX_MEASUREMENT_LAG deliberately above 0 precisely because
        # failing on every source edit trains people to refresh without
        # reading. Ordinary drift therefore falls through to the ratchet below,
        # unchanged.
        #
        # What IS a failure is an INCOHERENT claim: a recorded tree id that is
        # not an object in this repository at all. That artefact asserts an
        # engine state which has never existed here, so nothing about it can be
        # trusted — including the measurement it carries.
        # ⚠ ORDERING IS LOAD-BEARING. This existence test would give a FALSE
        # failure in a shallow clone, where an older tree object simply has
        # not been fetched. It is safe only because Arm 1 above already
        # returned on an unresolvable measured_at_sha, which is exactly what
        # a shallow clone produces. Do not reorder these arms, and do not
        # remove `fetch-depth: 0` from the workflows that run them.
        if _git(repo, "cat-file", "-e", f"{src_tree_sha}^{{tree}}").returncode != 0:
            findings.append(
                f"{label} records src_tree_sha {src_tree_sha[:12]}…, which is "
                f"not a tree object in this repository. The artefact claims an "
                f"engine source state that has never existed on this branch, so "
                f"its provenance is incoherent — re-measure rather than "
                f"re-stamp.\n      {howto}")
            return findings

    # Arm 4 — the distance. Unreachable failures are still reported.
    r = _git(repo, "rev-list", "--count", f"{sha}..HEAD", "--", path)
    if r.returncode != 0 or not r.stdout.strip().isdigit():
        findings.append(
            f"{label}: `git rev-list --count {sha[:12]}…..HEAD -- {path}` "
            f"failed (rc {r.returncode}): {(r.stderr or '').strip()[:200]}. "
            f"The ratchet could not run; treating that as a pass is how this "
            f"gate spent its whole life green (C-58).")
        return findings

    behind = int(r.stdout.strip())
    if behind > limit:
        findings.append(
            f"{label} is {behind} commits behind HEAD on {path} (limit "
            f"{limit}). The number it publishes is probably wrong. Refresh:\n"
            f"      {howto}")
    return findings
