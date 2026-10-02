#!/usr/bin/env python3
"""check_release_debt.py — ADR-011 §6: fail when main runs too far past a release.

WHY THIS EXISTS. OPEN-013: between v27.1.62 and v27.1.63 main ran 102 commits
and 47 days past the last tag with every required context green, and for that
whole window the only installable artefact still carried a fixer measured at a
63.3% break rate, because every accuracy fix lived only on main. Release debt
is the window in which users run a version already known to be wrong, and
nothing watched it.

WHAT IT MEASURES, AT RUN TIME, FROM GIT ONLY.
  T    = git describe --tags --abbrev=0 --match 'v[0-9]*' HEAD
         (the nearest release tag reachable from HEAD; must read vX.Y.Z)
  debt = git rev-list --first-parent --count T..HEAD
         (FIRST-PARENT commits: on main, one per merged PR or direct push,
         whichever merge style the owner used — a squash and a true merge
         both add exactly one first-parent commit)
  The all-commit count `git rev-list --count T..HEAD` is printed for
  information only; it is never compared with anything.

RULE (owner decision 2026-10-02, amending ADR-011 §6 to first-parent units):
  * dune-project's (version) at HEAD GREATER than T's version: PASS, with a
    note. A release is being prepared; the release PR itself must be able to
    land while main is in debt.
  * dune-project's version LOWER than T's: FAIL. The tree claims to be older
    than a release already cut from its own history.
  * otherwise FAIL when debt > MAX_FIRST_PARENT_DEBT, else PASS.

NO COMMITTED NUMBERS (C-13). The debt figure changes on every commit; it was
once in gen_project_state's generated block and broke that gate on the very
next commit. This gate computes it from git each run and compares it with the
one constant below, nothing else.

FAILS CLOSED (C-55 / OPEN-101). A shallow clone, no reachable release tag
(tags not fetched), an unparseable tag or version, or ANY git error is exit 2
— never a pass. A `rev-list` exit 128 read as green is exactly how two
staleness ratchets in this repo were blind in CI for their whole lives.

Exit: 0 pass (including the exemption), 1 debt or version failure, 2 infra.

`--selftest-fixture PATH` builds a throwaway git repository described by a
JSON file, clones it the way the file says, and runs the SAME `evaluate` on
the clone. It exists so check_gate_selftests.py can prove each arm fails by
mutating that JSON; it is never used by CI's real run.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# ADR-011 §6, amended by the owner 2026-10-02: first-parent commits, N = 25.
# This is the ONLY place the threshold lives. Change it here, with an ADR.
MAX_FIRST_PARENT_DEBT = 25

TAG_GLOB = "v[0-9]*"
TAG_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
DUNE_VERSION_RE = re.compile(r"^\(version\s+(\d+)\.(\d+)\.(\d+)\)\s*$", re.M)


class Infra(Exception):
    """The gate could not establish a trustworthy measurement (exit 2)."""


def git(repo: Path, *args: str) -> str:
    try:
        r = subprocess.run(["git", "-C", str(repo), *args],
                           capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Infra(f"git {' '.join(args)}: {exc}") from exc
    if r.returncode != 0:
        raise Infra(f"git {' '.join(args)} exited {r.returncode}: "
                    f"{(r.stderr or r.stdout).strip()[:300]}")
    return r.stdout.strip()


def count(repo: Path, *args: str) -> int:
    out = git(repo, "rev-list", "--count", *args)
    if not out.isdigit():
        raise Infra(f"git rev-list --count {' '.join(args)} printed {out!r}, "
                    f"not a count")
    return int(out)


def evaluate(repo: Path, limit: int) -> tuple[int, list[str]]:
    """(exit code, report lines). Raises Infra for anything untrustworthy."""
    if git(repo, "rev-parse", "--is-shallow-repository") != "false":
        raise Infra("shallow clone: the distance to the last release tag "
                    "cannot be measured (CI must check out with "
                    "fetch-depth: 0)")
    try:
        tag = git(repo, "describe", "--tags", "--abbrev=0",
                  "--match", TAG_GLOB, "HEAD")
    except Infra as exc:
        raise Infra(f"no tag matching '{TAG_GLOB}' is reachable from HEAD — "
                    f"tags not fetched, or never released ({exc})") from exc
    m = TAG_RE.match(tag)
    if not m:
        raise Infra(f"nearest release tag {tag!r} is not of the form vX.Y.Z")
    tag_ver = tuple(int(x) for x in m.groups())

    dune = git(repo, "show", "HEAD:dune-project")
    vs = DUNE_VERSION_RE.findall(dune)
    if len(vs) != 1:
        raise Infra(f"dune-project at HEAD has {len(vs)} '(version X.Y.Z)' "
                    f"lines (need exactly 1)")
    dune_ver = tuple(int(x) for x in vs[0])

    rng = f"{tag}..HEAD"
    fp = count(repo, "--first-parent", rng)
    allc = count(repo, rng)
    dv = ".".join(map(str, dune_ver))
    head = git(repo, "rev-parse", "--short", "HEAD")
    lines = [f"HEAD {head}: {fp} first-parent commit(s) past {tag} "
             f"({allc} commit(s) in all); dune-project version {dv}; "
             f"limit {limit} (ADR-011 §6)"]

    if dune_ver > tag_ver:
        lines.append(f"PASS (exempt): dune-project {dv} is newer than {tag} "
                     f"— a release is being prepared; tag it once it merges")
        return 0, lines
    if dune_ver < tag_ver:
        lines.append(f"FAIL: dune-project version {dv} is BEHIND the release "
                     f"tag {tag} reachable from HEAD — the tree claims to be "
                     f"older than a release cut from its own history")
        return 1, lines
    if fp > limit:
        lines.append(f"FAIL: release debt is {fp} first-parent commit(s) past "
                     f"{tag}, limit {limit} — cut a release (ADR-011 §6). "
                     f"Merged work is not installable until it is tagged.")
        return 1, lines
    lines.append(f"PASS: {fp} <= {limit}")
    return 0, lines


# ── fixture mode (for check_gate_selftests.py only) ─────────────────────────

FIXTURE_ENV = {
    "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_AUTHOR_NAME": "fixture", "GIT_AUTHOR_EMAIL": "fixture@invalid",
    "GIT_COMMITTER_NAME": "fixture", "GIT_COMMITTER_EMAIL": "fixture@invalid",
    "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z",
    "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z",
}


def _fx(cwd: Path, *args: str) -> None:
    env = {**os.environ, **FIXTURE_ENV}
    r = subprocess.run(["git", "-c", "init.defaultBranch=main",
                        "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false",
                        *args], cwd=cwd, env=env, capture_output=True,
                       text=True, timeout=60)
    if r.returncode != 0:
        raise Infra(f"fixture build: git {' '.join(args)} exited "
                    f"{r.returncode}: {r.stderr.strip()[:300]}")


def build_fixture(spec: dict, root: Path) -> Path:
    """origin: a tagged release commit, then `side_commits` commits on a
    branch merged with --no-ff (ONE first-parent commit, side_commits + 1 in
    all), then `direct_commits` commits straight on main. Cloned per
    spec["clone"]: "full" | "no-tags" | "shallow"."""
    src = root / "origin"
    src.mkdir()
    _fx(src, "init", "-q")
    (src / "dune-project").write_text(
        f"(lang dune 3.0)\n(version {spec['dune_version_at_tag']})\n")
    _fx(src, "add", "dune-project")
    _fx(src, "commit", "-q", "-m", "release")
    _fx(src, "tag", "-a", spec["tag"], "-m", spec["tag"])
    _fx(src, "checkout", "-q", "-b", "side")
    for i in range(spec["side_commits"]):
        (src / f"side{i}").write_text(f"{i}\n")
        _fx(src, "add", f"side{i}")
        _fx(src, "commit", "-q", "-m", f"side {i}")
    _fx(src, "checkout", "-q", "main")
    _fx(src, "merge", "-q", "--no-ff", "-m", "merge side", "side")
    for i in range(spec["direct_commits"]):
        (src / f"direct{i}").write_text(f"{i}\n")
        _fx(src, "add", f"direct{i}")
        _fx(src, "commit", "-q", "-m", f"direct {i}")
    if spec["dune_version_at_head"] != spec["dune_version_at_tag"]:
        (src / "dune-project").write_text(
            f"(lang dune 3.0)\n(version {spec['dune_version_at_head']})\n")
        _fx(src, "commit", "-q", "-am", "bump")
    dst = root / "clone"
    mode = spec["clone"]
    if mode == "full":
        _fx(root, "clone", "-q", str(src), str(dst))
    elif mode == "no-tags":
        _fx(root, "clone", "-q", "--no-tags", str(src), str(dst))
    elif mode == "shallow":
        _fx(root, "clone", "-q", "--depth", "1", src.as_uri(), str(dst))
    else:
        raise Infra(f"fixture: unknown clone mode {mode!r}")
    return dst


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=".")
    ap.add_argument("--max", type=int, default=MAX_FIRST_PARENT_DEBT,
                    help=f"first-parent commits allowed past the last release "
                         f"tag (default {MAX_FIRST_PARENT_DEBT}, ADR-011 §6)")
    ap.add_argument("--selftest-fixture", metavar="JSON",
                    help="evaluate a throwaway repo built from this spec "
                         "(kill-tests only)")
    ns = ap.parse_args()
    if ns.max < 0:
        ap.error("--max must be >= 0")
    try:
        if ns.selftest_fixture:
            spec = json.loads(Path(ns.selftest_fixture).read_text())
            limit = spec["max"]
            with tempfile.TemporaryDirectory(prefix="release-debt-") as td:
                rc, lines = evaluate(build_fixture(spec, Path(td)), limit)
        else:
            rc, lines = evaluate(Path(ns.repo), ns.max)
    except Infra as exc:
        print(f"[release-debt] INFRA (exit 2, never a pass): {exc}")
        return 2
    for ln in lines:
        print(f"[release-debt] {ln}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
