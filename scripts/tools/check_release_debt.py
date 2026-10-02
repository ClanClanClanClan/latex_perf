#!/usr/bin/env python3
"""check_release_debt.py — ADR-011 §6: fail when main runs too far past a release.

WHY THIS EXISTS. OPEN-013: between v27.1.62 and v27.1.63 main ran 102 commits
and 47 days past the last tag with every required context green, and for that
whole window the only installable artefact still carried a fixer measured at a
63.3% break rate, because every accuracy fix lived only on main. Release debt
is the window in which users run a version already known to be wrong, and
nothing watched it.

WHAT IT MEASURES, AT RUN TIME, FROM GIT ONLY.
  T    = the HIGHEST release tag reachable from HEAD: among
         `git tag --merged HEAD`, the names of the exact form vX.Y.Z
         (no leading zeros, nothing after Z), ordered as version tuples.
         Every other tag (v26.2.0-alpha1, v25-R0-...-ground-truth, a spike
         tag) is NOT a release and is ignored, so it can neither choose T nor
         turn CI red. NOT `git describe`: describe picks the tag with the
         fewest commits to HEAD across ALL parents, so an older hotfix tag on
         a merged side branch beats the real latest release on main — and
         the exemption below then passed any amount of debt (C-116).
  debt = git rev-list --first-parent --count T..HEAD
         (FIRST-PARENT commits: on main, one per merged PR or direct push,
         whichever merge style the owner used — a squash and a true merge
         both add exactly one first-parent commit)
  The all-commit count `git rev-list --count T..HEAD` is printed for
  information only; it is never compared with anything.

THE LIMIT. MAX_FIRST_PARENT_DEBT below is the only constant. Because the
owner's decision lives in ADR-011 §6's amendment, the gate reads the N stated
in that amendment's Decision paragraph on every run and exits 2 if it differs
from the constant (or cannot be found exactly once): raising the limit in code
without an ADR edit cannot pass.

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
(tags not fetched), an unparseable dune-project version, an ADR/constant
mismatch, or ANY git error is exit 2 — never a pass. A `rev-list` exit 128 read as green is exactly how two
staleness ratchets in this repo were blind in CI for their whole lives.

Exit: 0 pass (including the exemption), 1 debt or version failure, 2 infra.

`--selftest-fixture PATH` builds one throwaway git repository per case of a
JSON file (each a list of ops: version bumps, commits, tags, branches,
--no-ff merges), clones it the way the case says, and runs the SAME
`evaluate` on the clone; the exit code is the worst over the cases. It exists so check_gate_selftests.py can prove each arm fails by
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

_NUM = r"(0|[1-9][0-9]*)"
TAG_RE = re.compile(rf"\Av{_NUM}\.{_NUM}\.{_NUM}\Z")
ADR_011 = "docs/v27/adr/ADR-011-fund-track-R-and-demote-apply-fixes.md"
ADR_N_RE = re.compile(r"\*\*Decision\.\*\* N = (\d+) counts \*\*first-parent\*\*")
REPO_ROOT = Path(__file__).resolve().parents[2]
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


def check_adr_limit(root: Path = REPO_ROOT) -> None:
    """The constant must equal the N the owner's ADR-011 §6 amendment states."""
    try:
        text = (root / ADR_011).read_text(encoding="utf-8")
    except OSError as exc:
        raise Infra(f"cannot read {ADR_011} to confirm the limit: {exc}") from exc
    ns = ADR_N_RE.findall(text)
    if len(ns) != 1:
        raise Infra(f"{ADR_011} states the first-parent N {len(ns)}x "
                    f"(need exactly 1 '**Decision.** N = <n> counts "
                    f"**first-parent**')")
    if int(ns[0]) != MAX_FIRST_PARENT_DEBT:
        raise Infra(f"ADR-011 §6 states N = {ns[0]} but MAX_FIRST_PARENT_DEBT "
                    f"is {MAX_FIRST_PARENT_DEBT} — the limit is the owner's "
                    f"decision; change both or neither")


def latest_release_tag(repo: Path) -> tuple[str, tuple[int, int, int]]:
    """The highest vX.Y.Z tag reachable from HEAD (see the module doc)."""
    names = git(repo, "tag", "--merged", "HEAD").splitlines()
    rel = []
    for name in names:
        m = TAG_RE.match(name)
        if m:
            rel.append((tuple(int(x) for x in m.groups()), name))
    if not rel:
        raise Infra(f"no release tag (vX.Y.Z) is reachable from HEAD among "
                    f"{len(names)} reachable tag(s) — tags not fetched, or "
                    f"never released")
    ver, name = max(rel)
    return name, ver


def evaluate(repo: Path, limit: int) -> tuple[int, list[str]]:
    """(exit code, report lines). Raises Infra for anything untrustworthy."""
    if git(repo, "rev-parse", "--is-shallow-repository") != "false":
        raise Infra("shallow clone: the distance to the last release tag "
                    "cannot be measured (CI must check out with "
                    "fetch-depth: 0)")
    tag, tag_ver = latest_release_tag(repo)

    dune = git(repo, "show", "HEAD:dune-project")
    vs = DUNE_VERSION_RE.findall(dune)
    if len(vs) != 1:
        raise Infra(f"dune-project at HEAD has {len(vs)} '(version X.Y.Z)' "
                    f"lines (need exactly 1)")
    dune_ver = tuple(int(x) for x in vs[0])

    rng = f"refs/tags/{tag}..HEAD"
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


def _fx(cwd: Path, *args: str, date: str | None = None) -> None:
    env = {**os.environ, **FIXTURE_ENV}
    if date:
        env["GIT_AUTHOR_DATE"] = env["GIT_COMMITTER_DATE"] = date
    r = subprocess.run(["git", "-c", "init.defaultBranch=main",
                        "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false",
                        *args], cwd=cwd, env=env, capture_output=True,
                       text=True, timeout=60)
    if r.returncode != 0:
        raise Infra(f"fixture build: git {' '.join(args)} exited "
                    f"{r.returncode}: {r.stderr.strip()[:300]}")


def build_fixture(case: dict, root: Path) -> Path:
    """Replay case["ops"] in a fresh repo on branch main, then clone it per
    case["clone"]: "full" | "no-tags" | "shallow". Ops:
      {"op": "version", "v": "1.0.0"}   write dune-project, commit
      {"op": "commits", "n": k}         k one-file commits
      {"op": "tag", "name": ..., "annotated": bool, "date": optional ISO}
      {"op": "branch", "name": ...}     git checkout -b
      {"op": "checkout", "name": ...}
      {"op": "merge", "name": ...}      git merge --no-ff (ONE first-parent
                                        commit, however many it brings in)
    """
    src = root / "origin"
    src.mkdir()
    _fx(src, "init", "-q")
    seq = 0
    for op in case["ops"]:
        kind = op["op"]
        if kind == "version":
            (src / "dune-project").write_text(
                f"(lang dune 3.0)\n(version {op['v']})\n")
            _fx(src, "add", "dune-project")
            _fx(src, "commit", "-q", "-m", f"version {op['v']}")
        elif kind == "commits":
            for _ in range(op["n"]):
                seq += 1
                (src / f"f{seq}").write_text(f"{seq}\n")
                _fx(src, "add", f"f{seq}")
                _fx(src, "commit", "-q", "-m", f"commit {seq}")
        elif kind == "tag":
            if op.get("annotated", True):
                _fx(src, "tag", "-a", op["name"], "-m", op["name"],
                    date=op.get("date"))
            else:
                _fx(src, "tag", op["name"])
        elif kind == "branch":
            _fx(src, "checkout", "-q", "-b", op["name"])
        elif kind == "checkout":
            _fx(src, "checkout", "-q", op["name"])
        elif kind == "merge":
            _fx(src, "merge", "-q", "--no-ff", "-m", f"merge {op['name']}",
                op["name"])
        else:
            raise Infra(f"fixture: unknown op {kind!r}")
    dst = root / "clone"
    mode = case["clone"]
    if mode == "full":
        _fx(root, "clone", "-q", str(src), str(dst))
    elif mode == "no-tags":
        _fx(root, "clone", "-q", "--no-tags", str(src), str(dst))
    elif mode == "shallow":
        _fx(root, "clone", "-q", "--depth", "1", src.as_uri(), str(dst))
    else:
        raise Infra(f"fixture: unknown clone mode {mode!r}")
    return dst


def run_fixture(path: Path) -> int:
    """Every case of the fixture; the exit code is the worst one (2 > 1 > 0)."""
    cases = json.loads(path.read_text())["cases"]
    worst = 0
    for case in cases:
        tagname = f"[release-debt] [{case['name']}]"
        try:
            with tempfile.TemporaryDirectory(prefix="release-debt-") as td:
                rc, lines = evaluate(build_fixture(case, Path(td)),
                                     case["max"])
        except Infra as exc:
            print(f"{tagname} INFRA (exit 2, never a pass): {exc}")
            worst = 2
            continue
        for ln in lines:
            print(f"{tagname} {ln}")
        worst = max(worst, rc)
    return worst


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
        check_adr_limit()
        if ns.selftest_fixture:
            return run_fixture(Path(ns.selftest_fixture))
        rc, lines = evaluate(Path(ns.repo), ns.max)
    except Infra as exc:
        print(f"[release-debt] INFRA (exit 2, never a pass): {exc}")
        return 2
    for ln in lines:
        print(f"[release-debt] {ln}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
