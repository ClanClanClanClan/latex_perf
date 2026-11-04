#!/usr/bin/env python3
"""Pin every third-party GitHub Action to a commit SHA (C-200).

Tags and branches are mutable: `@v4` today is not `@v4` next month, and a
branch named `1.99` is not a release. check_workflow_triggers.py failure mode
8 therefore accepts a third-party `uses:` only as `owner/repo[/path]@<40-hex>
# vX.Y.Z`, with that SHA -> version pair present in .github/action-pins.json.
That registry is the trust root the gate checks comments against; this tool is
the only intended writer, and `--verify` re-derives every entry from GitHub.

  pin_actions.py --pin             rewrite tag/branch refs to SHA + comment,
                                   and record them (network)
  pin_actions.py --set A@TAG       pin action A (owner/repo[/path]) to TAG
                                   everywhere it is used (network)
  pin_actions.py --verify          every registry entry: does tag `version`
                                   still resolve to that SHA? (network)

Needs `gh` authenticated.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
REGISTRY = REPO / ".github" / "action-pins.json"
USES = re.compile(r"^(?P<pre>[ \t]*(?:-[ \t]*)?uses:[ \t]*)(?P<ref>[^\s#'\"]+)"
                  r"(?P<post>[ \t]*(?:#.*)?)$", re.M)
SHA = re.compile(r"^[0-9a-f]{40}$")
EXACT = re.compile(r"^v?\d+\.\d+\.\d+$")


def gh(path: str) -> object:
    out = subprocess.run(["gh", "api", path], capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit(f"gh api {path} failed: {out.stderr.strip()}")
    return json.loads(out.stdout)


def files() -> list[Path]:
    gh_dir = REPO / ".github"
    return sorted([*gh_dir.rglob("*.yml"), *gh_dir.rglob("*.yaml")])


def repo_of(action: str) -> str:
    return "/".join(action.split("/")[:2]).lower()


def tag_commit(repo: str, tag: str) -> str | None:
    out = subprocess.run(["gh", "api", f"repos/{repo}/git/ref/tags/{tag}"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return None
    obj = json.loads(out.stdout)["object"]
    while obj["type"] == "tag":
        obj = gh(f"repos/{repo}/git/tags/{obj['sha']}")["object"]
    return obj["sha"]


def exact_version(repo: str, sha: str, tag: str) -> str:
    """The most specific vX.Y.Z tag on `sha` (the tag itself if exact)."""
    if EXACT.match(tag):
        return tag
    best = None
    page = 1
    while page < 20:
        tags = gh(f"repos/{repo}/tags?per_page=100&page={page}")
        if not tags:
            break
        for t in tags:
            if t["commit"]["sha"] == sha and EXACT.match(t["name"]):
                if best is None or len(t["name"]) > len(best):
                    best = t["name"]
        page += 1
    return best if best is not None else tag   # no exact tag: keep the tag name


def load() -> dict:
    return json.loads(REGISTRY.read_text()) if REGISTRY.is_file() else {}


def save(reg: dict) -> None:
    REGISTRY.write_text(json.dumps(
        {k: dict(sorted(v.items())) for k, v in sorted(reg.items())},
        indent=2) + "\n")


def rewrite(want: dict[str, str] | None) -> int:
    """want: action -> tag to force; None = pin every non-SHA ref as is."""
    reg = load()
    cache: dict[tuple[str, str], tuple[str, str]] = {}
    changed = 0
    pending: dict[Path, str] = {}
    for f in files():
        text = f.read_text()

        def sub(m: re.Match) -> str:
            nonlocal changed
            ref = m.group("ref")
            if ref.startswith("./") or ref.startswith("docker://") or "@" not in ref:
                return m.group(0)
            action, _, cur = ref.partition("@")
            tag = (want or {}).get(action)
            if want is not None and tag is None:
                return m.group(0)
            if want is None:
                if SHA.match(cur):
                    # an existing SHA pin with no registry entry: an untagged
                    # commit (e.g. dtolnay/rust-toolchain, which has none)
                    if cur not in reg.get(repo_of(action), {}):
                        reg.setdefault(repo_of(action), {})[cur] = "untagged"
                        changed += 1
                        return f"{m.group('pre')}{action}@{cur} # untagged"
                    return m.group(0)
                tag = cur
            repo = repo_of(action)
            if (repo, tag) not in cache:
                sha = tag_commit(repo, tag)
                if sha is None:
                    raise SystemExit(f"{f.relative_to(REPO)}: {action}@{tag} is not a tag")
                cache[(repo, tag)] = (sha, exact_version(repo, sha, tag))
            sha, ver = cache[(repo, tag)]
            reg.setdefault(repo, {})[sha] = ver
            changed += 1
            return f"{m.group('pre')}{action}@{sha} # {ver}"

        new = USES.sub(sub, text)
        if new != text:
            pending[f] = new
    # Write only after EVERY ref resolved: a failure above (SystemExit) must
    # leave the tree untouched, or a rerun would record half-pinned refs.
    for f, new in pending.items():
        f.write_text(new)
    # drop registry entries no file uses any more
    used = set()
    for f in files():
        for m in USES.finditer(f.read_text()):
            a, _, r = m.group("ref").partition("@")
            if SHA.match(r):
                used.add((repo_of(a), r))
    reg = {k: {s: v for s, v in d.items() if (k, s) in used} for k, d in reg.items()}
    save({k: d for k, d in reg.items() if d})
    print(f"[pin-actions] rewrote {changed} uses: line(s); registry holds "
          f"{sum(len(d) for d in load().values())} pin(s)")
    return 0


def verify() -> int:
    reg = load()
    bad = 0
    n = 0
    for repo, pins in reg.items():
        for sha, ver in pins.items():
            n += 1
            if ver == "untagged":
                ok = subprocess.run(["gh", "api", f"repos/{repo}/commits/{sha}", "-q", ".sha"],
                                    capture_output=True, text=True).stdout.strip() == sha
                if not ok:
                    print(f"MISSING {repo}: untagged commit {sha} not found")
                    bad += 1
                continue
            got = tag_commit(repo, ver)
            if got != sha:
                print(f"MISMATCH {repo}: registry {sha} = {ver}, but tag {ver} -> {got}")
                bad += 1
    if n == 0:
        print("FAIL: empty registry")
        return 1
    print(f"[pin-actions] verify: {n - bad}/{n} pin(s) match their tags")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--pin", action="store_true")
    g.add_argument("--set", action="append", metavar="ACTION@TAG")
    g.add_argument("--verify", action="store_true")
    ns = ap.parse_args()
    if ns.verify:
        return verify()
    if ns.set:
        return rewrite(dict(s.split("@", 1) for s in ns.set))
    return rewrite(None)


if __name__ == "__main__":
    sys.exit(main())
