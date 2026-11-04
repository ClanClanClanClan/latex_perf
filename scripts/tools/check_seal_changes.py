#!/usr/bin/env python3
"""The seals' anchor OUTSIDE the code it protects (review 3 of the P2
baseline, M4).

_sample_seal.SEAL_PINS pins each sealed set's ids, but a commit that edits
both a manifest and its pin passes every check inside _sample_seal. This
gate compares the SEAL STATE at HEAD with the state at the merge-base with
the main branch:

  * SEAL_PINS, read from scripts/tools/_sample_seal.py at each revision (by
    parsing it, never importing it);
  * the id-set digest (_sample_seal.seal_digest: offset, n, sorted ids) of
    every seal manifest at each revision (a re-grade that rewrites only a
    manifest's oracle block is no change);
  * the labeller allow-list corpora/p2_baseline/cause_labels/labellers.json.

Any difference FAILS unless a commit in merge-base..HEAD that is a
descendant of (or equal to) the newest commit touching those paths carries
the trailer

    Seal-Change-Approved-By: <owner>

which REQUIRES THE OWNER'S SIGN-OFF (pre-registration §2.3). The trailer is
text in a commit message: the gate proves that an approval was recorded
after the last change, not who wrote it -- that residual trust, and the
CODEOWNERS entry that makes GitHub request the owner's review for these
paths, are stated in the pre-registration.

  check_seal_changes.py [--repo .] [--base REV]   (default base: merge-base
                                                   of HEAD and origin/main)
Exit 0 no change or approved; 1 unapproved change; 2 a precondition.
"""
from __future__ import annotations

import argparse
import ast
import json
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import _sample_seal as seal  # noqa: E402

SEAL_CODE = "scripts/tools/_sample_seal.py"
MANIFESTS = ((seal.SEALED_MANIFEST, seal.SEALED_OFFSET, seal.SEALED_N),
             (seal.HELDOUT_MANIFEST, seal.HELDOUT_OFFSET, seal.HELDOUT_N))
LABELLERS = "corpora/p2_baseline/cause_labels/labellers.json"
PATHS = (SEAL_CODE, *(m for m, _, _ in MANIFESTS), LABELLERS)
TRAILER = "Seal-Change-Approved-By:"


def git(repo, *a) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "--no-optional-locks", *a], cwd=repo, capture_output=True)


def show(repo, rev, path) -> bytes | None:
    r = git(repo, "show", f"{rev}:{path}")
    return r.stdout if r.returncode == 0 else None


def pins_at(repo, rev) -> dict | None:
    """SEAL_PINS as the source at `rev` assigns it (a dict of literal
    strings); None when the file or the assignment is absent; {"<unparsed>"}
    when it is not a literal the gate can read (a change, by construction)."""
    src = show(repo, rev, SEAL_CODE)
    if src is None:
        return None
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return {"<unparsed>": "syntax"}
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "SEAL_PINS"
                                                for t in node.targets):
            out = {}
            if not isinstance(node.value, ast.Dict):
                return {"<unparsed>": "not a dict"}
            for k, v in zip(node.value.keys, node.value.values):
                key = (k.id if isinstance(k, ast.Name) else
                       k.value if isinstance(k, ast.Constant) else ast.dump(k))
                val = v.value if isinstance(v, ast.Constant) else ast.dump(v)
                out[str(key)] = str(val)
            return out
    return None


def state_at(repo, rev) -> dict:
    st = {"pins": pins_at(repo, rev), "manifests": {}, "labellers": None}
    for rel, off, n in MANIFESTS:
        data = show(repo, rev, rel)
        if data is None:
            st["manifests"][rel] = None
            continue
        try:
            ids = [r["arxiv_id"] for r in json.loads(data)["docs"]]
            st["manifests"][rel] = seal.seal_digest(off, n, ids)
        except Exception:  # noqa: BLE001 -- an unreadable manifest is a state of its own
            st["manifests"][rel] = "<unreadable>"
    lab = show(repo, rev, LABELLERS)
    st["labellers"] = None if lab is None else lab.decode("utf-8", "replace")
    return st


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=".")
    ap.add_argument("--base", default=None)
    ns = ap.parse_args(argv)
    repo = Path(ns.repo)
    base = ns.base
    if base is None:
        r = git(repo, "merge-base", "HEAD", "origin/main")
        if r.returncode != 0:
            print("[seal-changes] FAIL: no merge-base with origin/main (fetch it; a gate that "
                  "cannot compare is not a pass)")
            return 2
        base = r.stdout.decode().strip()
    before, after = state_at(repo, base), state_at(repo, "HEAD")
    changed = [k for k in ("pins", "manifests", "labellers") if before[k] != after[k]]
    if not changed:
        print(f"[seal-changes] PASS: the seal state at HEAD equals {base[:10]}'s "
              f"({len(MANIFESTS)} manifests, pins, labeller allow-list)")
        return 0
    touching = git(repo, "log", "--format=%H", f"{base}..HEAD", "--", *PATHS).stdout.decode().split()
    newest = touching[0] if touching else None
    approvals = []
    for sha in git(repo, "log", "--format=%H", f"{base}..HEAD").stdout.decode().split():
        msg = git(repo, "log", "-1", "--format=%B", sha).stdout.decode()
        if any(line.startswith(TRAILER) and line[len(TRAILER):].strip()
               for line in msg.splitlines()):
            if newest is None or git(repo, "merge-base", "--is-ancestor", newest,
                                     sha).returncode == 0:
                approvals.append(sha)
    if approvals:
        print(f"[seal-changes] PASS (APPROVED): the seal state changed ({', '.join(changed)}) "
              f"since {base[:10]}; approved by the trailer on {approvals[0][:10]}, after the "
              f"last change {newest[:10] if newest else '-'}")
        return 0
    print(f"[seal-changes] FAIL: the seal state changed ({', '.join(changed)}) since "
          f"{base[:10]} ({len(touching)} commit(s) touch the seal paths) and no commit after the "
          f"last change carries '{TRAILER} <owner>'. A seal change requires the owner's "
          f"sign-off (pre-registration §2.3).")
    return 1


if __name__ == "__main__":
    sys.exit(main())
