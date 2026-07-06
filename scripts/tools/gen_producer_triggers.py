#!/usr/bin/env python3
"""Regenerate the golden fixpoints in specs/v27/producer_triggers.json.

The registry maps each producer to a SET of adversarial variants, each with a
trigger (hex), a mode (pilot), a kind (mutate/preserve) and the expected fixpoint
output (expected_hex). This keeps the triggers as-is and re-derives expected_hex
from the CURRENT binary (iterating --apply-fixes-for to a fixpoint, matching
check_producer_coverage.py), so after an INTENTIONAL producer change you run this
and review the golden diffs.

It does NOT invent variants for new producers — add those by hand (a letter-adjacent
variant for any control-word emitter, and preserve variants inside protected
regions); the gate fails until every produces_fix:true rule has variants.
"""
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BIN = os.path.join(REPO, "_build/default/latex-parse/src/validators_cli.exe")
REGISTRY = os.path.join(REPO, "specs/v27/producer_triggers.json")
MAX_PASSES = 8


def apply_once(rid, data, pilot):
    env = dict(os.environ)
    if pilot:
        env["L0_VALIDATORS"] = "pilot"
    else:
        env.pop("L0_VALIDATORS", None)
    with tempfile.NamedTemporaryFile("wb", suffix=".tex", delete=False) as t:
        t.write(data)
        p = t.name
    try:
        out = subprocess.run([BIN, "--apply-fixes-for", rid, p], capture_output=True, env=env).stdout
        return b"\n".join(l for l in out.split(b"\n") if not l.startswith(b"# "))
    finally:
        os.unlink(p)


def fixpoint(rid, data, pilot):
    seen = {data}
    cur = data
    for _ in range(MAX_PASSES):
        nxt = apply_once(rid, cur, pilot)
        if nxt == cur:
            return cur
        if nxt in seen:
            return nxt
        seen.add(nxt)
        cur = nxt
    return cur


def main():
    with open(REGISTRY) as f:
        reg = json.load(f)
    changed = 0
    for rid, e in sorted(reg.items()):
        for v in e["variants"]:
            trig = bytes.fromhex(v["hex"])
            fp = fixpoint(rid, trig, v.get("pilot", True)).hex()
            if fp != v.get("expected_hex"):
                changed += 1
            v["expected_hex"] = fp
    with open(REGISTRY, "w") as f:
        json.dump(reg, f, indent=1, sort_keys=True)
    nvar = sum(len(e["variants"]) for e in reg.values())
    print(f"[gen-triggers] regenerated {nvar} variant goldens across {len(reg)} producers ({changed} changed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
