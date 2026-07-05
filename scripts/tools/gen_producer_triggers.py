#!/usr/bin/env python3
"""Regenerate the golden expected-output field of specs/v27/producer_triggers.json.

The registry maps each producer to an ADVERSARIAL trigger (hex), the mode
(pilot), and the expected fixed output (expected_hex). This script keeps the
triggers as-is and re-derives expected_hex from the CURRENT binary, so after an
INTENTIONAL producer change you run this and review the golden diffs.

It does NOT invent triggers for new producers — add those by hand (letter-adjacent
for any control-word emitter) so a human picks an edge-stressing input; the gate
check_producer_coverage.py fails until every produces_fix:true rule has an entry.

Usage: build validators_cli.exe first, then: python3 scripts/tools/gen_producer_triggers.py
"""
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BIN = os.path.join(REPO, "_build/default/latex-parse/src/validators_cli.exe")
REGISTRY = os.path.join(REPO, "specs/v27/producer_triggers.json")


def apply_fix(rid, data, pilot):
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


def main():
    with open(REGISTRY) as f:
        reg = json.load(f)
    changed = 0
    for rid, e in sorted(reg.items()):
        trig = bytes.fromhex(e["hex"])
        out = apply_fix(rid, trig, e.get("pilot", True))
        new_hex = out.hex()
        if new_hex != e.get("expected_hex"):
            changed += 1
        e["expected_hex"] = new_hex
    with open(REGISTRY, "w") as f:
        json.dump(reg, f, indent=1, sort_keys=True)
    print(f"[gen-triggers] regenerated {len(reg)} goldens ({changed} changed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
