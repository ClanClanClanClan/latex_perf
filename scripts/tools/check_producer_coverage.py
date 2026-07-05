#!/usr/bin/env python3
"""Permanent producer-coverage + correctness gate.

Root cause it guards against (found in the v27.1.12 audit): the differential
(0-diff) and apply-fixes convergence gates only ever exercise a producer whose
trigger appears in the lint corpus AND in the mode (pilot / non-pilot) the corpus
runs. 69 of 150 producers (~46%) were NEVER corpus-triggered, so those gates gave
false confidence over half the producer surface — which is how the 7
control-word-glue bugs (\\cdot -> \\cdotb, etc.) and MATH-108 shipped unexercised.

This gate closes that gap structurally. For EVERY rule with produces_fix:true it
applies the rule's fix to a REGISTERED trigger (specs/v27/producer_triggers.json)
in the registered mode and asserts:

  * applied      — --apply-fixes-for changes the input (the producer really fires)
  * valid_utf8   — the applied output decodes as UTF-8
  * golden       — the output equals the recorded expected output (regression
                   detector: any change to a producer's fix output on its trigger
                   must be re-recorded and reviewed in the diff)
  * idempotent   — applying the fix a second time is a byte-identical no-op

The registry triggers are ADVERSARIAL where it matters — e.g. every control-word
producer's trigger is LETTER-ADJACENT ($a·b$, not $a · b$), which is exactly the
edge the audit and unit tests missed. The gate FAILS if any producer has no
registered trigger, so a new producer cannot ship until a trigger is registered
(and, for control-word emitters, it must be letter-adjacent).

Regenerate the registry with:  python3 scripts/tools/gen_producer_triggers.py
(only after INTENTIONAL producer changes, so the golden diffs are reviewed).
"""
from __future__ import annotations
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BIN = os.path.join(REPO, "_build/default/latex-parse/src/validators_cli.exe")
CONTRACTS = os.path.join(REPO, "specs/rules/rule_contracts.yaml")
REGISTRY = os.path.join(REPO, "specs/v27/producer_triggers.json")


def load_producers() -> list[str]:
    import yaml
    with open(CONTRACTS) as f:
        rules = yaml.safe_load(f)["rules"]
    return sorted(r["rule_id"] for r in rules if r.get("produces_fix") is True)


def apply_fix(rid: str, data: bytes, pilot: bool) -> bytes:
    env = dict(os.environ)
    if pilot:
        env["L0_VALIDATORS"] = "pilot"
    else:
        env.pop("L0_VALIDATORS", None)
    with tempfile.NamedTemporaryFile("wb", suffix=".tex", delete=False) as t:
        t.write(data)
        p = t.name
    try:
        out = subprocess.run([BIN, "--apply-fixes-for", rid, p],
                             capture_output=True, env=env).stdout
        return b"\n".join(l for l in out.split(b"\n") if not l.startswith(b"# "))
    finally:
        os.unlink(p)


def check_one(rid: str, entry: dict) -> list[str]:
    trig = bytes.fromhex(entry["hex"])
    expected = bytes.fromhex(entry["expected_hex"])
    pilot = entry.get("pilot", True)
    viol: list[str] = []
    out1 = apply_fix(rid, trig, pilot)
    if out1 == trig:
        return [f"{rid}: --apply-fixes-for made no change (producer did not fire on its trigger)"]
    try:
        out1.decode("utf-8")
    except UnicodeDecodeError as e:
        viol.append(f"{rid}: fixed output is NOT valid UTF-8 ({e})")
    if out1 != expected:
        viol.append(f"{rid}: output changed from recorded golden "
                    f"(got {out1!r}, expected {expected!r}) — re-run gen_producer_triggers.py if intended")
    out2 = apply_fix(rid, out1, pilot)
    if out2 != out1:
        viol.append(f"{rid}: NOT idempotent (2nd apply differs: {out2!r} vs {out1!r})")
    return viol


def main() -> int:
    producers = load_producers()
    if not os.path.exists(REGISTRY):
        print(f"[producer-coverage] FAIL: registry {os.path.relpath(REGISTRY, REPO)} missing", file=sys.stderr)
        return 1
    with open(REGISTRY) as f:
        registry = json.load(f)

    missing = [r for r in producers if r not in registry]
    violations: list[str] = []
    for rid in producers:
        if rid in missing:
            continue
        violations.extend(check_one(rid, registry[rid]))

    if missing:
        print(f"[producer-coverage] FAIL: {len(missing)} producer(s) have NO registered trigger "
              f"(add via gen_producer_triggers.py):", file=sys.stderr)
        for m in missing:
            print(f"  {m}", file=sys.stderr)
    if violations:
        print(f"[producer-coverage] FAIL: {len(violations)} correctness violation(s):", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
    if missing or violations:
        return 1
    print(f"[producer-coverage] PASS: all {len(producers)} producers apply, are valid-UTF-8, "
          f"idempotent, and match their golden output on adversarial triggers.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
