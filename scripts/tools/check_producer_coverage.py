#!/usr/bin/env python3
"""Permanent producer coverage + correctness gate (multi-trigger, fixpoint).

Root cause it guards against: the differential / apply-fixes convergence gates
only exercise a producer whose trigger appears in the corpus. As of v27.1.12,
69/150 producers were never corpus-triggered. Worse, even a SINGLE registered
trigger has blind spots — the v27.1.12 control-word-glue bugs hid behind
space-padded triggers, and the v27.1.13 protected-region leaks (a math producer
rewriting `$...$` INSIDE \\verb/comment) hid behind non-protected triggers.

So every producer carries a SET of adversarial variants (specs/v27/
producer_triggers.json), each stressing a different edge:
  * mutate variants  — letter-adjacent (glue), CJK-adjacent (multibyte), doubled,
                       EOF/BOL; the fix SHOULD change them.
  * preserve variants — the trigger placed inside a protected region (comment /
                        $math$ for non-math rules / \\verb / \\url); the fix MUST
                        leave them byte-identical.

For each variant the gate applies the producer's fix to a FIXPOINT (repeatedly,
matching the production `--apply-fixes` converge loop, capped) and asserts:
  * converges  — a fixpoint is reached within the cap (no oscillation)
  * valid_utf8 — the fixpoint decodes as UTF-8
  * golden     — the fixpoint equals the recorded expected output (regression
                 detector for BOTH the change and the no-change cases)

Fails if any producer has no variants → coverage is non-optional; a new producer
cannot ship until an adversarial variant set is registered (and, for control-word
emitters, must include a letter-adjacent variant). Regenerate goldens with
`gen_producer_triggers.py` after intentional producer changes.
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
MAX_PASSES = 8


def load_producers() -> list[str]:
    import yaml
    with open(CONTRACTS) as f:
        rules = yaml.safe_load(f)["rules"]
    return sorted(r["rule_id"] for r in rules if r.get("produces_fix") is True)


def apply_once(rid: str, data: bytes, pilot: bool) -> bytes:
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


def fixpoint(rid: str, data: bytes, pilot: bool):
    """Return (status, fixpoint_bytes). status in converged|cycle|cap."""
    seen = {data}
    cur = data
    for _ in range(MAX_PASSES):
        nxt = apply_once(rid, cur, pilot)
        if nxt == cur:
            return "converged", cur
        if nxt in seen:
            return "cycle", nxt
        seen.add(nxt)
        cur = nxt
    return "cap", cur


def check_variant(rid: str, v: dict) -> list[str]:
    trig = bytes.fromhex(v["hex"])
    expected = bytes.fromhex(v["expected_hex"])
    pilot = v.get("pilot", True)
    note = v.get("note", "?")
    viol = []
    status, fp = fixpoint(rid, trig, pilot)
    if status != "converged":
        viol.append(f"{rid} [{note}]: did NOT converge ({status}) within {MAX_PASSES} passes")
        return viol
    # Invariant: a fix must not CORRUPT valid input. If the trigger is already
    # invalid UTF-8 (ENC-004's domain — CP-1252 bytes it may legitimately leave
    # unfixed when the byte is CP-1252-undefined or inside a protected region),
    # the output is not required to be valid; the golden-match below still pins
    # the exact expected bytes.
    input_valid = True
    try:
        trig.decode("utf-8")
    except UnicodeDecodeError:
        input_valid = False
    if input_valid:
        try:
            fp.decode("utf-8")
        except UnicodeDecodeError as e:
            viol.append(f"{rid} [{note}]: fix turned VALID input into invalid UTF-8 ({e})")
    if fp != expected:
        viol.append(f"{rid} [{note}]: fixpoint {fp!r} != golden {expected!r} "
                    f"(re-run gen_producer_triggers.py if intended)")
    return viol


def main() -> int:
    producers = load_producers()
    if not os.path.exists(REGISTRY):
        print(f"[producer-coverage] FAIL: registry {os.path.relpath(REGISTRY, REPO)} missing", file=sys.stderr)
        return 1
    with open(REGISTRY) as f:
        registry = json.load(f)

    missing = [r for r in producers if r not in registry or not registry[r].get("variants")]
    violations: list[str] = []
    nvariants = 0
    for rid in producers:
        if rid in missing:
            continue
        for v in registry[rid]["variants"]:
            nvariants += 1
            violations.extend(check_variant(rid, v))

    if missing:
        print(f"[producer-coverage] FAIL: {len(missing)} producer(s) have NO registered variants "
              f"(add via gen_producer_triggers.py):", file=sys.stderr)
        for m in missing:
            print(f"  {m}", file=sys.stderr)
    if violations:
        print(f"[producer-coverage] FAIL: {len(violations)} variant violation(s):", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
    if missing or violations:
        return 1
    print(f"[producer-coverage] PASS: all {len(producers)} producers × {nvariants} adversarial "
          f"variants converge to valid, golden-matching fixpoints (glue / multibyte / "
          f"protected-region / idempotence edges).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
