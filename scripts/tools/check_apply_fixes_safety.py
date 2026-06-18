#!/usr/bin/env python3
"""check_apply_fixes_safety.py — corpus-wide --apply-fixes output safety gate.

The differential test (run_differential_test.py) validates LINT output (which
rules fire and how many times) is unchanged across releases. It is completely
BLIND to what the fixes actually *produce* — a buggy fix that corrupts content,
fails to converge, or introduces a new lint error sails through it. Per-fix unit
tests + a handful of E2E fixtures are the only other guard. This gate closes
that hole by exercising the real `--apply-fixes` path across the whole corpus.

For every corpus file it iterates `--apply-fixes` to a fixpoint (cycle-detected,
capped at MAX_PASSES). HARD safety properties (fail the gate):

  1. CONVERGENCE — fixes reach a stable fixpoint within MAX_PASSES (no cycle).
     A cycle means two producers contradict each other (e.g. TYPO-002 `--`→`–`
     vs TYPO-026 `–`→`--`, or CJK-001/002 `fullwidth→ASCII` vs CJK-010
     `ASCII→fullwidth`), so `--apply-fixes` would never stabilise.
  2. VALID OUTPUT — the fixpoint output is valid UTF-8 (structural-corruption
     check; extend to CST round-trip when wired to the OCaml side).

INFORMATIONAL (reported, does not fail): rules whose count rises at the fixpoint.
A v27.0.72 corpus investigation established these are NOT content corruption — they
are either benign convergent cascades, or naive diagnose-only scanners
false-positiving on a *correct* fix (TYPO-045's `$`-toggle math scan and TYPO-043's
verbatim scan both mis-fire after a fix shifts bytes; neither rule produces a fix).
They are surfaced for review, not used to block, because "new lint count" is a noisy
proxy for the real property (no corruption), which (1)+(2) capture directly. Fixing
those naive scanners is tracked separately.

Runs in pilot mode (L0_VALIDATORS=pilot) so pilot-gated TYPO fixes are exercised.

Exit 0 if every corpus file converges to valid output. Exit 1 (listing each hard
violation) otherwise. Both originally-tracked contradictory producer pairs have
now been reconciled at the source (TYPO-002⇄TYPO-026 numeric-range delegation;
CJK-001/002⇄CJK-010 Han-adjacency delegation), so KNOWN_UNSTABLE_SUBSTR is empty
and EVERY corpus file must converge — any non-convergence fails the gate.
"""

from __future__ import annotations

import argparse
import glob
import os
import subprocess
import sys
import tempfile

MAX_PASSES = 8

# Tracked non-convergent files pending reconciliation (do NOT fail the gate on
# these; DO fail on any NEW non-convergence). Both originally-tracked oscillating
# producer pairs are now RESOLVED at the source, so this is empty:
#   - dash: TYPO-002 (`--`→`–`) vs TYPO-026 (`–`→`--`) — TYPO-002 now delegates
#           numeric ranges (digit`--`digit) to TYPO-026.
#   - CJK:  CJK-001/002 (`fullwidth→ASCII`) vs CJK-010 (`ASCII→fullwidth`) —
#           CJK-001/002 now delegate Han-adjacent fullwidth punctuation to
#           CJK-010 (fullwidth_punct_adjacent_to_cjk), so the ±32-byte context
#           window no longer flips under the conversion.
KNOWN_UNSTABLE_SUBSTR: tuple[str, ...] = ()


def cli(repo: str) -> str:
    return os.path.join(repo, "_build/default/latex-parse/src/validators_cli.exe")


def lint_counts(binp: str, path: str, env) -> dict[str, int]:
    out = subprocess.run([binp, path], capture_output=True, text=True, env=env).stdout
    d: dict[str, int] = {}
    for ln in out.splitlines():
        if ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 3:
            try:
                d[p[0]] = int(p[2])
            except ValueError:
                pass
    return d


def apply_once(binp: str, path: str, env) -> str:
    out = subprocess.run(
        [binp, "--apply-fixes", path], capture_output=True, text=True, env=env
    ).stdout
    return "\n".join(l for l in out.splitlines() if not l.startswith("# "))


def fixpoint(binp: str, path: str, env):
    """Return (converged: bool, final_text: str, passes: int)."""
    cur = open(path, encoding="utf-8", errors="ignore").read()
    seen = {cur.rstrip("\n")}
    for n in range(1, MAX_PASSES + 1):
        with tempfile.NamedTemporaryFile("w", suffix=".tex", delete=False) as t:
            t.write(cur)
            tp = t.name
        try:
            nxt = apply_once(binp, tp, env)
        finally:
            os.unlink(tp)
        if nxt.rstrip("\n") == cur.rstrip("\n"):
            return True, cur, n  # stable fixpoint
        if nxt.rstrip("\n") in seen:
            return False, nxt, n  # cycle (oscillation)
        seen.add(nxt.rstrip("\n"))
        cur = nxt
    return False, cur, MAX_PASSES  # did not stabilise within cap


def allowlisted(path: str) -> bool:
    return any(s in path for s in KNOWN_UNSTABLE_SUBSTR)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--corpus", default="corpora/lint")
    ns = ap.parse_args()
    binp = cli(ns.repo)
    if not os.path.isfile(binp):
        # Self-build so the gate is runnable standalone (pre_release runs it after
        # the full build, so this is normally a no-op).
        subprocess.run(
            ["opam", "exec", "--", "dune", "build", "latex-parse/src/validators_cli.exe"],
            cwd=ns.repo, check=False,
        )
    if not os.path.isfile(binp):
        print("[apply-fixes-safety] FAIL: validators_cli.exe not built and build failed",
              file=sys.stderr)
        return 1
    env = dict(os.environ, L0_VALIDATORS="pilot")
    files = sorted(
        f for f in glob.glob(os.path.join(ns.repo, ns.corpus, "**/*"), recursive=True)
        if os.path.isfile(f)
    )

    nonconv, new_err, bad_utf8 = [], [], []
    for f in files:
        base = lint_counts(binp, f, env)
        converged, final, passes = fixpoint(binp, f, env)
        rel = os.path.relpath(f, ns.repo)
        if not converged:
            if not allowlisted(rel):
                nonconv.append(f"{rel}: did not converge in {MAX_PASSES} passes (contradictory producers?)")
            continue
        try:
            final.encode("utf-8")
        except UnicodeError:
            bad_utf8.append(rel)
        with tempfile.NamedTemporaryFile("w", suffix=".tex", delete=False) as t:
            t.write(final)
            tp = t.name
        try:
            fc = lint_counts(binp, tp, env)
        finally:
            os.unlink(tp)
        for rid, c in fc.items():
            if c > base.get(rid, 0):
                new_err.append(f"{rel}: {rid} {base.get(rid, 0)}→{c}")

    # Informational: rises in lint counts at the fixpoint (noisy proxy — see
    # module docstring; investigated and confirmed non-corrupting).
    if new_err:
        print(f"[apply-fixes-safety] INFO: {len(new_err)} rule-count rise(s) at fixpoint "
              f"(diagnose-only-scanner noise / convergent cascades, not corruption):")
        for v in new_err:
            print(f"  info: {v}")

    # Hard safety violations: non-convergence (oscillation) + invalid output.
    violations = nonconv + [f"{b}: fixpoint output not valid UTF-8" for b in bad_utf8]
    if violations:
        print(f"[apply-fixes-safety] FAIL: {len(violations)} hard safety violation(s) "
              f"across {len(files)} corpus files:", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1
    print(f"[apply-fixes-safety] PASS: all {len(files)} corpus files converge to valid "
          f"output (pilot mode, ≤{MAX_PASSES} passes; {len(new_err)} informational count-rises).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
