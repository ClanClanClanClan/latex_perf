#!/usr/bin/env python3
"""Kill-tests for the kill-test harness's PARALLEL machinery.

check_gate_selftests.py runs its mutations concurrently, each in an isolated
worktree copy. Parallelism adds one way to be wrong that the serial harness
did not have: a surviving mutant can be LOST between the worker that saw it and
the report (a dropped future, a keyed result overwritten, an aggregation that
skips an entry) — and a lost survivor reads exactly like a kill. Each arm
below asserts the KIND of outcome, not merely that the run went red:

  1. a no-op mutation injected into the registry (--inject-survivor) run with
     2 workers -> exit 1, reported as a blind spot BY NAME;
  2. the same run without the injection -> exit 0 (so arm 1's failure is the
     injection, not a broken gate or a broken copy);
  3. the always-on canary: with the verdict function sabotaged in-process to
     MASK survivors, the run must refuse to report (exit 2, canary FATAL) —
     so a masking defect cannot turn a surviving mutant into a green run.

Cheap by construction: one small gate (--only), two workers.
"""
import contextlib
import io
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
HARNESS = HERE / "check_gate_selftests.py"
GATE = "check_fix_producer_ledger"  # one mutation, sub-second gate

fails = 0


def check(name, ok, detail=""):
    global fails
    print(f"  [{'ok' if ok else 'FAIL'}] {name}" + ("" if ok else f"\n{detail}"))
    fails += not ok


def run(*extra):
    r = subprocess.run([sys.executable, str(HARNESS), "--level", "pure",
                        "--only", GATE, "--jobs", "2", *extra],
                       cwd=REPO, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


print("[selftest-gate-selftests] parallel harness kill-tests")
rc, out = run("--inject-survivor")
check("an injected surviving mutant fails the run (exit 1)", rc == 1, out)
check("... and is reported by name as a blind spot",
      "INJECTED SURVIVOR" in out
      and "gate PASSED a known-bad mutation" in out
      and "FAIL: 1 blind spot(s)" in out, out)

rc, out = run()
check("the same run without the injection passes (exit 0)", rc == 0, out)
check("... having run the canary in isolated mode",
      "isolated mode" in out and "PASS: 1 mutation(s)" in out, out)

# Arm 3: sabotage the verdict so a survivor (rc == 0) is classified as a kill.
sys.path.insert(0, str(HERE))
import check_gate_selftests as h  # noqa: E402

_real = h.classify


def masking(g, m, rc, out):
    return None if rc == 0 else _real(g, m, rc, out)


h.classify = masking
argv = sys.argv
sys.argv = [str(HARNESS), "--level", "pure", "--only", GATE, "--jobs", "2"]
buf = io.StringIO()
try:
    with contextlib.redirect_stdout(buf):
        rc = h.main()
finally:
    sys.argv = argv
    h.classify = _real
out = buf.getvalue()
check("a verdict that masks survivors is caught by the canary (exit 2)",
      rc == 2 and "harness canary" in out and "FATAL" in out, out)

if fails:
    print(f"[selftest-gate-selftests] FAIL: {fails} arm(s)")
    sys.exit(1)
print("[selftest-gate-selftests] PASS: 3 arms")
