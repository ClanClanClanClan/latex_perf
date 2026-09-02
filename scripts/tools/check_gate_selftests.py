#!/usr/bin/env python3
"""check_gate_selftests.py — mutation kill-tests: prove every covered gate can FAIL.

WHY THIS EXISTS. In one month, three of this repo's gates were found provably
blind, and every one had been green the whole time:

  * check_fix_type_consistency's Bucket-C producer check was satisfied by an
    OCaml COMMENT (C-27) — a commented-out producer certified as live;
  * the published root count matched the SUBSTRING "documentclass", so the one
    fixture that exists to lack a \\documentclass was counted as having one
    (C-28) — and the "fix" then published a defensible-looking derivation of
    the WRONG quantity (C-29);
  * check_fix_type_consistency itself sat RED on main for weeks because it ran
    in no CI path (OPEN-028).

The common shape: a gate nobody has ever seen fail is not evidence of anything.
This harness makes "can it fail?" a required, mechanical question. For each
registered gate it:

  1. runs the gate clean — must exit 0 (an already-red gate cannot be
     selftested; that is reported as infrastructure, exit 2);
  2. for each registered mutation: backs the target file up (content + mtime),
     applies a known-bad edit, runs the gate, and asserts BOTH a non-zero exit
     AND an expected message regex — the regex is the defence against a gate
     failing for the WRONG reason (e.g. the edit breaking YAML parsing rather
     than triggering the arm under test);
  3. restores the file and PROVES the restoration (sha256 compare, mtime
     preserved so a restored .ml does not trigger a 20-minute dune rebuild);
  4. runs the gate clean again — must exit 0.

ANTI-VACUITY, aimed at the harness itself:
  * every string-mutation anchor must occur EXACTLY ONCE in its target; a
    vanished or duplicated anchor is registry rot and fails the run (exit 2),
    never a silent skip;
  * the mutation count is pinned (MIN_MUTATIONS) so registry shrinkage is a
    deliberate act;
  * every `check_*.py` invoked by spec-drift.yml must appear in the REGISTRY or
    in EXEMPT with a written reason — a new gate wired into CI without
    kill-tests fails this harness, which is the "no gate ships without kill
    tests" invariant made mechanical (PROJECT_STATE §5).

Levels: --level pure (no build products needed; runs in required spec-drift) |
binary (needs the built validators_cli.exe; runs in the required build job) |
all. A missing CLI at binary level is a FAILURE (exit 2), not a skip — a
skipped selftest that reports green is the exact disease this file treats.

Safety: refuses to run if any target file is git-dirty (the mutations are
in-place; a crash must not be able to eat uncommitted work) unless CI=true or
--force. Every mutation runs under try/finally restore.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

MIN_MUTATIONS = 9

REPO = Path(__file__).resolve().parent.parent.parent
PY = sys.executable
TOOLS = "scripts/tools"

# Gates invoked by spec-drift.yml that are deliberately NOT covered yet.
# Removing an entry here without adding registry coverage fails the run.
# ⚠ 15 of the 18 spec-drift gates have NEVER been proven able to fail. That
# is the honest starting state, enumerated here rather than hidden; each
# entry removed from this dict must gain REGISTRY coverage in the same
# commit, and OPEN-036 tracks the burn-down.
EXEMPT = {
    "check_rule_contracts.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_regression_gates.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_code_quality.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_doc_refs.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_fix_safety_language.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_gates_meta.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_memo_files.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_mli_doc_coverage.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_release_integrity.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_repo_facts.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_roadmap_facts.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_severity_drift.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_version_labels.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_workflow_triggers.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
    "check_project_state.py": "covered (see REGISTRY)",
    "check_fix_type_consistency.py": "covered (see REGISTRY)",
    "check_gate_selftests.py": "this harness itself",
}


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


class Mutation:
    """One known-bad edit that MUST make its gate fail.

    Either (old, new) exact-string replacement — the anchor must occur exactly
    once — or a `transform` callable for structured files (JSON), where an
    embedded whitespace-sensitive anchor would be brittle.
    """

    def __init__(self, label, target, expect_regex, old=None, new=None,
                 transform=None):
        self.label, self.target = label, REPO / target
        self.expect = re.compile(expect_regex, re.S)
        self.expect_src = expect_regex
        self.old, self.new, self.transform = old, new, transform

    def apply(self) -> None:
        text = self.target.read_text(encoding="utf-8")
        if self.transform is not None:
            self.target.write_text(self.transform(text), encoding="utf-8")
            return
        n = text.count(self.old)
        if n != 1:
            # Registry rot: the anchor drifted. Loud infra failure, never a skip.
            print(f"[gate-selftests] REGISTRY ROT: anchor for '{self.label}' "
                  f"occurs {n}x in {self.target.name} (need exactly 1). "
                  f"Update the registry deliberately.")
            sys.exit(2)
        self.target.write_text(text.replace(self.old, self.new),
                               encoding="utf-8")


class GateTest:
    def __init__(self, name, cmd, level, mutations):
        self.name, self.cmd, self.level, self.mutations = name, cmd, level, mutations


def append_discarding_proof(text: str) -> str:
    """Append a proof that discards 2 hypotheses via ADJACENT underscores.

    This is the shape the gate was blind to until 2026-08-25: its counting
    regex CONSUMED the separator between matches, so `intros _ _` counted as 1
    (< THRESHOLD 2) — including the gate's own docstring example. The fix is a
    lookahead; this kill-test keeps it fixed.
    """
    return text + ("\nLemma killtest_discard : forall (a b : nat), True.\n"
                   "Proof. intros _ _. exact I. Qed.\n")


def flip_polyglossia(text: str) -> str:
    d = json.loads(text)
    fx = next(f for f in d["fixtures"] if f["id"] == "fr_polyglossia")
    assert fx["expected_cli"] == "NOT-READY", "fixture drifted; update registry"
    fx["expected_cli"] = "READY"
    return json.dumps(d, indent=1) + "\n"


REGISTRY = [
    GateTest(
        "check_fix_type_consistency", [PY, f"{TOOLS}/check_fix_type_consistency.py"],
        "pure",
        [
            # Arm 1: an auto-apply rule whose remedy type goes unrecorded.
            Mutation("produces_fix=true nulled (SCRIPT-021)",
                     "specs/rules/rules_v3.yaml",
                     r"SCRIPT-021: produces_fix=true but spec fix: is null",
                     old="  fix: reorder_scripts", new="  fix: null"),
            # Arm 2: a Bucket C token nulled — the destroy-18-commitments move.
            Mutation("Bucket C token nulled (REF-006)",
                     "specs/rules/rules_v3.yaml",
                     r"REF-006: Bucket C but spec fix: is null",
                     old="  fix: suggest_pageref", new="  fix: null"),
            # THE COMMENT-BLINDNESS REGRESSION TEST (C-27). Comment the only
            # REF-006 producer out. This kill FAILS iff the gate ever becomes
            # comment-blind again: a blind regex still sees the commented text,
            # the gate stays green, and this harness goes red.
            Mutation("REF-006 producer commented out",
                     "latex-parse/src/validators_l1.ml",
                     r"REF-006: Bucket C with fix: 'suggest_pageref' but NO",
                     old='(mk_result_with_candidates ~id:"REF-006"',
                     new='((* mk_result_with_candidates KILLTEST *) '
                         'mk_result ~id:"REF-006"'),
            # The Bucket-C set is derived from PROSE; a reworded reason must
            # trip the pin, not silently shrink the set.
            Mutation("Bucket C reason prefix reworded (REF-006)",
                     "scripts/tools/generate_rule_contracts.py",
                     r"PROBE FAILED: Bucket C is 17, pinned at 18",
                     old='"Bucket C (suggest_pageref',
                     new='"bucket C (suggest_pageref'),
        ]),
    GateTest(
        "check_project_state", [PY, f"{TOOLS}/check_project_state.py"],
        "pure",
        [
            # A hand-edited digit inside the generated block must be caught.
            Mutation("generated-block digit edited",
                     "docs/v27/PROJECT_STATE.md",
                     r"measured-position block is STALE",
                     # NB: this anchor is a LIVE number and rots by design
                     # whenever the measured position moves — updating it here
                     # is the deliberate act the registry-rot check forces.
                     # 187/199 since the OPEN-041/030 parser policy pair
                     # (over-rejection 19 -> 12; was 180/199 after OPEN-010,
                     # 172 after T2, 155 after T3, 141 after OPEN-002).
                     old="Correct verdicts: 187/199",
                     new="Correct verdicts: 188/199"),
            # Ledger discipline: a malformed size cell (caught live on
            # 2026-08-24 when an append overflowed the row — keep it caught).
            Mutation("ledger size cell malformed (OPEN-022)",
                     "docs/v27/PROJECT_STATE.md",
                     r"size must be one of S/M/L/XL",
                     old="verified by audit | S |",
                     new="verified by audit | ZZ |"),
            # CLAIM PROVENANCE (C-28): the published "APPLIED TO k/n" clause
            # must be recomputable from the rows it describes.
            Mutation("protocol APPLIED-TO clause falsified",
                     "corpora/real_roots/results.json",
                     r"does not match the recorded measurement",
                     old="APPLIED TO 18/200 rows",
                     new="APPLIED TO 42/200 rows"),
        ]),
    GateTest(
        "check_unused_hypotheses", [PY, f"{TOOLS}/check_unused_hypotheses.py"],
        "pure",
        [
            # The adjacent-underscore regression (OPEN-036 finding #1): before
            # the lookahead fix this exact mutation was INVISIBLE to the gate.
            Mutation("adjacent-underscore discard appended",
                     "proofs/BuildLog.v",
                     r"2 bare underscores in intros",
                     transform=append_discarding_proof),
        ]),
    GateTest(
        "check_known_false_ready", [PY, f"{TOOLS}/check_known_false_ready.py"],
        "binary",
        [
            # A fixed false-READY silently marked live (or vice versa) must
            # surface as drift, in either direction.
            # ⚠ The first version of this regex ended `|baseline` — and a
            # CRASHED gate (KeyError) prints its own source line, which
            # contains the word "baseline", so a crash would have counted as a
            # kill. Found by adversarial pre-ship review; the traceback guard
            # below now also rejects any "kill" whose output is a crash.
            Mutation("fr_polyglossia expected_cli flipped",
                     "corpora/false_ready/manifest.json",
                     r"UNRECORDED FIX|REGRESSION \(a fixed false-READY",
                     transform=flip_polyglossia),
        ]),
]


GATE_TIMEOUT = 300  # seconds — a hung gate must not hold a mutated tree open


def run_gate(cmd) -> tuple[int, str]:
    try:
        r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True,
                           timeout=GATE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return -1, "GATE TIMEOUT — treated as a crash, never as a kill"
    return r.returncode, r.stdout + r.stderr


def check_spec_drift_coverage() -> list[str]:
    """Coverage must hold in BOTH directions, across BOTH required workflows.

    v1 only checked invoked ⊆ covered ∪ exempt over spec-drift.yml. That is
    one-directional: a gate REMOVED from CI kept its green kill-tests forever —
    the OPEN-028 disease (a gate running nowhere) was invisible to this
    harness. And nothing asserted that ci.yml still runs the binary level at
    all. Both directions are now checked, over spec-drift.yml AND ci.yml.
    """
    sd = (REPO / ".github/workflows/spec-drift.yml").read_text()
    ci = (REPO / ".github/workflows/ci.yml").read_text()
    invoked = set(re.findall(r"(check_[a-z_]+\.py)", sd + ci))
    covered = {Path(g.cmd[-1]).name for g in REGISTRY}
    problems = []
    for name in sorted(set(re.findall(r"(check_[a-z_]+\.py)", sd))):
        if name not in covered and name not in EXEMPT:
            problems.append(
                f"{name} is wired into required spec-drift but has neither a "
                f"kill-test in the REGISTRY nor an EXEMPT entry with a reason — "
                f"a gate nobody has seen fail is not evidence")
    for name in sorted(covered - invoked):
        problems.append(
            f"{name} has kill-tests but is invoked by NEITHER spec-drift.yml "
            f"nor ci.yml — a gate running nowhere is the OPEN-028 disease, and "
            f"green kill-tests must not mask it")
    if "check_gate_selftests.py --level binary" not in ci:
        problems.append(
            "ci.yml no longer runs `check_gate_selftests.py --level binary` — "
            "the binary-level kill-tests are not executing anywhere")
    return problems


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--level", choices=["pure", "binary", "all"], default="all")
    ap.add_argument("--force", action="store_true",
                    help="run even if target files are git-dirty")
    ns = ap.parse_args()

    gates = [g for g in REGISTRY
             if ns.level == "all" or g.level == ns.level]
    n_mut = sum(len(g.mutations) for g in REGISTRY)
    if n_mut < MIN_MUTATIONS:
        print(f"[gate-selftests] REGISTRY SHRANK: {n_mut} mutations, pinned "
              f"minimum {MIN_MUTATIONS}. Shrinking coverage must be deliberate.")
        return 2

    problems = check_spec_drift_coverage()
    if problems:
        print(f"[gate-selftests] FAIL: {len(problems)} coverage problem(s)")
        for p in problems:
            print(f"  - {p}")
        return 1

    # The binary level MUST fail loudly when the CLI is absent. A skip that
    # reports green is the exact disease this harness treats.
    if ns.level in ("binary", "all"):
        cli = REPO / "_build/default/latex-parse/src/validators_cli.exe"
        if not cli.is_file():
            if ns.level == "binary":
                print("[gate-selftests] FAIL: binary level requested but the "
                      "CLI is not built — refusing to report green on a "
                      "selftest that did not run")
                return 2
            gates = [g for g in gates if g.level != "binary"]
            print("[gate-selftests] note: CLI not built; binary-level gates "
                  "excluded from this ALL run (they run in the build job)")

    # In-place mutations must not be able to eat uncommitted work.
    targets = sorted({str(m.target.relative_to(REPO))
                      for g in gates for m in g.mutations})
    # "CI" must mean CI: direnv/nix setups export CI=false, and any non-empty
    # string is truthy in Python — so `CI=false` used to skip the dirty check.
    in_ci = os.environ.get("CI", "").strip().lower() in ("1", "true", "yes")
    if not (ns.force or in_ci):
        r = subprocess.run(["git", "--no-optional-locks", "status",
                            "--porcelain", "--", *targets],
                           cwd=REPO, capture_output=True, text=True)
        if r.stdout.strip():
            print("[gate-selftests] REFUSING: mutation targets are git-dirty "
                  "(a crash mid-mutation would eat uncommitted work):\n"
                  + r.stdout + "  commit/stash first, or pass --force")
            return 2

    # ⚠ A SINGLE-INSTANCE LOCK, because two concurrent runs poison each
    # other's backups: B (started inside A's mutation window) backs up A's
    # MUTATED bytes as its "original", both restore "successfully", and the
    # tree ends permanently mutated while both exit green. O_EXCL is atomic;
    # a stale lock is reported with its pid, never silently stolen.
    lock = REPO / ".gate-selftests.lock"
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"{os.getpid()}\n".encode())
        os.close(fd)
    except FileExistsError:
        print(f"[gate-selftests] REFUSING: {lock} exists (pid "
              f"{lock.read_text().strip()!r}). Another selftest run is active "
              f"— or crashed; inspect, restore from .gate-selftest-backups/ "
              f"if needed, then remove the lock by hand.")
        return 2

    # ⚠ BACKUPS LIVE ON DISK BEFORE THE MUTATION DOES. v1 held the backup only
    # in process memory with a truncate-write restore and no subprocess
    # timeout — a hard kill (SIGKILL skips finally) in the mutation window
    # left the tree mutated with NOTHING on disk to recover from. Now: the
    # original bytes are written to .gate-selftest-backups/<name> and fsynced
    # BEFORE the target is touched, the restore goes through a temp file +
    # os.replace (atomic on POSIX), and the backup is deleted only after the
    # sha256 round-trip is proven.
    bdir = REPO / ".gate-selftest-backups"
    bdir.mkdir(exist_ok=True)

    failures, ran = [], 0
    try:
        for g in gates:
            rc, out = run_gate(g.cmd)
            if rc != 0:
                print(f"[gate-selftests] ABORT: {g.name} is ALREADY RED before "
                      f"any mutation — fix the gate first, then selftest it")
                print(out[:800])
                return 2
            for m in g.mutations:
                ran += 1
                before = sha(m.target)
                st = m.target.stat()
                bfile = bdir / m.target.name
                bfile.write_bytes(m.target.read_bytes())
                bfd = os.open(bfile, os.O_RDONLY)
                os.fsync(bfd)
                os.close(bfd)
                try:
                    m.apply()
                    rc, out = run_gate(g.cmd)
                    if rc == 0:
                        failures.append(
                            f"{g.name} / '{m.label}': gate PASSED a known-bad "
                            f"mutation — it is blind to this defect class")
                    elif "Traceback (most recent call last)" in out or rc == -1:
                        # A crash is NEVER a kill, whatever the regex says: a
                        # crashing gate prints its own source line, which can
                        # contain the very words the regex expects (measured:
                        # a KeyError in check_known_false_ready emitted
                        # "baseline" twice).
                        failures.append(
                            f"{g.name} / '{m.label}': gate CRASHED on the "
                            f"mutation instead of detecting it — a crash is "
                            f"not detection. Output head: {out[:300]!r}")
                    elif not m.expect.search(out):
                        failures.append(
                            f"{g.name} / '{m.label}': gate failed but WITHOUT "
                            f"the expected message /{m.expect_src}/ — it is "
                            f"failing for the wrong reason. Output head: "
                            f"{out[:300]!r}")
                finally:
                    tmp = m.target.with_suffix(m.target.suffix + ".restore-tmp")
                    tmp.write_bytes(bfile.read_bytes())
                    os.replace(tmp, m.target)  # atomic: never a torn restore
                    # Preserve mtime at ns precision: a fresh mtime on a
                    # restored .ml makes dune rebuild the world for a no-op.
                    os.utime(m.target, ns=(st.st_atime_ns, st.st_mtime_ns))
                if sha(m.target) != before:
                    print(f"[gate-selftests] FATAL: restoration of {m.target} "
                          f"is NOT byte-identical — recover from {bfile} NOW")
                    return 2
                bfile.unlink()  # only after the round-trip is proven
            rc, out = run_gate(g.cmd)
            if rc != 0:
                print(f"[gate-selftests] FATAL: {g.name} is red AFTER "
                      f"restoration — the selftest damaged its inputs")
                print(out[:800])
                return 2
    finally:
        lock.unlink(missing_ok=True)
        try:
            bdir.rmdir()  # succeeds only when empty = every backup consumed
        except OSError:
            print(f"[gate-selftests] WARNING: {bdir} is not empty — a backup "
                  f"was not consumed; inspect before trusting the tree")

    if failures:
        print(f"[gate-selftests] FAIL: {len(failures)} blind spot(s)")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"[gate-selftests] PASS: {ran} mutation(s) across "
          f"{len(gates)} gate(s) — every one killed its gate with the expected "
          f"message, and every restoration is byte-identical.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
