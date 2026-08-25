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

MIN_MUTATIONS = 8

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
    "check_unused_hypotheses.py": "no kill-test yet — the uncovered set is OPEN-036's ledger",
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
                     old="Correct verdicts: 133/199",
                     new="Correct verdicts: 134/199"),
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
        "check_known_false_ready", [PY, f"{TOOLS}/check_known_false_ready.py"],
        "binary",
        [
            # A fixed false-READY silently marked live (or vice versa) must
            # surface as drift, in either direction.
            Mutation("fr_polyglossia expected_cli flipped",
                     "corpora/false_ready/manifest.json",
                     r"UNRECORDED FIX|REGRESSION|baseline",
                     transform=flip_polyglossia),
        ]),
]


def run_gate(cmd) -> tuple[int, str]:
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def check_spec_drift_coverage() -> list[str]:
    """Every check_*.py wired into spec-drift must be covered or exempt."""
    wf = REPO / ".github/workflows/spec-drift.yml"
    invoked = set(re.findall(r"(check_[a-z_]+\.py)", wf.read_text()))
    covered = {Path(g.cmd[-1]).name for g in REGISTRY}
    problems = []
    for name in sorted(invoked):
        if name not in covered and name not in EXEMPT:
            problems.append(
                f"{name} is wired into required spec-drift but has neither a "
                f"kill-test in the REGISTRY nor an EXEMPT entry with a reason — "
                f"a gate nobody has seen fail is not evidence")
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
    if not (ns.force or os.environ.get("CI")):
        r = subprocess.run(["git", "--no-optional-locks", "status",
                            "--porcelain", "--", *targets],
                           cwd=REPO, capture_output=True, text=True)
        if r.stdout.strip():
            print("[gate-selftests] REFUSING: mutation targets are git-dirty "
                  "(a crash mid-mutation would eat uncommitted work):\n"
                  + r.stdout + "  commit/stash first, or pass --force")
            return 2

    failures, ran = [], 0
    for g in gates:
        rc, out = run_gate(g.cmd)
        if rc != 0:
            print(f"[gate-selftests] ABORT: {g.name} is ALREADY RED before any "
                  f"mutation — fix the gate first, then selftest it")
            print(out[:800])
            return 2
        for m in g.mutations:
            ran += 1
            before = sha(m.target)
            backup = m.target.read_bytes()
            st = m.target.stat()
            try:
                m.apply()
                rc, out = run_gate(g.cmd)
                if rc == 0:
                    failures.append(
                        f"{g.name} / '{m.label}': gate PASSED a known-bad "
                        f"mutation — it is blind to this defect class")
                elif not m.expect.search(out):
                    failures.append(
                        f"{g.name} / '{m.label}': gate failed but WITHOUT the "
                        f"expected message /{m.expect_src}/ — it is failing "
                        f"for the wrong reason. Output head: {out[:300]!r}")
            finally:
                m.target.write_bytes(backup)
                # Preserve mtime: a restored .ml with a fresh mtime makes dune
                # rebuild the world (15-25 min on this FS) for a no-op change.
                os.utime(m.target, (st.st_atime, st.st_mtime))
            if sha(m.target) != before:
                print(f"[gate-selftests] FATAL: restoration of {m.target} is "
                      f"NOT byte-identical — repo damaged, fix by hand NOW")
                return 2
        rc, out = run_gate(g.cmd)
        if rc != 0:
            print(f"[gate-selftests] FATAL: {g.name} is red AFTER restoration "
                  f"— the selftest damaged its inputs")
            print(out[:800])
            return 2

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
