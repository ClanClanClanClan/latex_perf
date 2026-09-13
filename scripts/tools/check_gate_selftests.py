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

MIN_MUTATIONS = 12

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
    # Wired into spec-drift on 2026-09-12 (OPEN-091) after being release-only.
    # Exempt ONLY until their kill-tests land in the same burn-down; wiring a
    # gate and proving it can fail are two different things, and shipping the
    # first without the second is what OPEN-036 is about.
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
        # ⚠ PRESERVE THE FILE MODE. write_text/write_bytes create the file with
        # default permissions, so mutating an EXECUTABLE script and restoring it
        # silently drops the +x bit. This harness reports "every restoration is
        # byte-identical" and that stayed true — the CONTENT was identical and
        # the METADATA was not. It cost a red `compliance` job:
        # scripts/validate_catalogue.py went 100755 -> 100644 and
        # validate_catalogue.sh died `Permission denied` (exit 126).
        self._mode = self.target.stat().st_mode
        text = self.target.read_text(encoding="utf-8")
        if self.transform is not None:
            self.target.write_text(self.transform(text), encoding="utf-8")
            os.chmod(self.target, self._mode)
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
        os.chmod(self.target, self._mode)


class GateTest:
    def __init__(self, name, cmd, level, mutations):
        self.name, self.cmd, self.level, self.mutations = name, cmd, level, mutations


def readme_version_drift(text: str) -> str:
    """Bump the README title version away from project_facts, version-agnostically.

    This mutation used to pin the literal `# LaTeX Perfectionist v27.1.62`.
    Cutting v27.1.63 rotted that anchor and aborted the whole harness — a
    kill-test that breaks on every release is a kill-test people delete. The
    rule it guards (README title must equal project_facts version) does not
    depend on WHICH version, so neither should the mutation.
    """
    import re as _re
    m = _re.search(r"^# LaTeX Perfectionist v(\d+)\.(\d+)\.(\d+)", text, _re.M)
    if not m:
        print("[gate-selftests] REGISTRY ROT: no '# LaTeX Perfectionist vX.Y.Z' "
              "title in README.md")
        sys.exit(2)
    bogus = f"v{m.group(1)}.{m.group(2)}.{int(m.group(3)) - 1}"
    return text.replace(m.group(0), f"# LaTeX Perfectionist {bogus}", 1)


def stale_governance_count(text: str) -> str:
    """OPEN-082/083. Roll ONE generated count back to a stale value.

    governance/project_facts.yaml is generated, but for 97 commits nothing
    regenerated it: 63/178/1543 shipped against a measured 64/179/1592, and
    check_repo_facts.py meanwhile pinned ten outward-facing files to the stale
    numbers. Gate B (regenerate into a tempdir, diff the committed file) exists
    for exactly that; decrementing proof_files_core reproduces it.

    This kills rather than no-ops because generate_project_facts.py MEASURES
    proof_files_core (files_core, counted by globbing proofs/*.v) — it reads the
    committed file only for a release_date fallback, and release_date is in the
    gate's ignore_lines. So the regenerated side stays at the true count while
    the committed side is stale, and run_and_diff reports the difference.

    Version-agnostic on purpose: the count moves whenever a core .v file lands
    (63 -> 64 with PdflatexFatalChannels.v), and a kill-test that rots on every
    proof addition is a kill-test people delete. Line-anchored because the bare
    string `proof_files_core` also appears as `- proofs.proof_files_core` under
    honesty_annotation.measured_and_true.
    """
    import re as _re
    anchor = r"^(  proof_files_core: )(\d+)$"
    hits = _re.findall(anchor, text, _re.M)
    if len(hits) != 1:
        print(f"[gate-selftests] REGISTRY ROT: '  proof_files_core: <n>' occurs "
              f"{len(hits)}x in governance/project_facts.yaml (need exactly 1)")
        sys.exit(2)
    m = _re.search(anchor, text, _re.M)
    return text.replace(m.group(0), f"{m.group(1)}{int(m.group(2)) - 1}", 1)

def stale_theorem_total(text: str) -> str:
    """OPEN-082/083: docs/PROOFS.md states a theorem total governance denies.

    Not hypothetical and not old. On 2026-09-12 docs/PROOFS.md:8 and
    docs/PROOF_GUIDE.md:146 read `1,543 theorems/lemmas` while
    governance/project_facts.yaml said 1592 — stale since
    proofs/PdflatexFatalChannels.v landed in #592 — and scripts/release.sh was
    armed to abort the v27.1.63 ceremony on the discrepancy. It is also the
    exact finding that put these two files in CHECKS (PR #245 p1.9: the docs
    said 1,157 theorems, governance said 1,181 — the 24 subtracted below).

    The total moves every time a proof lands, so a literal anchor would rot at
    the next release: the README-title anchor already did exactly that and
    aborted this whole harness. The number is therefore read from governance
    at mutation time, and EVERY rendering the gate accepts (bare and
    comma-grouped) is rewritten globally, so the kill cannot be softened by
    the document phrasing the number differently or stating it twice.
    """
    facts = REPO / "governance/project_facts.yaml"
    m = (re.search(r"^\s*theorem_count_reported:\s*(\d+)\s*$",
                   facts.read_text(encoding="utf-8"), re.M)
         if facts.is_file() else None)
    if m is None:
        print("[gate-selftests] REGISTRY ROT: governance/project_facts.yaml is "
              "missing or has no proofs.theorem_count_reported")
        sys.exit(2)
    n = int(m.group(1))
    comma = f"{n:,}"
    if comma not in text and str(n) not in text:
        print(f"[gate-selftests] REGISTRY ROT: docs/PROOFS.md no longer states "
              f"the governance theorem total {n} in any form the gate reads")
        sys.exit(2)
    out = text.replace(comma, f"{n - 24:,}").replace(str(n), str(n - 24))
    # Post-condition: mirror check_repo_facts.render_candidates. If any
    # rendering survived, the gate would PASS and the harness would report it
    # blind — a false accusation of the gate. Fail as registry rot instead.
    if any(c in out for c in (str(n), comma, f"{comma} theorems",
                              f"{n} theorems", f"{comma} theorems/lemmas")):
        print(f"[gate-selftests] REGISTRY ROT: a rendering of {n} survived the "
              f"docs/PROOFS.md mutation; the gate would pass and be falsely "
              f"reported blind")
        sys.exit(2)
    return out


def afr_raise_break_count(text: str) -> str:
    """Flip one preserved row to broken — the regression this gate exists for.

    A producer that starts destroying real papers shows up exactly here: the
    break count rises above the ratchet. Mutating the ARTEFACT rather than the
    gate proves the gate reads the measurement, not its own constant.
    """
    import json as _json
    d = _json.loads(text)
    for r in d["rows"]:
        if r.get("cell") == "preserved":
            r["cell"] = "broken"
            r["rc_after"] = 1
            break
    d["summary"]["preserved"] -= 1
    d["summary"]["broken"] += 1
    return _json.dumps(d, indent=2, ensure_ascii=False) + "\n"


def afr_desync_cell(text: str) -> str:
    """Leave a row labelled `preserved` while its own rc says it failed.

    C-45's shape: a summary computed FROM a wrong cell agrees with it. The
    gate must re-derive each cell from the row's recorded rc pair.
    """
    import json as _json
    d = _json.loads(text)
    for r in d["rows"]:
        if r.get("cell") == "preserved":
            r["rc_after"] = 1
            break
    return _json.dumps(d, indent=2, ensure_ascii=False) + "\n"


def append_discarding_proof(text: str) -> str:
    """Append a proof that discards 2 hypotheses via ADJACENT underscores.

    This is the shape the gate was blind to until 2026-08-25: its counting
    regex CONSUMED the separator between matches, so `intros _ _` counted as 1
    (< THRESHOLD 2) — including the gate's own docstring example. The fix is a
    lookahead; this kill-test keeps it fixed.
    """
    return text + ("\nLemma killtest_discard : forall (a b : nat), True.\n"
                   "Proof. intros _ _. exact I. Qed.\n")


def reinsert_gates_pass_iff(text: str) -> str:
    """OPEN-055. Put back the `X <-> X` tautology this gate now catches.

    all_static_gates_pass is DEFINITIONALLY the conjunction on the right, so
    the statement is X <-> X and the proof is split; intros H; exact H. It
    shipped for months because CompileProgress.v was outside the gate's
    LOAD_BEARING list AND because bullets and `split` both short-circuit
    is_hypothesis_restatement.
    """
    marker = "  (* OPEN-055: [gates_pass_iff] was DELETED here"
    assert marker in text, "OPEN-055 marker gone; update registry"
    taut = (
        "  Lemma gates_pass_iff :\n"
        "    forall p pf,\n"
        "      all_static_gates_pass p pf <->\n"
        "      T0_accepts p /\\ T1_admissible p /\\ T2_closed p /\\\n"
        "      T3_compatible p pf /\\ T4_coherent p /\\ T5_safe p.\n"
        "  Proof.\n"
        "    intros p pf. split.\n"
        "    - intros H. exact H.\n"
        "    - intros H. exact H.\n"
        "  Qed.\n\n")
    i = text.index(marker)
    return text[:i] + taut + text[i:]


def restrand_ungraded_row(text: str) -> str:
    """C-45. Re-create the sticky-`ungraded` defect exactly as it shipped.

    Puts a row back to `ungraded-infra` while its own recorded pdflatex_rc is
    0, which is the state OPEN-053's re-grade left behind and which nothing
    detected for two commits (res["counts"] is recomputed FROM the cells, so
    the artefact stayed self-consistent while being wrong about the world).
    """
    d = json.loads(text)
    row = next(r for r in d["docs"] if r.get("pdflatex_rc") == 0
               and r.get("cell") == "true-READY")
    row["cell"] = "ungraded-infra"
    d["counts"] = {}
    for r in d["docs"]:
        d["counts"][r["cell"]] = d["counts"].get(r["cell"], 0) + 1
    return json.dumps(d, indent=1) + "\n"


def drift_baseline_split(text: str) -> str:
    """C-43. Push baseline.error_halt off the live fixture split.

    Keeps false_ready_total correct, so this arm can only be killed by the
    sub-count check — not by the pre-existing total check.
    """
    d = json.loads(text)
    b = d["baseline"]
    assert "error_halt" in b, "baseline split gone; update registry"
    b["error_halt"] = b["error_halt"] + 5
    return json.dumps(d, indent=1) + "\n"


# ── Anchors for the check_workflow_triggers mode-4/5 kill-tests ───────
#
# These pin the EXACT text of the exhaustion guards added on 2026-09-13.
# Written out rather than regex-matched so that if the guard is reworded the
# harness aborts with REGISTRY ROT instead of silently testing nothing --
# a mutation whose `old` is absent is the classic vacuous kill-test.

GUARD_45 = (
    '          if [ "$warm" -ne 1 ]; then\n'
    '            echo "::error::workers never answered a warmup request'
    ' after 45 attempts" >&2\n'
    "            cat service.stderr 2>/dev/null || true\n"
    "            exit 1\n"
    "          fi\n"
)

OPAM_GUARDED_BLOCK = (
    "        installed=0\n"
    "        for attempt in 1 2 3; do\n"
    "          if opam update -y && opam install -y"
    " ${{ inputs.opam-packages }}; then\n"
    "            installed=1\n"
    "            break\n"
    "          fi\n"
    "          echo \"[setup-ocaml-env] opam install failed"
    " (attempt $attempt/3), retrying in 15s...\"\n"
    "          sleep 15\n"
    "        done\n"
    "        if [ \"$installed\" -ne 1 ]; then\n"
    "          echo \"::error::[setup-ocaml-env] opam install failed 3/3 for:\" \\\n"
    "               \"${{ inputs.opam-packages }}\"\n"
    "          exit 1\n"
    "        fi\n"
)

# main's text before 2026-09-13: `&& break`, and nothing after `done`.
OPAM_SILENT_BLOCK = (
    "        for attempt in 1 2 3; do\n"
    "          opam update -y && opam install -y"
    " ${{ inputs.opam-packages }} && break\n"
    "          echo \"[setup-ocaml-env] opam install failed"
    " (attempt $attempt/3), retrying in 15s...\"\n"
    "          sleep 15\n"
    "        done\n"
)


def drift_second_setup_ocaml(text: str) -> str:
    """Give the RETRY attempt a different compiler than attempt 1.

    Mutates the LAST occurrence so attempt 1 keeps the pinned version and the
    pair is genuinely inconsistent -- which is the defect, not merely an edit.
    """
    needle = "ocaml-compiler: 5.1.1"
    i = text.rindex(needle)
    return text[:i] + "ocaml-compiler: 5.2.0" + text[i + len(needle):]


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
        "check_doc_consistency", [PY, f"{TOOLS}/check_doc_consistency.py"],
        "pure",
        [
            # A number published in two places must not be allowed to drift.
            # Both anchors below were LIVE contradictions on main before
            # 2026-09-04; the gate exists because they shipped.
            Mutation("README version drifts from project_facts",
                     "README.md",
                     r"README title says .* but project_facts",
                     transform=readme_version_drift),
            Mutation("rule-maturity block goes stale",
                     "specs/rules/README.md",
                     r"specs/rules/README.md says Draft",
                     old="  - Draft: 529",
                     new="  - Draft: 619"),
            # ── OPEN-078 / C-47 ───────────────────────────────────────────
            # The three below pin the REPAIRS, not the original rules. The
            # first version of inv_no_handwritten_position exempted any line
            # containing "superseded" and matched only \d{2,3}/(199|200); the
            # first version of inv_compile_blocking_count scanned three files
            # for one phrasing and matched ZERO times in all three. Each
            # mutation reproduces one of those blind spots, so a regression
            # to the old shape fails here rather than eight days later.
            Mutation("a positional restatement hides behind the retired "
                     "'superseded' hatch",
                     "docs/v27/PROJECT_STATE.md",
                     r"handwritten-position.*198/200",
                     old="## 2. Where we are, in one paragraph",
                     new="## 2. Where we are, in one paragraph\n\n"
                         "Superseded note: sample 1 is 198/200 correct."),
            Mutation("a BARE PERCENTAGE — the shape the old pattern could "
                     "not see at all",
                     "docs/v27/PROJECT_STATE.md",
                     r"handwritten-position.*7\.2%",
                     old="## 6. Provenance",
                     new="## 6. Provenance\n\n"
                         "The certificate is wrong on 7.2% of certified papers."),
            Mutation("a stale compile-blocking count OUTSIDE the three files "
                     "the old invariant scanned",
                     "latex-parse/src/compile_contract.mli",
                     r"compile-blocking-count.*compile_contract\.mli.*37",
                     old="run ONLY the 36 compile-blocking rules",
                     new="run ONLY the 37 compile-blocking rules"),
        ]),
    GateTest(
        "check_apply_fixes_real_differential",
        [PY, f"{TOOLS}/check_apply_fixes_real_differential.py"],
        "pure",
        [
            Mutation("a producer starts breaking real papers again",
                     "corpora/apply_fixes_real/results.json",
                     r"breaks \d+ of \d+ real COMPILING papers; the pinned "
                     r"baseline is",
                     transform=afr_raise_break_count),
            Mutation("a row's cell stops following from its own rc pair",
                     "corpora/apply_fixes_real/results.json",
                     r"cell 'preserved' but rc_after=1",
                     transform=afr_desync_cell),
        ]),
    GateTest(
        "check_proof_substance",
        [PY, f"{TOOLS}/check_proof_substance.py"],
        "pure",
        [
            # OPEN-055: an `X <-> X` iff proved by split/intros/exact. The
            # regex names the new arm's wording specifically so the older
            # hypothesis-restatement arm cannot supply a false kill.
            Mutation("X <-> X tautology reinserted (OPEN-055)",
                     "proofs/CompileProgress.v",
                     r"is an `X <-> X` restatement",
                     transform=reinsert_gates_pass_iff),
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
                     # 197/199 since the residual-eight triple (kpathsea
                     # allowlist + DELIM-003 def-family guard + CJK
                     # containment): over-rejection 8 -> 2; was 191 after
                     # OPEN-042, 187/180/172/155/141 before.
                     # C-45 moved it again: repairing the stranded
                     # `ungraded-infra` row made sample 1 FULLY graded, so the
                     # denominator went 199 -> 200 and correct 197 -> 198.
                     old="Correct verdicts: 198/200",
                     new="Correct verdicts: 199/200"),
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
            # C-45: a verdict cell that its own row contradicts. The regex
            # names the COMPILES wording specifically, because re-stranding a
            # row also makes the generated block stale and that unrelated
            # finding must not be able to supply a false kill.
            Mutation("ungraded row re-stranded while it compiles (C-45)",
                     "corpora/real_roots/results.json",
                     r"but its recorded outcome says it COMPILES",
                     transform=restrand_ungraded_row),
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
        "check_cst_structure_lossless", [PY, f"{TOOLS}/check_cst_structure_lossless.py"],
        "pure",
        [
            Mutation("the roundtrip corpus drops out of the CST test's dune sandbox "
                     "while the test stays green",
                     "latex-parse/src/dune",
                     r"stanza missing `\(deps \(source_tree \.\./\.\./corpora/roundtrip\)\)`",
                     old="  (source_tree ../../corpora/roundtrip)\n",
                     new=""),
        ]),
    GateTest(
        "check_fix_integration_wired", [PY, f"{TOOLS}/check_fix_integration_wired.py"],
        "pure",
        [
            Mutation("E2E fix-pipeline test detached from `dune runtest`",
                     "latex-parse/src/dune",
                     r"fix-integration-wired\] FAIL: latex-parse/src/dune has no stanza "
                     r"for test_rule_fix_integration",
                     old="(test\n"
                         " (name test_rule_fix_integration)\n"
                         " (modules test_rule_fix_integration)\n"
                         " (libraries latex_parse_lib test_helpers unix)\n"
                         " (deps\n"
                         "  (source_tree ../../corpora/fixtures/v26_2_1)))\n"
                         "\n",
                     new=""),
        ]),
    GateTest(
        "check_fix_producer_ledger", [PY, f"{TOOLS}/check_fix_producer_ledger.py"],
        "pure",
        [
            Mutation("a shipped producer left out of SHIPPED_VERSIONS (TYPO-002)",
                             "scripts/tools/generate_fix_producer_ledger.py",
                             r"\[ledger\] ERROR: SHIPPED_VERSIONS drifts from code:.*"
                             r"In code but missing from SHIPPED_VERSIONS: \['TYPO-002'\]",
                             old='    "TYPO-002": "v26.2.1",\n',
                             new=''),
        ]),
    GateTest(
        "check_result_helpers", [PY, f"{TOOLS}/check_result_helpers.py"],
        "pure",
        [
            Mutation("ENC-004 hand-written as a raw 4-field result literal",
                     "latex-parse/src/validators_l0.ml",
                     r"validators_l0\.ml:\d+: raw result record literal at `\{ id = \"ENC-004\"",
                     old='Some (mk_result ~id:"ENC-004" ~severity:Warning ~message ~count:!cnt)',
                     new='Some { id = "ENC-004"; severity = Warning; message = message; count = !cnt }'),
        ]),
    GateTest(
        "check_code_quality", [PY, f"{TOOLS}/check_code_quality.py"],
        "pure",
        [
            Mutation("real_roots read goes broad again — the NameError swallow "
                     "that manufactured 'no measured_at_sha'",
                     "scripts/tools/check_project_state.py",
                     r"Python gate silent-except: FAIL: "
                     r"scripts/tools/check_project_state\.py:\d+: broad "
                     r"`except Exception` produces a fallback and continues",
                     old='        except (json.JSONDecodeError, OSError) as exc:\n'
                         '            findings.append(f"corpora/real_roots/results.json is unreadable: {exc}")\n'
                         '            sha, rr_data = "unreadable", None\n',
                     new='        except Exception:  # noqa: BLE001\n'
                         '            sha, rr_data = None, None\n'),
        ]),
    GateTest(
        "check_doc_refs", [PY, f"{TOOLS}/check_doc_refs.py"],
        "pure",
        [
            Mutation("docs index still points at the pre-rename "
                     "PROOF_TAXONOMY.md",
                     "docs/README.md",
                     r"\[doc-refs\] FAIL: docs/README\.md:\d+: broken link: "
                     r"\[PROOF_TAXONOMY\.md\]\(PROOF_TAXONOMY\.md\)",
                     old="[PROOF_CLASSES.md](PROOF_CLASSES.md)",
                     new="[PROOF_TAXONOMY.md](PROOF_TAXONOMY.md)"),
        ]),
    GateTest(
        "check_fix_safety_language", [PY, f"{TOOLS}/check_fix_safety_language.py"],
        "pure",
        [
            Mutation("the auto-fix channel called 'proven byte-safe' again (#537)",
                     "docs/CANDIDATE_FIXES.md",
                     r"\[fix-safety-language\] FAIL:.*"
                     r"docs/CANDIDATE_FIXES\.md:\d+: 'proven byte-safe' — the "
                     r"auto-fix channel is guard-gated, not proven",
                     old="Auto-fixes (Bucket A) are **guard-gated, not proven**, "
                         "and applied silently.",
                     new="Auto-fixes (Bucket A) are proven byte-safe and "
                         "applied silently."),
        ]),
    GateTest(
        "check_gates_meta", [PY, f"{TOOLS}/check_gates_meta.py"],
        "pure",
        [
            Mutation("a covered gate script stops validating anything "
                     "(validators glob narrowed back to validators.ml)",
                     "scripts/validate_catalogue.py",
                     r"validate_catalogue\.py: output does not contain "
                     r"PASS/FAIL marker.*only found \d+ runtime rule IDs",
                     old='SRC_DIR.glob("validators*.ml")',
                     new='SRC_DIR.glob("validators.ml")'),
        ]),
    GateTest(
        "check_memo_files", [PY, f"{TOOLS}/check_memo_files.py"],
        "pure",
        [
            Mutation("memo mandates a proof module nothing implements "
                     "(round-7 gap, no file and no alias)",
                     "specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md",
                     r"\[memo-files\] FAIL: 1 / \d+ memo-mandated paths have "
                     r"no implementation:\n[\s\S]*  §16\.2: "
                     r"proofs/DependencyInvalidationSound\.v",
                     old="- `proofs/DependencyInvalidation.v`",
                     new="- `proofs/DependencyInvalidationSound.v`"),
        ]),
    GateTest(
        "check_mli_doc_coverage", [PY, f"{TOOLS}/check_mli_doc_coverage.py"],
        "pure",
        [
            Mutation("new exported vals land with no ocamldoc (ratchet breach)",
                     "latex-parse/src/broker.mli",
                     r"\[mli-doc\] FAIL: broker\.mli:\d+: val "
                     r"'hedged_deadline_misses' has no ocamldoc "
                     r"\(\*\* \.\.\. \*\) comment\..*undocumented val\(s\) "
                     r"exceeds ceiling",
                     old="val hedge_fired_count : pool -> int",
                     new="val rescue_attempts : pool -> int\n"
                         "val hedged_deadline_misses : pool -> int\n"
                         "val worker_readiness_waits : pool -> int\n"
                         "val hedge_fired_count : pool -> int"),
        ]),
    GateTest(
        "check_regression_gates",
        [PY, f"{TOOLS}/check_regression_gates.py", "--skip-mutation"],
        "pure",
        [
            Mutation("STRUCT-003 reverted to its pre-P1.4 lowercase id (no_tabs)",
                     "latex-parse/src/validators_l0.ml",
                     r"validators_l0\.ml:\d+: lowercase rule id 'no_tabs'\. "
                     r"Use FAMILY-NNN convention",
                     old='  { id = "STRUCT-003"; run; languages = [] }',
                     new='  { id = "no_tabs"; run; languages = [] }'),
        ]),
    GateTest(
        "check_release_integrity", [PY, f"{TOOLS}/check_release_integrity.py"],
        "pure",
        [
            Mutation("a count in the GENERATED governance facts goes stale "
                     "(OPEN-082/083)",
                     "governance/project_facts.yaml",
                     r"Generated-file authenticity: FAIL: "
                     r"governance/project_facts\.yaml: differs from regenerated "
                     r"output.*proof_files_core",
                     transform=stale_governance_count),
        ]),
    GateTest(
        "check_repo_facts",
        [PY, f"{TOOLS}/check_repo_facts.py",
         "--facts", "governance/project_facts.yaml", "--repo", "."],
        "pure",
        [
            Mutation("docs/PROOFS.md publishes a theorem total that governance "
                     "contradicts (OPEN-082/083; the P1.8 finding this CHECKS row "
                     "was added for)",
                     "docs/PROOFS.md",
                     r"PROJECT FACTS DRIFT DETECTED.*docs/PROOFS\.md: expected one of "
                     r"[^\n]* for proofs\.theorem_count_reported",
                     transform=stale_theorem_total),
        ]),
    GateTest(
        "check_roadmap_facts", [PY, f"{TOOLS}/check_roadmap_facts.py"],
        "pure",
        [
            Mutation("superseded 61-doc differential matrix restated in the "
                     "roadmap (the line e3016b90 deleted)",
                     "docs/v27/ROADMAP.md",
                     r"ROADMAP\.md matrix false-READY: says 10, "
                     r"authoritative source says \d+",
                     old="### Honest current scope of the guarantee",
                     new="### Honest current scope of the guarantee\n\n"
                         "- **On `main` (v27.1.57):** **33 true-READY / "
                         "16 true-NOT-READY / 10 false-READY / "
                         "2 false-NOT-READY** (total 61)."),
        ]),
    GateTest(
        "check_rule_contracts", [PY, f"{TOOLS}/check_rule_contracts.py"],
        "pure",
        [
            Mutation("a log-dependent rule joins the hot-path Class C table while its "
                     "contract still says B (the PR #241 p1.2 runtime/contract binding)",
                     "latex-parse/src/execution_class.ml",
                     r"execution_class\.ml Class C not in contracts: \['LAY-005'\]",
                     old='let _class_c_ids =\n  [\n',
                     new='let _class_c_ids =\n  [\n    "LAY-005";\n'),
        ]),
    GateTest(
        "check_severity_drift", [PY, f"{TOOLS}/check_severity_drift.py"],
        "pure",
        [
            Mutation("DELIM-003 quietened to Warning at runtime while the "
                     "catalogue still says Error (drops it out of the T5 "
                     "fatal belt)",
                     "latex-parse/src/validators_l1.ml",
                     r"\[severity-drift\] FAIL: DELIM-003: spec=Error "
                     r"runtime=Warning",
                     old='~id:"DELIM-003" ~severity:Error',
                     new='~id:"DELIM-003" ~severity:Warning'),
        ]),
    GateTest(
        "check_version_labels", [PY, f"{TOOLS}/check_version_labels.py"],
        "pure",
        [
            Mutation("a maintained doc keeps last release's fix-producer stamp "
                     "(the '96 as of v27.0.67' drift)",
                     "specs/rules/README.md",
                     r"'Fix producers: 96 as of v27\.0\.67' stale "
                     r"\(current is \d+ as of v[\d.]+\)",
                     old="## Catalog Snapshot (rules_v3.yaml)",
                     new="## Catalog Snapshot (rules_v3.yaml)\n\n"
                         "- Fix producers (`produces_fix: true` in "
                         "`rule_contracts.yaml`): 96 as of\n"
                         "  v27.0.67."),
        ]),
    GateTest(
        "check_workflow_triggers", [PY, f"{TOOLS}/check_workflow_triggers.py"],
        "pure",
        [
            Mutation("unit-tests push un-scoped -- required context published twice "
                             "per commit (PR #531)",
                             ".github/workflows/unit-tests.yml",
                             r"DUPLICATED: 'unit-tests' is published by a workflow with an "
                             r"unfiltered `push:`",
                             old="  push:\n    branches: [main]\n",
                             new="  push:\n"),
            # Failure mode 4. Removing the exhaustion guard puts the loop back
            # in the shape that reported READY while nothing was: measured
            # 2026-09-13, all four live instances exited 0 with every probe
            # failing. The `warm` flag is what makes exhaustion observable, so
            # deleting the guard alone is the minimal, honest mutation.
            Mutation("rust-proxy warmup loop loses its exhaustion guard",
                     ".github/workflows/rust-proxy-smoke.yml",
                     r"SILENT-RETRY: .*rust-proxy-smoke.*Wait for service readiness",
                     old=GUARD_45,
                     new=""),
            # The `&& break` form is the one the FIRST draft of the detector
            # missed, on the very loop that prompted it. Pin it separately from
            # the bare-`break` form above so a regression to that draft is a
            # kill, not a silent narrowing.
            Mutation("setup-ocaml dep install reverts to the `&& break` "
                     "no-guard form",
                     ".github/actions/setup-ocaml-env/action.yml",
                     r"SILENT-RETRY: .*setup-ocaml-env.*Install opam dependencies",
                     old=OPAM_GUARDED_BLOCK,
                     new=OPAM_SILENT_BLOCK),
            # Failure mode 5. A retry that installs a different toolchain than
            # the attempt it replaces is worse than no retry.
            Mutation("the two setup-ocaml attempts drift apart",
                     ".github/actions/setup-ocaml-env/action.yml",
                     r"attempts have DRIFTED",
                     transform=drift_second_setup_ocaml),
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
            # C-43. baseline.strong_fatal/error_halt sat frozen at the round-7
            # values while the live set nearly doubled, because nothing read
            # them. They are gated now; this arm keeps them gated. The regex
            # names the sub-count message specifically so the pre-existing
            # total check cannot supply a false kill.
            Mutation("baseline sub-count drifted off the live split",
                     "corpora/false_ready/manifest.json",
                     r"baseline\.error_halt=\d+ disagrees with \d+ live fixtures",
                     transform=drift_baseline_split),
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
    # OPEN-055: proof.yml hosts the REQUIRED `proof-ci` context and runs
    # check_proof_substance.py, but this coverage check only knew about
    # spec-drift.yml and ci.yml — so a gate wired into required CI still read
    # as "running nowhere". Same blind-spot shape as the gate it guards.
    pf_path = REPO / ".github/workflows/proof.yml"
    pf = pf_path.read_text() if pf_path.is_file() else ""
    invoked = set(re.findall(r"(check_[a-z_]+\.py)", sd + ci + pf))
    # The script is the first cmd element ending in .py, NOT cmd[-1]: gates that
    # need arguments (check_repo_facts --facts ..., check_regression_gates
    # --skip-mutation) put flags after it, and keying on the last element then
    # silently mapped the gate to "--skip-mutation" and reported BOTH that the
    # real gate was uncovered AND that a phantom gate ran nowhere.
    def _script(g):
        for a in g.cmd:
            if str(a).endswith(".py"):
                return Path(a).name
        return Path(g.cmd[-1]).name

    covered = {_script(g) for g in REGISTRY}
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
                    mode = m.target.stat().st_mode
                    tmp.write_bytes(bfile.read_bytes())
                    os.chmod(tmp, mode)
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
