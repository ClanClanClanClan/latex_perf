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


def prov_stale_build(text: str) -> str:
    """Same engine source, different binary — the STALE BUILD case (C-68).

    After C-68 a cli_sha256 mismatch is a failure only when latex-parse/src is
    UNCHANGED since the measurement, because identical source reproduces the
    hash byte-for-byte while a comment-only edit moves it. This mutation
    therefore has to set BOTH fields: the source anchor to HEAD's actual tree,
    and the binary hash to something impossible. Setting only the hash would
    now (correctly) produce a note rather than a kill.

    Since C-72 it also sets cli_build_root to this checkout's fingerprint: the
    same source built in another checkout directory legitimately gives another
    hash, so the failure arm fires only for a build made in this checkout.

    Binary level: the arm is inert without a built CLI, which is the whole of
    OPEN-101.
    """
    import json as _json
    import subprocess as _sp
    d = _json.loads(text)
    tgt = d.get("provenance", d)
    tgt["src_tree_sha"] = _sp.run(
        ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
        capture_output=True, text=True).stdout.strip()
    tgt["cli_sha256"] = "0" * 64
    # And claim THIS platform produced it: a hash from another platform is a
    # note, not a kill (C-64), so without this the mutation would not fire on
    # the ubuntu CI runner.
    from _measurement_provenance import cli_platform as _plat
    tgt["cli_platform"] = _plat()
    # And claim THIS checkout built it: a hash built in another checkout
    # directory is a note, not a kill, because the build embeds absolute paths
    # (C-72). Without this the mutation would only produce a note.
    from _measurement_provenance import build_root_fingerprint as _root
    tgt["cli_build_root"] = _root(REPO)
    return _json.dumps(d, indent=2)



def allowlist_inject_implicated(text: str) -> str:
    """Slip an implicated rule into the default auto-fix set (OPEN-112).

    A transform, not an exact-string anchor: the list's content changes as the
    meaning review admits rules, and the mutation must keep landing."""
    new, n = re.subn(r'(let default_allowlist\s*=\s*\[)', r'\1 "CHEM-005";',
                     text, count=1)
    assert n == 1, "default_allowlist anchor not found"
    return new


def review_flip_first_safe(text: str) -> str:
    """Flip the first SAFE-reviewed rule to UNSAFE while it stays allow-listed."""
    import json as _json
    d = _json.loads(text)
    for v in d["rules"].values():
        if v.get("verdict") == "safe":
            v["verdict"] = "unsafe"
            break
    else:
        raise AssertionError("no safe rule to flip")
    return _json.dumps(d, indent=1, ensure_ascii=False)


def review_drop_refutations(text: str) -> str:
    """Keep every verdict but delete the adversarial refutation evidence."""
    import json as _json
    d = _json.loads(text)
    for v in d["rules"].values():
        v["refutation"] = None
    return _json.dumps(d, indent=1, ensure_ascii=False)


def afr_scope_default(text: str) -> str:
    """Claim the pinned artefact measured the allow-list, not the full fixer."""
    import json as _json
    d = _json.loads(text)
    d.setdefault("provenance", {})["fixer_scope"] = "default"
    return _json.dumps(d, indent=2, ensure_ascii=False)

def prov_stale_engine_tree(text: str) -> str:
    """Claim the artefact was measured against a different engine source tree.

    The platform-independent anchor added for OPEN-101/C-64. It is the arm that
    can actually run in CI — `cli_sha256` compares a macOS arm64 Mach-O against
    an ubuntu-22.04 build and can never agree off the producing machine — so it
    is the one that most needs a kill-test of its own.
    """
    import json as _json
    d = _json.loads(text)
    tgt = d.get("provenance", d)
    tgt["src_tree_sha"] = "0" * 40
    return _json.dumps(d, indent=2)


def prov_unresolvable_sha(text: str) -> str:
    """Point an artefact's provenance at a sha no clone can resolve.

    This is the arm that was live in CI for the whole life of both staleness
    ratchets (C-58). `actions/checkout` defaults to a one-commit clone, in which
    `git rev-list <sha>..HEAD` exits 128 for ANY provenance sha; the gates read
    `if rc == 0 and isdigit():` with no else, so the ratchet silently skipped on
    every PR ever run. The sha below is well-formed hex that is not a commit, so
    `git cat-file -e` fails exactly as it does in a shallow clone — reproducing
    CI's condition on a full local clone.

    The sibling arm (a RESOLVABLE sha that is not an ancestor, which returns a
    meaningless count rather than an error) is not mutation-tested here because
    no sha is portably guaranteed to be present-but-unreachable in every clone.
    It was verified live on 2026-09-20 against the real defect: five artefacts
    stamped 52d850ef and the fixed gate reported "is NOT an ancestor of HEAD",
    where the old one had read "2 commits behind, limit 5" and passed. Both arms
    sit in the same function, so this mutation proves it is reached.
    """
    import json as _json
    d = _json.loads(text)
    tgt = d.get("provenance", d)
    tgt["measured_at_sha"] = "dead" * 10  # 40 hex chars, not an object
    return _json.dumps(d, indent=2)


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


def drop_one_passes_count(text: str) -> str:
    """OPEN-119. Strip `pdflatex_passes` from one row of a results artefact
    whose protocol claims the multi-pass protocol wholesale (no APPLIED-TO
    clause). The claim-provenance check (C-28) must see that the published
    protocol no longer describes every row. It was written for results.json
    alone; this proves the sample-3 arm of the loop is reached."""
    d = json.loads(text)
    row = next(r for r in d["docs"] if r.get("pdflatex_passes"))
    del row["pdflatex_passes"]
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


def kernel_drop_topmark(text: str) -> str:
    """The 2026-09-27 review's first missing name, removed from the committed
    kernel file (count kept consistent, so only the completeness arm fires)."""
    d = json.loads(text)
    assert "topmark" in d["names"], "kernel file drifted; update registry"
    del d["names"]["topmark"]
    d["count"] = len(d["names"])
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


def kernel_uncover_one(text: str) -> str:
    """TeX's hash count reporting one name outside the kernel's candidates."""
    d = json.loads(text)
    assert d["coverage"]["uncovered"] == 0, "kernel file drifted; update registry"
    d["coverage"]["uncovered"] = 1
    d["coverage"]["covered"] -= 1
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


def contract_pass4_uncover_one(text: str) -> str:
    """Re-review 2: TeX's count on pass 4 (after two failing passes and one
    that completed, the last pass the protocol can grade) reporting one name
    outside a complete contract's universe."""
    d = json.loads(text)
    hit = [x for x in d["coverage_passes"] if x["history"] == "FFS"
           and x["env"] == "forced" and x["jobname"] == "job"]
    assert len(hit) == 1 and hit[0]["uncovered"] == 0, "contract drifted; update registry"
    hit[0]["uncovered"] = 1
    hit[0]["covered"] -= 1
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


def contract_drop_grading_pass3(text: str) -> str:
    """Re-review 2: the count of pass 3 after F S under the graders'
    environment silently missing."""
    d = json.loads(text)
    n = len(d["coverage_passes"])
    d["coverage_passes"] = [x for x in d["coverage_passes"] if not (
        x["history"] == "FS" and x["env"] == "grading" and x["jobname"] == "job")]
    assert len(d["coverage_passes"]) == n - 1, "contract drifted; update registry"
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


KERNEL_FILE = "corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json"


def strict_family_one_disagrees(text: str) -> str:
    """ADR-012 M2: a Runs constructor whose probe family has one probe the
    oracle disagrees with."""
    d = json.loads(text)
    f = d["by_family"]["R_script_double"]
    assert f["agree"] == f["n"] >= 1, "rule_probes drifted; update registry"
    f["agree"] -= 1
    return json.dumps(d, indent=1) + "\n"


def strict_differential_one_disagreement(text: str) -> str:
    d = json.loads(text)
    assert d["summary"]["disagree"] == 0, "differential drifted; update registry"
    d["summary"]["disagree"] = 1
    d["summary"]["agree"] -= 1
    return json.dumps(d, indent=1) + "\n"


def _first_admitted(d: dict, text_ok: bool = False) -> str:
    for n, h in sorted(d["signatures"].items()):
        if not text_ok or not isinstance(h["text"], list):
            return n
    raise AssertionError("signature file drifted; update registry")


def strict_admitted_not_inert(text: str) -> str:
    """C-85 / R-INERT: an admitted name whose recorded meaning is a
    conditional primitive."""
    d = json.loads(text)
    d["meanings"][_first_admitted(d)] = "\\iftrue"
    return json.dumps(d, indent=1) + "\n"


def strict_admitted_transparent(text: str) -> str:
    """C-85: an admitted name that is transparent after a $ in display math
    (its display-follower grade compiles)."""
    d = json.loads(text)
    d["evidence"][_first_admitted(d)]["D-FOLLOW-DOLLAR"] = [0, True, "", None]
    return json.dumps(d, indent=1) + "\n"


def strict_admitted_global_resource(text: str) -> str:
    """C-85: an admitted name that fails under repetition (\\tableofcontents)."""
    d = json.loads(text)
    d["evidence"][_first_admitted(d, text_ok=True)]["R-TEXT"] = [
        1, False, "! No room for a new \\write .", 16]
    return json.dumps(d, indent=1) + "\n"


def strict_admitted_family_missing(text: str) -> str:
    d = json.loads(text)
    d["evidence"][_first_admitted(d)].pop("D-FOLLOW-CHAR")
    return json.dumps(d, indent=1) + "\n"


def strict_interleave_disagrees(text: str) -> str:
    d = json.loads(text)
    r = d["interleaving"]["rounds"]
    assert r and r[-1]["disagree"] == 0, "signature file drifted; update registry"
    r[-1]["disagree"] = 1
    return json.dumps(d, indent=1) + "\n"


def strict_matrix_cell_dropped(text: str) -> str:
    """C-85 / check 7: no probe exercises `$` in display math followed by a
    character."""
    d = json.loads(text)
    cell = "display|dollar|char|-"
    before = len(d["probes"])
    d["probes"] = [r for r in d["probes"] if cell not in r.get("branches", [])]
    assert len(d["probes"]) < before, "rule_probes drifted; update registry"
    return json.dumps(d, indent=1) + "\n"


def strict_bound_scope_dropped(text: str) -> str:
    d = json.loads(text)
    assert "not over L_S0" in d["summary"]["upper_bound_95"]["scope"], \
        "differential drifted; update registry"
    d["summary"]["upper_bound_95"]["scope"] = "the disagreement rate"
    return json.dumps(d, indent=1) + "\n"


def strict_signature_candidate_dropped(text: str) -> str:
    """A rejected candidate silently removed: the candidate set no longer is
    the selection rule's."""
    d = json.loads(text)
    assert d["rejected"], "signature file drifted; update registry"
    d["rejected"].pop(sorted(d["rejected"])[0])
    return json.dumps(d, indent=1) + "\n"


# ---- ADR-012 step 2, slice A: the one-argument commands ---------------------

def _first_arg(d: dict, runs_text: bool = False) -> str:
    for n, h in sorted(d["arg_signatures"].items()):
        if not runs_text or h["text"][0] == "run":
            return n
    raise AssertionError("argument-signature file drifted; update registry")


def strict_capacity_pair_unprobed(text: str) -> str:
    """C-94: the first frame-kind pair's at-bound document disagrees."""
    d = json.loads(text)
    assert d["pairs"] and d["pairs"][0]["at"]["oracle"][0] == 0, "capacity drifted; update registry"
    d["pairs"][0]["at"]["oracle"][0] = 1
    return json.dumps(d, indent=1) + "\n"


def strict_capacity_overflow_early(text: str) -> str:
    """C-94: pdfTeX overflows long before the account's window: the model
    under-counts a kind (the reviewer's defect, measured)."""
    d = json.loads(text)
    steps = d["pairs"][0]["overflow_steps"]
    ok = dict(steps[0])
    ok.update(target=127, oracle=[0, True, "", None])
    bad = dict(steps[0])
    bad.update(target=128, oracle=[1, False, "! TeX capacity exceeded, sorry [grouping levels=255].", 3])
    d["pairs"][0]["overflow_steps"] = [ok, bad] + steps
    return json.dumps(d, indent=1) + "\n"


def strict_capacity_kind_dropped(text: str) -> str:
    """C-94: every pair holding a formula is dropped (the probes never
    stacked the frame kind the defect was in)."""
    d = json.loads(text)
    keep = [r for r in d["pairs"]
            if not any(str(r.get(k, "")).startswith(("inline.", "display."))
                       for k in ("below", "above"))]
    assert len(keep) < len(d["pairs"]), "capacity drifted; update registry"
    d["pairs"] = keep
    d["frame_pairs"]["n"] = len(keep)
    return json.dumps(d, indent=1) + "\n"


def strict_arg_groups_dropped(text: str) -> str:
    """C-94: an admitted command's text run behaviour without its groups."""
    d = json.loads(text)
    n = _first_arg(d, runs_text=True)
    d["arg_signatures"][n]["text"] = d["arg_signatures"][n]["text"][:3]
    return json.dumps(d, indent=1) + "\n"


def strict_reuse_local(text: str) -> str:
    """LOW-2: a reuse source that is a local path, not a committed file."""
    d = json.loads(text)
    d["reuse"] = {"grades_reused": 1, "sources": [
        {"file": "/private/tmp/lp/rule_probes.json", "sha256": "0" * 64, "records": 1}]}
    return json.dumps(d, indent=1) + "\n"


def strict_inert_expl3(text: str) -> str:
    """C-96: an admitted name whose code is expl3 reaching \\immediate. The
    reading of version 4 (`\\\\([A-Za-z@]+)`) took `\\lpq_t:n` as `\\lpq`,
    whose meaning here is harmless: the walk stopped there silently."""
    d = json.loads(text)
    n = _first_admitted(d)
    d["meanings"][n] = "macro:->\\lpq_t:n {x}"
    d["meanings"]["lpq_t:n"] = "\\immediate"
    d["meanings"]["lpq"] = "\\relax"
    return json.dumps(d, indent=1) + "\n"


def strict_capacity_pair_forged(text: str) -> str:
    """M-1: drop a pair AND decrement frame_pairs.n (consistent forgery the
    pure count check passes)."""
    d = json.loads(text)
    d["pairs"] = d["pairs"][1:]
    d["frame_pairs"]["n"] -= 1
    return json.dumps(d, indent=1) + "\n"


def strict_capacity_peak_forged(text: str) -> str:
    d = json.loads(text)
    d["pairs"][0]["at"]["peak"] -= 1
    return json.dumps(d, indent=1) + "\n"


def strict_memory_bound_forged(text: str) -> str:
    """M-2: a memory worst case whose recorded account is not the model's."""
    d = json.loads(text)
    mb = d["capacity"]["memory_bound"]
    n = sorted(k for k in mb if k != "filler")[0]
    w = sorted(mb[n])[0]
    mb[n][w]["at"]["mem"] -= 1
    return json.dumps(d, indent=1) + "\n"


def strict_arg_groups_forged(text: str) -> str:
    """M-2: a consistent forged g, in the signature AND in the stored summary
    of stage G (the gate re-derives g from the graded depths)."""
    d = json.loads(text)
    n = _first_arg(d, runs_text=True)
    d["arg_signatures"][n]["text"][3] += 1
    d["capacity"]["groups"][n]["text"] += 1
    return json.dumps(d, indent=1) + "\n"


def strict_name_cost_forged(text: str) -> str:
    """C-98: an admitted name whose cost is lower than its memory documents
    give."""
    d = json.loads(text)
    n = sorted(d["signatures"])[0]
    d["signatures"][n]["cost"] = 1
    return json.dumps(d, indent=1) + "\n"


def strict_inert_definition(text: str) -> str:
    """LOW-4 of the round-2 review: an admitted name whose code redefines
    another name (\\gdef\\mbox{x}) must not be inert."""
    d = json.loads(text)
    n = _first_admitted(d)
    d["meanings"][n] = "macro:->\\gdef \\mbox {x}"
    d["meanings"].setdefault("gdef", "\\gdef")
    return json.dumps(d, indent=1) + "\n"


def strict_arg_not_inert(text: str) -> str:
    """R-INERT on an admitted one-argument command's recorded meaning."""
    d = json.loads(text)
    d["meanings"][_first_arg(d)] = "\\iftrue"
    return json.dumps(d, indent=1) + "\n"


def strict_arg_nest_overflows(text: str) -> str:
    """C-86 for arguments: a command nested to the brace bound overflows
    TeX's grouping levels (\\fbox, \\underline were rejected for this)."""
    d = json.loads(text)
    d["evidence"][_first_arg(d, runs_text=True)]["A-R-NEST-TEXT"] = [
        1, False, "! TeX capacity exceeded, sorry [grouping levels=255].", 205]
    return json.dumps(d, indent=1) + "\n"


def strict_arg_follower_missing(text: str) -> str:
    d = json.loads(text)
    d["evidence"][_first_arg(d)].pop("A-D-FOLLOW")
    return json.dumps(d, indent=1) + "\n"


def strict_arg_both_kinds(text: str) -> str:
    """contract_wf: a name with a phase-1 signature also given an argument
    signature."""
    d = json.loads(text)
    p1 = json.loads((REPO / "corpora/contracts/strict/article-s0-signatures.json").read_text())
    n = sorted(p1["signatures"])[0]
    d["arg_signatures"][n] = d["arg_signatures"][_first_arg(d)]
    return json.dumps(d, indent=1) + "\n"


def strict_arg_candidate_dropped(text: str) -> str:
    d = json.loads(text)
    assert d["selection"]["names"], "argument-signature file drifted; update registry"
    d["selection"]["names"].pop(0)
    return json.dumps(d, indent=1) + "\n"


def strict_arg_context_disagrees(text: str) -> str:
    """Phase-1 names inside an argument's mode (an hbox): one disagreement."""
    d = json.loads(text)
    assert d["context"].get("disagree") == 0, "argument-signature file drifted"
    d["context"]["disagree"] = 1
    return json.dumps(d, indent=1) + "\n"


def strict_rules_other_arg_file(text: str) -> str:
    d = json.loads(text)
    assert d.get("arg_signatures_sha256"), "rule_probes drifted; update registry"
    d["arg_signatures_sha256"] = "0" * 64
    return json.dumps(d, indent=1) + "\n"


def strict_scan_cell_dropped(text: str) -> str:
    """The argument scanner's matrix: no probe closes the outermost argument
    of a long command (scan|close|k1|nosh|noou)."""
    d = json.loads(text)
    cell = "scan|close|k1|nosh|noou"
    hit = 0
    for r in d["probes"]:
        if cell in r.get("branches", []):
            # only this cell goes: whole probes would uncover other cells too
            r["branches"] = [b for b in r["branches"] if b != cell]
            hit += 1
    assert hit, "rule_probes drifted; update registry"
    return json.dumps(d, indent=1) + "\n"


def strict_arg_family_dropped(text: str) -> str:
    """A live slice-A constructor (R_close_arg) without its probe family."""
    d = json.loads(text)
    assert "R_close_arg" in d["by_family"], "rule_probes drifted; update registry"
    d["by_family"].pop("R_close_arg")
    return json.dumps(d, indent=1) + "\n"


def strict_faithful_is_decide(text: str) -> str:
    """The final review's MEDIUM-1 redefinition, verbatim: Faithful's body
    becomes `oracle_ok (render d) <-> decide C d = ProvenReady` and the
    corollary's proof `symmetry; apply HF; exact Hs` -- the decide=decide
    tautology. coqc printed the same pinned statement and Print Assumptions
    stayed Closed; only the body pin can see it."""
    old_body = "(oracle_ok (render d) <-> Runs C init (flatten_doc d) Compiles)."
    old_proof = ("  destruct (strict_decider_exact C d Hs) as [Hready _].\n"
                 "  rewrite Hready. symmetry. apply HF. exact Hs.\n")
    assert text.count(old_body) == 1 and text.count(old_proof) == 1, \
        "Bridge.v drifted; update registry"
    return (text.replace(old_body, "(oracle_ok (render d) <-> decide C d = ProvenReady).")
                .replace(old_proof, "  symmetry. apply HF. exact Hs.\n"))


# ---- check_strict_bytes (ADR-012 M2 phase 2) --------------------------------

def bytes_family_one_disagrees(text: str) -> str:
    """A reader constructor whose probe family has one document the oracle
    disagrees with."""
    d = json.loads(text)
    f = d["by_family"]["LL_comment"]
    assert f["agree"] == f["n"] >= 1, "bytes_probes drifted; update registry"
    f["agree"] -= 1
    return json.dumps(d, indent=1) + "\n"


def bytes_other_arg_file(text: str) -> str:
    """Slice A: the byte-level evidence ran another argument-signature file."""
    d = json.loads(text)
    assert d.get("arg_signatures_sha256"), "bytes_probes drifted; update registry"
    d["arg_signatures_sha256"] = "0" * 64
    return json.dumps(d, indent=1) + "\n"


def bytes_differential_one_disagreement(text: str) -> str:
    d = json.loads(text)
    assert d["summary"]["disagree"] == 0, "bytes_differential drifted; update registry"
    d["summary"]["disagree"] = 1
    d["summary"]["agree"] -= 1
    return json.dumps(d, indent=1) + "\n"


def bytes_differential_below_floor(text: str) -> str:
    d = json.loads(text)
    assert d["summary"]["graded"] >= 3000, "bytes_differential drifted; update registry"
    d["summary"]["graded"] = d["summary"]["agree"] = 2999
    return json.dumps(d, indent=1) + "\n"


def bytes_near_miss_decided(text: str) -> str:
    """A near-miss outside the fragment that the decider gave a verdict."""
    d = json.loads(text)
    near = d["by_family"]["L0-NEAR"]
    assert near["n"] == 0, "bytes_probes drifted; update registry"
    near["n"] = near["agree"] = 1
    return json.dumps(d, indent=1) + "\n"


def bytes_reader_cell_dropped(text: str) -> str:
    """No agreeing probe exercises the reader cell S|comment."""
    d = json.loads(text)
    n = 0
    for r in d["documents"]:
        if "S|comment" in r.get("lex_branches", []):
            r["lex_branches"].remove("S|comment")
            n += 1
    assert n >= 1, "bytes_probes drifted; update registry"
    return json.dumps(d, indent=1) + "\n"


def bytes_tree_consistency_differs(text: str) -> str:
    d = json.loads(text)
    tc = d["summary"]["tree_bytes_consistency"]
    assert tc["agree"] == tc["checked"] >= 1, "bytes_probes drifted; update registry"
    tc["agree"] -= 1
    return json.dumps(d, indent=1) + "\n"


def bytes_explain_mismatch(text: str) -> str:
    d = json.loads(text)
    assert d["summary"]["explain_mismatches"] == 0, "bytes_differential drifted"
    d["summary"]["explain_mismatches"] = 1
    return json.dumps(d, indent=1) + "\n"


def lexical_catcode_changed(text: str) -> str:
    """The lexical contract no longer what the evidence ran (~ made other)."""
    d = json.loads(text)
    assert d["catcodes"][126] == 13, "lexical contract drifted; update registry"
    d["catcodes"][126] = 12
    return json.dumps(d, indent=1, sort_keys=True) + "\n"


def lexical_structural_drift(text: str) -> str:
    """A structural name that is not the one Syntax.v renders."""
    d = json.loads(text)
    assert d["structural"]["par"] == "par", "lexical contract drifted; update registry"
    d["structural"]["par"] = "parr"
    return json.dumps(d, indent=1, sort_keys=True) + "\n"


def lexical_endline_not_eol(text: str) -> str:
    """\\endlinechar's byte no longer of category 5: LL_end/LL_nullcs could
    then be reached inside the fragment."""
    d = json.loads(text)
    assert d["catcodes"][13] == 5, "lexical contract drifted; update registry"
    d["catcodes"][13] = 12
    return json.dumps(d, indent=1, sort_keys=True) + "\n"


def bytes_record_agree_flipped(text: str) -> str:
    """The bytes PR's review, LOW-3: one graded record's `agree` flipped, the
    summary untouched. A gate that trusts the summary passes this."""
    d = json.loads(text)
    r = next(r for r in d["documents"] if r.get("class") == "E1")
    assert r["agree"] is True, "bytes_probes drifted; update registry"
    r["agree"] = False
    return json.dumps(d, indent=1) + "\n"


def bytes_record_oracle_changed(text: str) -> str:
    """A READY record whose stored oracle tuple no longer compiles (rc 1),
    its `agree` and the summary untouched."""
    d = json.loads(text)
    r = next(r for r in d["documents"] if r.get("class") == "READY")
    assert r["oracle"][0] == 0 and r["agree"] is True, "bytes_differential drifted"
    r["oracle"][0] = 1
    return json.dumps(d, indent=1) + "\n"


def bytes_e0_record_has_line(text: str) -> str:
    """LOW-1's regression: an E0 record carrying a line pdfTeX never reports."""
    d = json.loads(text)
    r = next(r for r in d["documents"] if r.get("class") == "E0")
    assert r["model"][3] is None, "bytes_probes drifted; update registry"
    r["model"][3] = 4
    return json.dumps(d, indent=1) + "\n"


def faithful_bytes_is_decide(text: str) -> str:
    """The OPEN-121 MEDIUM-1 shape on bytes: FaithfulBytes' iff states the
    decider instead of Runs (the corollary would be decide = decide)."""
    old = "(oracle_ok b <-> Runs (bc_kernel C) init (toks_of ks) Compiles)."
    assert text.count(old) == 1, "BridgeBytes.v drifted; update registry"
    return text.replace(old, "(oracle_ok b <-> decide_bytes C b = ProvenReady).")


REGISTRY = [
    GateTest(
        "check_strict_kernel",
        [PY, f"{TOOLS}/check_strict_kernel.py", "--repo", "."],
        "pure",
        [
            # The review rule of design §C.3: every Runs constructor cites
            # its probe family.
            Mutation("a Runs constructor loses its probe tag",
                     "proofs/Strict/Semantics.v",
                     r"FAIL Semantics\.v: constructor R_close_top has no",
                     old="(* probe S0/R_close_top: }",
                     new="(* S0/R_close_top: }"),
            Mutation("a probe family has a disagreeing probe",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL rule_probes: family R_script_double: 1 of",
                     transform=strict_family_one_disagrees),
            Mutation("the differential reports a disagreement",
                     "corpora/strict_s0/differential_v4.json",
                     r"FAIL differential: 1 disagreement",
                     transform=strict_differential_one_disagreement),
            # C-85: the published bound must be one over the generator's
            # distribution, not over L_S0.
            Mutation("the differential's bound drops its scope",
                     "corpora/strict_s0/differential_v4.json",
                     r"FAIL differential: the upper bound does not state",
                     transform=strict_bound_scope_dropped),
            # C-85 / R-INERT: a non-inert name admitted.
            Mutation("an admitted name is a conditional (not inert)",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' is not inert: conditional",
                     transform=strict_admitted_not_inert),
            # C-85: a name transparent to the display-$ look-ahead admitted.
            Mutation("an admitted name is transparent after a display $",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' is not a bad display-\$ follower",
                     transform=strict_admitted_transparent),
            # C-85: a name consuming a global resource admitted.
            Mutation("an admitted name fails under repetition",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' does not compile under R-TEXT",
                     transform=strict_admitted_global_resource),
            Mutation("an admitted name lacks a display-follower probe",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' lacks probe families",
                     transform=strict_admitted_family_missing),
            Mutation("the last interleaving round disagrees",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: no interleaving round with 0 disagreements",
                     transform=strict_interleave_disagrees),
            # C-85 / check 7: a follower class of a look-ahead unprobed.
            Mutation("a branch-matrix cell is not exercised",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL branch matrix: cell display\|dollar\|char\|- is not",
                     transform=strict_matrix_cell_dropped),
            # check 7 derives the look-ahead tokens from Runs: a rule that
            # starts reading the next token must bring its follower cells.
            Mutation("a Runs rule starts reading the next token",
                     "proofs/Strict/Semantics.v",
                     r"FAIL branch matrix: cell \w+\|end\|char\|- is not",
                     old="    Runs C (mkState fs true p) (TEnd :: rest) Compiles",
                     new="    Runs C (mkState fs true p) (TEnd :: TChar c :: rest) Compiles"),
            # C-86: the capacity bounds dropped from membership.
            Mutation("membership no longer requires the capacity bounds",
                     "proofs/Strict/Decide.v",
                     r"FAIL Decide\.v: in_strict_doc no longer requires `bounded`",
                     old="  in_strict_toks C (flatten_doc d) /\\ bounded C (flatten_doc d) = true.",
                     new="  in_strict_toks C (flatten_doc d)."),
            # C-94: the capacity account through a proxy again (a formula
            # counted as no group, the reviewer's \mbox{$ ... $} shape).
            Mutation("the group account stops counting formulas (C-94)",
                     "proofs/Strict/Decide.v",
                     r"FAIL Decide\.v: frame_groups is not the pinned account",
                     old="  | FArg _ _ g _ _ => g\n  | _ => 1\n",
                     new="  | FArg _ _ g _ _ => g\n  | FShift _ _ _ => 0\n  | _ => 1\n"),
            Mutation("the group bound is taken on the initial state only (C-94)",
                     "proofs/Strict/Decide.v",
                     r"FAIL Decide\.v: bounded is not the pinned account",
                     old="Nat.leb (peak C init ts) max_groups\n",
                     new="Nat.leb (groups (s_frames init)) max_groups\n"),
            # C-94: a frame-kind pair of the model not probed at the bound.
            Mutation("a frame-kind pair is not probed at the bound (C-94)",
                     "corpora/strict_s0/capacity.json",
                     r"FAIL corpora/strict_s0/capacity\.json: pair \S+ not probed at the bound",
                     transform=strict_capacity_pair_unprobed),
            Mutation("pdfTeX overflows where the account does not predict (C-94)",
                     "corpora/strict_s0/capacity.json",
                     r"FAIL corpora/strict_s0/capacity\.json: pair \S+ pdfTeX overflows at",
                     transform=strict_capacity_overflow_early),
            Mutation("a frame kind of the model is in no probed pair (C-94)",
                     "corpora/strict_s0/capacity.json",
                     r"FAIL corpora/strict_s0/capacity\.json: no probed pair has a frame of kind",
                     transform=strict_capacity_kind_dropped),
            # C-94: an argument command without its measured TeX groups.
            Mutation("an argument command's groups are not measured (C-94)",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: '.*' runs in text without its measured TeX groups",
                     transform=strict_arg_groups_dropped),
            # M-2 of the round-2 review: g re-derived from stage G's grades.
            Mutation("a consistent forged g (M-2)",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: '.*'s groups in text \(\d+\) are not what stage G",
                     transform=strict_arg_groups_forged),
            # LOW-4 of the round-2 review: a definition in a closure.
            Mutation("R-INERT passes a closure that redefines a name (LOW-4)",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' is not inert: expansion reaches \\gdef",
                     transform=strict_inert_definition),
            # C-98: a name's memory cost below its measurement.
            Mutation("a name's memory cost is forged low (C-98)",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: '.*'s cost 1 is not what its memory documents give",
                     transform=strict_name_cost_forged),
            Mutation("the memory bound is dropped from membership (C-98)",
                     "proofs/Strict/Decide.v",
                     r"FAIL Decide\.v: bounded is not the pinned account",
                     old="\n  && Nat.leb (mem C ts) max_mem.",
                     new="."),
            # LOW-2 of the C-94 review: grades reused from a local file.
            Mutation("grades are reused from a file nobody else can read (LOW-2)",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL rule_probes: grades reused from /private/tmp/\S+ which is not a committed",
                     transform=strict_reuse_local),
            # C-96: R-INERT must read an expl3 name whole (\lpq_t:n is not \lpq).
            Mutation("R-INERT reads an expl3 name as its letters (C-96)",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' is not inert: expansion reaches \\immediate",
                     transform=strict_inert_expl3),
            Mutation("the signature candidates are not the selection rule's",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: candidate set differs",
                     transform=strict_signature_candidate_dropped),
            # A semantics change without re-running the evidence.
            Mutation("the committed extraction changes under the evidence",
                     "latex-parse/strict/strict_kernel_extracted.ml",
                     r"FAIL rule_probes: ran another extraction",
                     old="[@@@warning \"-a\"]\n",
                     new="[@@@warning \"-a\"]\n\nlet _lp_kill = ()\n"),
            # OPEN-121 final review MEDIUM-1: Faithful redefined as the
            # decider (a tautology) under an unchanged pinned statement.
            Mutation("Faithful is redefined as the decider (review repro)",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: Faithful's body is not the pinned one.*"
                     r"FAIL Bridge\.v: Faithful's body does not mention Runs.*"
                     r"FAIL Bridge\.v: Faithful's body mentions \['decide'\]",
                     transform=strict_faithful_is_decide),
            Mutation("Faithful's body conjoins the decider to Runs",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: Faithful's body mentions \['decide'\]",
                     old="Runs C init (flatten_doc d) Compiles).",
                     new="Runs C init (flatten_doc d) Compiles /\\ "
                         "decide C d = ProvenReady)."),
            Mutation("Bridge.v shadows a name Faithful reads",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: defines more than Faithful",
                     old="Definition Faithful (oracle_ok",
                     new="Local Notation flatten_doc := flatten_doc.\n"
                         "Definition Faithful (oracle_ok"),
            # OPEN-121 re-review MEDIUM-1, the repro verbatim: a shadow module
            # on the Require line. coqc's Print still showed Semantics.Runs
            # and a line-start definer scan never looked there.
            Mutation("a shadow Module Semantics on Bridge.v's Require line",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: defines more than Faithful: "
                     r"\[\('Module', 'Semantics'\), \('Definition', 'Runs'\)",
                     old="From LaTeXPerfectionist.Strict Require Import Syntax "
                         "Contract Semantics Decide.\n",
                     new="From LaTeXPerfectionist.Strict Require Import Syntax "
                         "Contract Semantics Decide. Module Semantics. Definition "
                         "Runs (C : contract) (s : Semantics.state) (ts : list tok) "
                         "(o : outcome) : Prop := run C s ts = Some o. End "
                         "Semantics. Import Semantics.\n"),
            # OPEN-121 re-review 2 (HIGH-1), mutant A: a control prefix hid
            # the shadow's keyword from a sentence-start scan.
            Mutation("a Time-prefixed shadow in_strict_doc in Bridge.v",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: defines more than Faithful: "
                     r"\[\('prefix', 'Time'\), \('Definition', 'in_strict_doc'\)\]",
                     old="Corollary strict_ready_iff_pdflatex :",
                     new="Time Definition in_strict_doc (C : contract) (d : doc) : "
                         "Prop := False.\n\nCorollary strict_ready_iff_pdflatex :"),
            # Mutant B: a comment holding a string with a comment delimiter.
            # Coq sees two comments and a Definition; the kill regex needs the
            # LEXER to see the Definition (the no-quote rule alone would not
            # print it).
            Mutation("a shadow in_strict_doc between two comment-strings",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: defines more than Faithful: "
                     r"\[\('Definition', 'in_strict_doc'\)\]",
                     old="Corollary strict_ready_iff_pdflatex :",
                     new="(* \"(*\" *)\nDefinition in_strict_doc (C : contract) "
                         "(d : doc) : Prop := False.\n(* \"*)\" *)\n\n"
                         "Corollary strict_ready_iff_pdflatex :"),
            # The allow-list itself: a sentence no keyword scan would flag.
            Mutation("an unpinned tactic sentence in Bridge.v",
                     "proofs/Strict/Bridge.v",
                     r"FAIL Bridge\.v: its code is not the pinned sentence list "
                     r"BRIDGE_SENTENCES .*not pinned: \['assumption'\]",
                     old="apply HF. exact Hs.",
                     new="apply HF. assumption."),
            # A name written into the kernel instead of the contract.
            Mutation("a control-word name is written into the Coq kernel",
                     "proofs/Strict/Semantics.v",
                     r"FAIL proofs/Strict/Semantics\.v: string literal 'alpha'",
                     old="Definition init : state := mkState [] false 0.\n",
                     new="Definition init : state := mkState [] false 0.\n"
                         "Definition lp_kill := \"alpha\".\n"),
            # ---- ADR-012 step 2, slice A --------------------------------
            # The review rule for the two new relations (Scans, Stops).
            Mutation("a Scans constructor loses its probe tag",
                     "proofs/Strict/Semantics.v",
                     r"FAIL Semantics\.v: constructor SC_close_last has no",
                     old="(* probe S0/SC_close_last: the closing brace",
                     new="(* S0/SC_close_last: the closing brace"),
            Mutation("a live argument constructor loses its probe family",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL rule_probes: no probe family for constructor R_close_arg",
                     transform=strict_arg_family_dropped),
            Mutation("membership no longer requires well-formed arguments",
                     "proofs/Strict/Decide.v",
                     r"FAIL Decide\.v: in_strict_toks no longer requires `wfa`",
                     old="  Forall (fun t => tok_ok C t = true) ts /\\ scripts_ok ts = true "
                         "/\\ wfa C 0 ts = true.",
                     new="  Forall (fun t => tok_ok C t = true) ts /\\ scripts_ok ts = true."),
            Mutation("an admitted one-argument command is not inert",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: admitted '.*' is not inert: conditional",
                     transform=strict_arg_not_inert),
            Mutation("an admitted one-argument command overflows grouping levels",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: admitted '.*' does not compile under "
                     r"A-R-NEST-TEXT",
                     transform=strict_arg_nest_overflows),
            Mutation("an admitted one-argument command lacks its display-follower probe",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: admitted '.*' lacks probe families "
                     r"\['A-D-FOLLOW'\]",
                     transform=strict_arg_follower_missing),
            Mutation("a name has both kinds of signature (contract_wf)",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: '.*' has both kinds of signature",
                     transform=strict_arg_both_kinds),
            Mutation("the argument candidates are not the selection rule's",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: the candidate list is not the selection rule's",
                     transform=strict_arg_candidate_dropped),
            Mutation("a phase-1 name disagrees inside an argument's mode",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: the context stage has 1 disagreement",
                     transform=strict_arg_context_disagrees),
            Mutation("the rule probes ran another argument-signature file",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL rule_probes: ran another argument-signature file",
                     transform=strict_rules_other_arg_file),
            Mutation("an argument-scanner cell is not exercised",
                     "corpora/strict_s0/rule_probes.json",
                     r"FAIL branch matrix: cell scan\|close\|k1\|nosh\|noou is not",
                     transform=strict_scan_cell_dropped),
        ]),
    GateTest(
        "check_strict_bytes",
        [PY, f"{TOOLS}/check_strict_bytes.py", "--repo", "."],
        "pure",
        [
            # The review rule of design §C.3, for the reader: every
            # constructor cites its probe family.
            Mutation("a reader constructor loses its probe tag",
                     "proofs/Strict/Lexer.v",
                     r"FAIL Lexer\.v: constructor LL_comment has no",
                     old="(* probe L0/LL_comment: the rest",
                     new="(* L0/LL_comment: the rest"),
            Mutation("a reader probe family has a disagreeing probe",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: family LL_comment: 1 of",
                     transform=bytes_family_one_disagrees),
            Mutation("the byte-level differential reports a disagreement",
                     "corpora/strict_s0/bytes_differential.json",
                     r"FAIL bytes_differential: 1 disagreement",
                     transform=bytes_differential_one_disagreement),
            Mutation("the byte-level differential is below its floor",
                     "corpora/strict_s0/bytes_differential.json",
                     r"FAIL bytes_differential: graded 2999 files, the floor is 3000",
                     transform=bytes_differential_below_floor),
            Mutation("a near-miss outside the fragment got a verdict",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: near-misses: 1 decided",
                     transform=bytes_near_miss_decided),
            Mutation("a reader branch-matrix cell is not exercised",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL reader branch matrix: cell S\|comment is not exercised",
                     transform=bytes_reader_cell_dropped),
            Mutation("the tree and the bytes deciders differ on a rendering",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: the tree decider and the bytes decider differ",
                     transform=bytes_tree_consistency_differs),
            Mutation("explain disagrees with the verdict",
                     "corpora/strict_s0/bytes_differential.json",
                     r"FAIL bytes_differential: explain_mismatches = 1",
                     transform=bytes_explain_mismatch),
            # A reader change without re-running the evidence.
            Mutation("the committed bytes extraction changes under the evidence",
                     "latex-parse/strict/strict_bytes_extracted.ml",
                     r"FAIL bytes_probes: ran another bytes_extract",
                     old="[@@@warning \"-a\"]\n",
                     new="[@@@warning \"-a\"]\n\nlet _lp_kill = ()\n"),
            Mutation("the byte-level probes ran another argument-signature file",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: ran another arg_signatures",
                     transform=bytes_other_arg_file),
            Mutation("the lexical contract changes under the evidence",
                     "corpora/contracts/strict/article-s0-lexical.json",
                     r"FAIL bytes_probes: ran another lexical",
                     transform=lexical_catcode_changed),
            Mutation("a structural name is not the renderer's",
                     "corpora/contracts/strict/article-s0-lexical.json",
                     r"FAIL lexical contract: structural names",
                     transform=lexical_structural_drift),
            Mutation("the end-of-line byte is no longer of category 5",
                     "corpora/contracts/strict/article-s0-lexical.json",
                     r"FAIL lexical contract: \\endlinechar is not a category-5 byte",
                     transform=lexical_endline_not_eol),
            # A name written into the reader instead of the lexical contract.
            Mutation("a control-word name is written into the Coq reader",
                     "proofs/Strict/Lexer.v",
                     r"FAIL proofs/Strict/Lexer\.v: string literal 'par'",
                     old="Definition sp : ascii := ascii_of_nat 32.\n",
                     new="Definition sp : ascii := ascii_of_nat 32.\n"
                         "Definition lp_kill := \"par\".\n"),
            # Membership without its exclusions.
            Mutation("in_strict_bytes no longer excludes a stream ending with $",
                     "proofs/Strict/DecideBytes.v",
                     r"FAIL DecideBytes\.v: in_strict_bytes no longer requires `ends_dollar",
                     old="    bounded (bc_kernel C) (toks_of ks) = true /\\\n"
                         "    ends_dollar (toks_of ks) = false.\n",
                     new="    bounded (bc_kernel C) (toks_of ks) = true.\n"),
            Mutation("the line bound's pin changes",
                     "proofs/Strict/Lexer.v",
                     r"FAIL Lexer\.v: missing the pin",
                     old="Example max_line_bytes_is_10000 : max_line_bytes = Nat.mul 100 100.",
                     new="Example max_line_bytes_is_10000 : max_line_bytes = Nat.mul 100 101."),
            # OPEN-121 MEDIUM-1 / C-87, on bytes: FaithfulBytes redefined as
            # the decider, conjoined with it, or shadowed from the Require line.
            Mutation("FaithfulBytes is redefined as the decider",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: FaithfulBytes' body is not the pinned one.*"
                     r"FAIL BridgeBytes\.v: FaithfulBytes' body does not mention Runs.*"
                     r"FAIL BridgeBytes\.v: FaithfulBytes' body mentions \['decide_bytes'\]",
                     transform=faithful_bytes_is_decide),
            Mutation("FaithfulBytes' body conjoins the decider to Runs",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: FaithfulBytes' body mentions \['decide_bytes'\]",
                     old="Runs (bc_kernel C) init (toks_of ks) Compiles).",
                     new="Runs (bc_kernel C) init (toks_of ks) Compiles /\\ "
                         "decide_bytes C b = ProvenReady)."),
            Mutation("a shadow Module Semantics on BridgeBytes.v's Require line",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: defines more than FaithfulBytes and its "
                     r"corollaries: \('Module', 'Semantics'\)",
                     old="From LaTeXPerfectionist.Strict Require Import Syntax Contract "
                         "Semantics Decide Lexer Front DecideBytes.\n",
                     new="From LaTeXPerfectionist.Strict Require Import Syntax Contract "
                         "Semantics Decide Lexer Front DecideBytes. Module Semantics. "
                         "Definition Runs (C : contract) (s : Semantics.state) "
                         "(ts : list tok) (o : outcome) : Prop := run C s ts = Some o. "
                         "End Semantics. Import Semantics.\n"),
            # The bytes PR's review, LOW-2: the kernel's C-88 shapes on
            # BridgeBytes.v. Mutant A: a control prefix hides the shadow's
            # keyword (measured: coqc's printed statement pins still pass on
            # this build; the kernel type pins and Print Module fail).
            Mutation("a Time-prefixed shadow in_strict_bytes in BridgeBytes.v",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: defines more than FaithfulBytes and its "
                     r"corollaries: \('prefix', 'Time'\).*"
                     r"FAIL BridgeBytes\.v: defines more than FaithfulBytes and its "
                     r"corollaries: \('Definition', 'in_strict_bytes'\)",
                     old="Corollary strict_ready_iff_pdflatex_bytes : forall oracle_ok C b,",
                     new="Time Definition in_strict_bytes (C : bcontract) "
                         "(b : list Ascii.ascii) : Prop := False.\n\n"
                         "Corollary strict_ready_iff_pdflatex_bytes : forall oracle_ok C b,"),
            # Mutant B: a shadow between two comments holding strings with a
            # comment delimiter (Coq lexes strings inside comments).
            Mutation("a shadow in_strict_bytes between two comment-strings",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: defines more than FaithfulBytes and its "
                     r"corollaries: \('Definition', 'in_strict_bytes'\)",
                     old="Corollary strict_ready_iff_pdflatex_bytes : forall oracle_ok C b,",
                     new="(* \"(*\" *)\nDefinition in_strict_bytes (C : bcontract) "
                         "(b : list Ascii.ascii) : Prop := False.\n(* \"*)\" *)\n\n"
                         "Corollary strict_ready_iff_pdflatex_bytes : forall oracle_ok C b,"),
            # The allow-list itself: a sentence no keyword scan would flag.
            Mutation("an unpinned tactic sentence in BridgeBytes.v",
                     "proofs/Strict/BridgeBytes.v",
                     r"FAIL BridgeBytes\.v: its code is not the pinned sentence list "
                     r"BRIDGE_SENTENCES .*not pinned: \['apply HF; auto'\]",
                     old="apply HF; assumption.",
                     new="apply HF; auto."),
            # LOW-3: the summary is recomputed from the records.
            Mutation("one record's agree flipped under an unchanged summary",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: record i=\d+: stored agree False, but its "
                     r"oracle tuple .* give True",
                     transform=bytes_record_agree_flipped),
            Mutation("one record's oracle tuple changed under its agree",
                     "corpora/strict_s0/bytes_differential.json",
                     r"FAIL bytes_differential: record i=\d+: stored agree True, but its "
                     r"oracle tuple \[1, ",
                     transform=bytes_record_oracle_changed),
            # LOW-1: an E0 has no l.N; a record that gives one disagrees.
            Mutation("an E0 record carries a line",
                     "corpora/strict_s0/bytes_probes.json",
                     r"FAIL bytes_probes: record i=\d+: stored agree True, .*"
                     r"model E0 carries a line \(4\); pdfTeX reports none",
                     transform=bytes_e0_record_has_line),
        ]),
    GateTest(
        "check_gen_contract_parsers",
        [PY, f"{TOOLS}/check_gen_contract_parsers.py"],
        "pure",
        [
            # Review defect 2 (2026-09-27): the null control sequence read as
            # the literal name `csname\endcsname`. Reverting the reading must
            # fail the recorded-trace test.
            Mutation("null cs no longer read as the empty name",
                     "scripts/tools/gen_contract.py",
                     r"FAIL null cs",
                     old='        if dec == e + b"csname" + e + b"endcsname":\n'
                         '            out.append(("cs", NULL_CS))\n',
                     new='        if dec == e + b"csname" + e + b"endcsname":\n'
                         '            pass\n'),
            # Review defect 1: a kernel name the reviewers found missing.
            Mutation("kernel file loses topmark",
                     KERNEL_FILE, r"FAIL kernel \S+ holds topmark",
                     transform=kernel_drop_topmark),
            # The completeness evidence itself must be read, not just present.
            Mutation("kernel hash coverage reports one uncovered name",
                     KERNEL_FILE, r"FAIL kernel \S+: TeX's hash count finds no name",
                     transform=kernel_uncover_one),
            # Re-review defect 1 (2026-09-27): the completeness evidence of the
            # pass the oracle grades must be read.
            Mutation("contract pass-4 hash coverage reports one uncovered name",
                     "corpora/contracts/article.json",
                     r"FAIL contract article\.json: \.\.\. and it finds nothing undumped",
                     transform=contract_pass4_uncover_one),
            Mutation("contract loses the grading-environment count of pass 3",
                     "corpora/contracts/article.json",
                     r"FAIL contract article\.json: TeX's hash count on every pass",
                     transform=contract_drop_grading_pass3),
            # Re-review 2 defect 1: the pass histories must reach pass 4.
            Mutation("pass histories stop after the first failing pass",
                     "scripts/tools/gen_contract.py",
                     r"FAIL pass histories: exactly",
                     old="    for j in range(max_passes):\n",
                     new="    for j in range(1):\n"),
            # Re-review LOW item a: set_in through the save stack. Disabling
            # the stack lookup must fail the recorded \WriteBookmarks test.
            Mutation("set_in no longer looked up in the save stack",
                     "scripts/tools/gen_contract.py",
                     r"FAIL set_in: hyperref's",
                     old="                stack = saves.get(key) or []\n",
                     new="                stack = []\n"),
            # One oracle TeX environment (_oracle.ORACLE_TEX_VARS). A grader
            # that restates it, or a generator environment that drifts from
            # base + its documented overrides, must fail the gate.
            Mutation("a grader restates the oracle's TeX environment",
                     "scripts/tools/confirm_fix_policy.py",
                     r"FAIL env: no tool restates the oracle's TeX environment",
                     old="    return oracle_tex_env(td)\n",
                     new='    return dict(oracle_tex_env(td), openin_any="p")\n'),
            Mutation("the generator's grading environment forces the date",
                     "scripts/tools/gen_contract.py",
                     r"FAIL env grading: exactly the oracle's environment",
                     old='    if env == "grading":\n        return out\n',
                     new='    if env == "grading":\n        return dict(out, **FORCE_DATE)\n'),
        ]),
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
            Mutation("provenance sha unresolvable — ratchet blinded (C-58)",
                     "corpora/apply_fixes_real/results.json",
                     r"cannot be resolved in this clone",
                     transform=prov_unresolvable_sha),
            Mutation("a row's cell stops following from its own rc pair",
                     "corpora/apply_fixes_real/results.json",
                     r"cell 'preserved' but rc_after=1",
                     transform=afr_desync_cell),
            Mutation("the pinned artefact claims the allow-list scope (OPEN-112)",
                     "corpora/apply_fixes_real/results.json",
                     r"provenance\.fixer_scope=",
                     transform=afr_scope_default),
        ]),
    GateTest(
        "check_oracle_pin",
        [PY, f"{TOOLS}/check_oracle_pin.py"],
        "pure",
        [
            # ADR-012 decision 7 / OPEN-118: a tool that shells out to a host
            # pdflatex again must fail the gate, not grade with the laptop.
            Mutation("a grader calls a host pdflatex directly again",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"pdflatex\", top]).returncode, False\n"),
            # A graded artefact whose oracle block loses the image is a
            # host-graded artefact again.
            Mutation("a graded artefact stops naming the pinned image",
                     "corpora/strict_battery/manifest.json",
                     r"not the pinned image",
                     old='"image": "texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b"',
                     new='"image": null'),
            # Review of 2026-09-27: the scan matched only a Python list whose
            # FIRST element was "pdflatex", and only under scripts/. One kill
            # per evasion shape it was measured to miss.
            Mutation("an engine behind a timeout prefix in a list",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"timeout\", \"180\", \"pdflatex\", top]).returncode, False\n"),
            Mutation("an engine as a shell=True f-string",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run(f\"pdflatex {top}\", shell=True).returncode, False\n"),
            Mutation("an engine found with shutil.which",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([shutil.which(\"latexmk\"), top]).returncode, False\n"),
            Mutation("a shell grader runs a bare pdflatex again",
                     "scripts/tools/diff_compile_check.sh",
                     r"starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  ( cd \"$d\" && pdflatex \"$base\" )\n"),
            # Review round 2 (2026-09-27): evasions measured to pass the scan.
            Mutation("an engine after an echo on the same shell line",
                     "scripts/tools/diff_compile_check.sh",
                     r"starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  echo run && pdflatex \"$base\"\n"),
            Mutation("an engine name assembled from a shell variable",
                     "scripts/tools/diff_compile_check.sh",
                     r"starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  P=pdf; ${P}latex \"$base\"\n"),
            # Review round 3: the shell dequotes a word before running it, so
            # an engine assembled from quoted/escaped pieces is still an engine.
            Mutation("an engine name split by shell quotes",
                     "scripts/tools/diff_compile_check.sh",
                     r"starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  \"pdf\"latex \"$base\"\n"),
            Mutation("an engine name split by a shell backslash",
                     "scripts/tools/diff_compile_check.sh",
                     r"starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  pdf\\latex \"$base\"\n"),
            Mutation("an engine as a bytes literal",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([b\"pdflatex\", top]).returncode, False\n"),
            Mutation("an engine behind a dict value",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        E = {\"tex\": \"pdflatex\"}\n        rc, timed_out = subprocess.run([E[\"tex\"], top]).returncode, False\n"),
            # OPEN-119: the virgin sample is a graded artefact like any other;
            # its frame manifest losing the image is a host grade again.
            Mutation("the virgin sample's manifest stops naming the pinned image",
                     "corpora/real_roots/manifest_sample3.json",
                     r"manifest_sample3\.json: graded by .*not the pinned image",
                     old='"image": "texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b"',
                     new='"image": null'),
            Mutation("an engine split by implicit string concatenation",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"pdf\" \"latex\", top]).returncode, False\n"),
            Mutation("an OCaml file that spawns processes names an engine",
                     "latex-parse/src/test_validators_cli.ml",
                     r"starts a TeX engine directly",
                     old="  let ic = Unix.open_process_in cmd in\n",
                     new="  let ic = Unix.open_process_in (\"pdflatex \" ^ cmd) in\n"),
            # The image string alone is not evidence: a hand-stamped block
            # must also carry the pinned tree's fingerprints and a backend.
            Mutation("a graded artefact records a foreign macro layer",
                     "corpora/false_ready/manifest.json",
                     r"macro_layer_sha256 .* is not the pinned",
                     old='"macro_layer_sha256": "27089de69500214440bb78910236f788be89a4692c989bdc217ca93e5ba91c10"',
                     new='"macro_layer_sha256": "0000000000000000000000000000000000000000000000000000000000000000"'),
            Mutation("a graded artefact records a host backend",
                     "corpora/apply_fixes/manifest.json",
                     r"oracle backend .* is not one of",
                     old='"backend": "container"',
                     new='"backend": "host"'),
            # A re-pin that forgets to re-measure the tree fingerprints.
            Mutation("tex-oracle.yml re-pinned without re-measuring the tree",
                     ".github/workflows/tex-oracle.yml",
                     r"fingerprints were measured for",
                     old="  TEX_IMAGE: texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b\n",
                     new="  TEX_IMAGE: texlive/texlive@sha256:0000000000000000000000000000000000000000000000000000000000000000\n"),
            # OPEN-118 known limit (g), C-91: shapes the round-3 re-review
            # MEASURED at RC 0 -- a format-less engine, a format selector,
            # an ANSI-C escape, a statically resolvable concatenation. One
            # kill per shape.
            Mutation("pdftex (INITEX) in a Python argv list",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly \('pdftex'\)",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"pdftex\", \"-ini\", top]).returncode, False\n"),
            Mutation("a '&fmt' format selector behind a variable binary (Python)",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly \('&pdflatex'\)",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([os.environ[\"TEXBIN\"], \"&pdflatex\", top]).returncode, False\n"),
            Mutation("a -fmt= format selector behind a variable binary (Python)",
                     "scripts/tools/ablate_fix_classes.py",
                     r"starts a TeX engine directly \('-fmt=pdflatex'\)",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([os.environ[\"TEXBIN\"], \"-fmt=pdflatex\", top]).returncode, False\n"),
            Mutation("an engine name built by str.join over literals",
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('pdflatex'\)",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"\".join([\"pdf\", \"latex\"]), top]).returncode, False\n"),
            Mutation("an engine name built by + over literals",
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('pdflatex'\)",
                     old="        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n",
                     new="        rc, timed_out = subprocess.run([\"pdf\" + \"latex\", top]).returncode, False\n"),
            Mutation("an engine name in a shell ANSI-C escape",
                     "scripts/tools/diff_compile_check.sh",
                     r"diff_compile_check\.sh:\d+: starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  $'pdf\\x6catex' \"$base\"\n"),
            Mutation("pdftex '&pdflatex' in a shell grader",
                     "scripts/tools/diff_compile_check.sh",
                     r"diff_compile_check\.sh:\d+: starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  pdftex '&pdflatex' \"$base\"\n"),
            Mutation("a -fmt= selector after a variable binary in shell",
                     "scripts/tools/diff_compile_check.sh",
                     r"diff_compile_check\.sh:\d+: starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  \"$TEXBIN\" -fmt=pdflatex \"$base\"\n"),
            Mutation("a bare initex in shell",
                     "scripts/tools/diff_compile_check.sh",
                     r"diff_compile_check\.sh:\d+: starts a TeX engine directly",
                     old="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n",
                     new="  cp \"$CORPUS\"/*_part.tex \"$d/\" 2>/dev/null || true\n  initex \"$base\"\n"),
            # C-91 review round 4: shapes MEASURED to scan clean at a0c839e3.
            # One kill per shape; the vocabulary is _oracle.TEX_ENGINE_BINARIES.
            Mutation('a format-named engine link the old 11-name list missed',
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  pdflatex-dev "$base"\n'),
            Mutation('mllatex -progname=pdflatex (a -progname format selector)',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('mllatex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        rc, timed_out = subprocess.run(["mllatex", "-progname=pdflatex", top]).returncode, False\n'),
            Mutation('a -progname= selector behind a variable binary',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('-progname=pdflatex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        rc, timed_out = subprocess.run([os.environ["TEXBIN"], "-progname=pdflatex", top]).returncode, False\n'),
            Mutation('an engine name built by + over parenthesised literals',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('(pdf)?latex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        rc, timed_out = subprocess.run([("pdf") + ("latex"), top]).returncode, False\n'),
            Mutation('an engine name built by join over a generator',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('pdflatex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        rc, timed_out = subprocess.run(["".join(c for c in ("pdf", "lat", "ex")), top]).returncode, False\n'),
            Mutation('an engine name built from a once-bound variable',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('pdflatex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        _LP_KILL_P = "pd"\n        rc, timed_out = subprocess.run([_LP_KILL_P + "flat" + "ex", top]).returncode, False\n'),
            Mutation('an engine name built by % formatting',
                     "scripts/tools/ablate_fix_classes.py",
                     r"ablate_fix_classes\.py:\d+: starts a TeX engine directly \('pdflatex'\)",
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new='        rc, timed_out = subprocess.run(["pdf%sex" % "lat", top]).returncode, False\n'),
            Mutation("an engine in a parameter expansion's default word",
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  E="${TEXENG:-pdftex}"; $E "$base"\n'),
            Mutation('an engine made by brace expansion',
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  pdf{latex,} "$base"\n'),
            Mutation('an engine matched by a glob',
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  pdfla[t]ex "$base"\n'),
            Mutation('an engine assigned by printf -v',
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  printf -v E \'%slatex\' pdf; $E "$base"\n'),
            Mutation('an echoed engine command piped into a shell',
                     "scripts/tools/diff_compile_check.sh",
                     r'diff_compile_check\.sh:\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo \'pdflatex main.tex\' | sh\n'),
            Mutation('a make function over literals assembles an engine',
                     "Makefile",
                     r"Makefile:\d+: starts a TeX engine directly",
                     old="SHELL := /bin/bash\n",
                     new="SHELL := /bin/bash\nkill:\n\t$(subst X,,pdfXlatex) main.tex\n"),
            Mutation('an engine in an extensionless shebang script',
                     "verify_percentiles",
                     r"verify_percentiles:\d+: starts a TeX engine directly",
                     old="set -euo pipefail\n",
                     new="set -euo pipefail\npdflatex main.tex\n"),
            Mutation('a workflow run: value after the YAML-key rule',
                     ".github/workflows/tex-oracle.yml",
                     r"tex-oracle\.yml:\d+: starts a TeX engine directly",
                     old="      - name: Emit fixture list\n",
                     new="      - name: Kill\n        run: pdflatex t.tex\n      - name: Emit fixture list\n"),
            # C-91 review round 5: one kill per evasion shape measured to scan
            # clean (the reviewer's harness, the reviewer's session scratchpad, not in the repository).
            Mutation('an echoed engine run through a timeout-wrapped shell',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo \'pdflatex t.tex\' | timeout 60 sh\n'),
            Mutation('an echoed engine run by a while-read loop',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo \'pdflatex t.tex\' | while read -r c; do $c; done\n'),
            Mutation('an echoed engine run by awk system()',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo \'pdflatex t.tex\' | awk \'{system($0)}\'\n'),
            Mutation('an engine in a command substitution inside a message',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo "log: $(pdflatex "$base")"\n'),
            Mutation('an engine in backquotes inside a printf message',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  printf \'%s\\n\' "`pdflatex t.tex`"\n'),
            Mutation('an engine command echoed into a file',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  echo \'pdflatex t.tex\' > "$d/run.sh"\n'),
            Mutation('an engine assembled from two shell variables',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  LPK_P=pdfl; LPK_Q=atex; ${LPK_P}${LPK_Q} "$base"\n'),
            Mutation('an engine made by a case-folding expansion',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  LPK_E=PDFLATEX; ${LPK_E,,} "$base"\n'),
            Mutation('an engine made by += and a plain expansion',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  LPK_E=pd; LPK_E+=flatex; $LPK_E "$base"\n'),
            Mutation("an engine in an indirect expansion's default",
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  ${!lpk_n:-pdftex} "$base"\n'),
            Mutation('a heredoc body run by python3',
                     'scripts/tools/diff_compile_check.sh',
                     'diff_compile_check\\.sh:\\d+: starts a TeX engine directly',
                     old='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n',
                     new='  cp "$CORPUS"/*_part.tex "$d/" 2>/dev/null || true\n  python3 - <<\'LPKEOF\'\nimport subprocess; subprocess.run([\'pdfl\' + \'atex\', \'t.tex\'])\nLPKEOF\n'),
            Mutation('an engine made by map(chr, ...)',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run([''.join(map(chr, [112, 100, 102, 108, 97, 116, 101, 120])), top]).returncode, False\n"),
            Mutation('an engine made by %(name)s dict formatting',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run(['%(a)satex' % {'a': 'pdfl'}, top]).returncode, False\n"),
            Mutation('an engine made by str.__add__',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run([str.__add__('pdfl', 'atex'), top]).returncode, False\n"),
            Mutation('an engine made by functools.reduce(operator.add)',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run([functools.reduce(operator.add, ['pdfl', 'atex']), top]).returncode, False\n"),
            Mutation('an engine made by a walrus',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run([(_lpk_w := 'pdfl') + 'atex', top]).returncode, False\n"),
            Mutation('a format selector as an unpacked dict key',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        rc, timed_out = subprocess.run([sys.executable, *{'-progname=pdflatex': 1}, top]).returncode, False\n"),
            Mutation('an engine from tuple unpacking',
                     'scripts/tools/ablate_fix_classes.py',
                     'ablate_fix_classes\\.py:\\d+: starts a TeX engine directly',
                     old='        rc, timed_out = get_oracle().run_once(pathlib.Path(work), top, env, 180)\n',
                     new="        _lpk_a, _lpk_b = 'pdfl', 'atex'\n        rc, timed_out = subprocess.run([_lpk_a + _lpk_b, top]).returncode, False\n"),
            Mutation('an OCaml Unix.system of an engine',
                     'latex-parse/src/fix_policy.ml',
                     'fix_policy\\.ml:\\d+: starts a TeX engine directly',
                     old='(* Fix policy — see fix_policy.mli for the why.\n',
                     new='let _lpk = Unix.system "pdflatex main.tex"\n(* Fix policy — see fix_policy.mli for the why.\n'),
            Mutation('make variables assembling an engine',
                     'Makefile',
                     'Makefile:\\d+: starts a TeX engine directly',
                     old='SHELL := /bin/bash\n',
                     new='SHELL := /bin/bash\nLPK_P = pdfl\nLPK_Q = atex\nkill:\n\t$(LPK_P)$(LPK_Q) main.tex\n'),
            Mutation('a Dockerfile RUN of an engine',
                     'Dockerfile',
                     'Dockerfile:\\d+: starts a TeX engine directly',
                     old='FROM ubuntu:22.04\n',
                     new='FROM ubuntu:22.04\nRUN pdflatex main.tex\n'),
            Mutation("a composite action's run: of an engine",
                     '.github/actions/setup-ocaml-env/action.yml',
                     'action\\.yml:\\d+: starts a TeX engine directly',
                     old='  steps:\n',
                     new='  steps:\n    - run: pdflatex main.tex\n      shell: bash\n'),
            Mutation('a pre-commit entry: that runs an engine',
                     '.pre-commit-config.yaml',
                     'pre-commit-config\\.yaml:\\d+: starts a TeX engine directly',
                     old='    hooks:\n',
                     new='    hooks:\n      - id: lpk\n        entry: pdflatex main.tex\n        language: system\n'),
            Mutation("a notebook cell's !engine line",
                     'ml/notebooks/span_extractor_training.ipynb',
                     'span_extractor_training\\.ipynb:\\d+: starts a TeX engine directly',
                     old='"!nvidia-smi\\n",',
                     new='"!nvidia-smi\\n",\n    "!pdflatex main.tex\\n",'),
        ]),
    GateTest(
        # OPEN-118 review round 2: a run with no proof that pdfTeX ran (the
        # measured shape: docker CLI "failed to connect to the docker API",
        # exit 1) was graded "pdflatex failed". One kill per proof check.
        "check_oracle_infra_grading",
        [PY, f"{TOOLS}/check_oracle_infra_grading.py"],
        "pure",
        [
            # The contract generator is an oracle client (run_engine): the
            # engine it names must be the one that runs, and on the native
            # backend no host TeX variable may cross into its jobs.
            Mutation("the in-container script runs a fixed engine, not the given one",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*runs the engine run_engine names",
                     old='timeout -k 10 "$t" "$e" "$@"',
                     new='timeout -k 10 "$t" pdflatex "$@"'),
            Mutation("native run_engine lets the host's TeX variables through",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*no host TeX variable",
                     old="        env = engine_env(env, self.engine_base)\n",
                     new="        env = {**os.environ, **engine_env(env, self.engine_base)}\n"),
            # C-91 review round 4 (HIGH): the native backend handed pdflatex
            # the caller's whole dict minus the _ENV_FORWARD names, and a host
            # openout_any_pdflatex=a flipped a grade. The engine's environment
            # is an allow-list now; each kill reopens one layer of it.
            Mutation("engine_env passes every key of the caller's dict (a blocklist)",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*shim on the native backend does not give its run",
                     old="    out.update({k: v for k, v in (tex_vars or {}).items() if _ENV_FORWARD.match(k)})\n",
                     new="    out.update(tex_vars or {})\n"),
            Mutation("the container backend stops checking its container's environment",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*fingerprint accepted a container whose environment",
                     old="            check_container_env(dict(x.split(",
                     new="            (dict(x.split("),
            Mutation("check_container_env accepts any environment",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*fingerprint accepted a container whose environment",
                     old="    if got != IMAGE_ENV:\n",
                     new="    if False:\n"),
            Mutation("the container oracle drops the pdfTeX-banner proof",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*'nobanner' run",
                     old='        _require_pdftex_ran(rc, p.stdout, f"container {self.name}")\n',
                     new=""),
            Mutation("the container oracle trusts the docker CLI's rc again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*'dead' run",
                     old="        if m is None:\n            raise OracleError(\n",
                     new="        if m is None:\n            return p.returncode, p.stdout + p.stderr, False\n"
                         "        if m is None:\n            raise OracleError(\n"),
            Mutation("the shim maps only OracleError to INFRA_RC",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*non-OracleError exception",
                     old="    except BaseException as e:  # noqa: BLE001 -- every exception, see below\n",
                     new="    except OracleError as e:\n"),
            Mutation("pdflatex_ok grades an oracle failure as 'fails'",
                     "scripts/tools/check_apply_fixes_roundtrip.py",
                     r"\[oracle-infra\] FAIL.*pdflatex_ok under 'dead'",
                     old='        print(f"[fixer-roundtrip] NOT GRADED ({base}): {e}", file=sys.stderr)\n        return None\n',
                     new='        print(f"[fixer-roundtrip] NOT GRADED ({base}): {e}", file=sys.stderr)\n        return False\n'),
            Mutation("false_ready_oracle.sh drops the per-pass banner proof",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*run_pdflatex graded plan 'dead'",
                     old="    if ! grep -q 'This is pdfTeX' \"$out\" 2>/dev/null; then rc=NOPROOF; break; fi\n",
                     new=""),
            Mutation("false_ready_oracle.sh stops checking the halt run's log",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*halt run's pdfTeX log",
                     old="  if ! grep -q 'This is pdfTeX' \"$rundir/${base%.tex}.log\" 2>/dev/null; then\n",
                     new="  if false; then\n"),
            Mutation("a compiles fixture that stops compiling is soft drift again",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*drift_class error-halt vs manifest compiles",
                     old='  elif [ "$2" = compiles ]; then echo hard-rejects\n',
                     new=""),
            # OPEN-118 review round 3: proof pdfTeX ran is not proof its rc
            # is the document's. MEASURED: a full work root gave banner + rc 1
            # ("I can't write on file `t.log'", "fwrite() failed") and every
            # grader graded FAILS. One kill per environment check.
            Mutation("the container oracle stops refusing pdfTeX's own write failures",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*'fwrite' run",
                     old='        _require_output_written(p.stdout + err, args, f"container {self.name}")\n',
                     new=""),
            Mutation("the own-output check stops keying on the job name",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*own \\openout refused",
                     old="        own = (stem == job and dot and ext.isalnum()) if job else (\n",
                     new="        own = True if job else (\n"),
            Mutation("the container oracle drops the free-space floor before a run",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*runs \(and grades\) with the work root below",
                     old='        _require_free_space(cwd, "before")\n        cmd = ["exec"',
                     new='        cmd = ["exec"'),
            Mutation("the container oracle drops the free-space floor after a run",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*grades a run after which",
                     old='        _require_output_written(p.stdout + err, args, f"container {self.name}")\n'
                         '        _require_free_space(cwd, "after")\n',
                     new='        _require_output_written(p.stdout + err, args, f"container {self.name}")\n'),
            Mutation("false_ready_oracle.sh stops vetting each pass's output",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*graded plan 'fwrite'",
                     old='    if ! oracle_vet "$wd" "$out" "${cmd[@]}" 2>/dev/null; then rc=ENVFAIL; break; fi\n',
                     new=""),
            Mutation("false_ready_oracle.sh stops checking free space before a run",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*run_pdflatex graded a run with the work root below",
                     old='  if ! oracle_vet "$wd" 2>/dev/null; then rm -f "$out"; echo "ENVFAIL no"; return; fi\n',
                     new=""),
            Mutation("diff_compile_check.sh stops vetting the run's output",
                     "scripts/tools/diff_compile_check.sh",
                     r"\[oracle-infra\] FAIL.*diff_compile_check\.sh no longer vets",
                     old='  if [ "$envok" = yes ] && ! oracle_vet "$d" "$pout" -interaction=nonstopmode -halt-on-error "$base" 2>/dev/null; then\n    envok=no\n  fi\n',
                     new=""),
            # OPEN-118 known limit (b), C-91: ONE grading environment, imposed
            # by the oracle. Each kill reverts one layer of it.
            Mutation("run_pdflatex stops imposing the grading environment",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex forwards a caller's TeX variables",
                     old="ENGINE_PDFLATEX, args, graded_env(env), timeout)",
                     new="ENGINE_PDFLATEX, args, env, timeout)"),
            Mutation("graded_env stops imposing ORACLE_TEX_VARS",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*SOURCE_DATE_EPOCH=None \(protocol '0'\)",
                     old="    out.update(ORACLE_TEX_VARS)\n    return out\n",
                     new="    return out\n"),
            Mutation("graded_env forwards the host's other TeX variables",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*host FORCE_SOURCE_DATE='1' reached the engine",
                     old="    out = {k: v for k, v in env.items() if not _ENV_FORWARD.match(k)}\n",
                     new="    out = dict(env)\n"),
            Mutation("graded_env stops requiring a private TEXMFHOME/TEXMFVAR",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex graded a run with no private",
                     old="    missing = [k for k in _GRADING_TEXMF if not env.get(k)]\n",
                     new="    missing = []\n"),
            Mutation("_oracle.sh runs a bare pdflatex on the native backend again",
                     "scripts/tools/_oracle.sh",
                     r"\[oracle-infra\] FAIL.*_oracle\.sh \(native\) does not run",
                     old='    PDFLATEX=(python3 "$py" pdflatex --timeout "$TEX_TIMEOUT")\n    ORACLE_RM=(rm -f --)\n',
                     new='    PDFLATEX=(pdflatex)\n    ORACLE_RM=(rm -f --)\n'),
            Mutation("check_apply_fixes_roundtrip passes the host environment again",
                     "scripts/tools/check_apply_fixes_roundtrip.py",
                     r"\[oracle-infra\] FAIL.*pdflatex_ok does not grade in the protocol",
                     old="            rc, timed_out = o.run_once(workdir, base, o.tex_env(td), secs)\n",
                     new="            rc, timed_out = o.run_once(workdir, base, dict(os.environ), secs)\n"),
            Mutation("image_command lets an engine through as an argument",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*image_command ran \['xargs'\]",
                     old="        eng = [a for a in map(str, argv) if Path(a).name in TEX_ENGINE_BINARIES\n               or a.startswith(\"&\") or FMT_SELECTOR.match(a)]\n",
                     new="        eng = []\n"),
            Mutation("image_command lets a -progname/-fmt selector through",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*image_command ran \['sha256sum'\]",
                     old="               or a.startswith(\"&\") or FMT_SELECTOR.match(a)]\n",
                     new="               or a.startswith(\"&\")]\n"),
            Mutation("image_command runs a shell",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*image_command ran \['sh'\]",
                     old="        if not argv or Path(str(argv[0])).name in _IMAGE_SHELLS:\n",
                     new="        if not argv:\n"),
            # C-91 review round 5: the argv allow-list, the private
            # TEXMFCONFIG and the container-state checks, one kill each.
            Mutation("run_pdflatex stops checking the graded argv",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex ran the argv \['-cnf-line=openout_any=a'",
                     old="        check_engine_argv(args, cwd, graded=True)\n",
                     new=""),
            Mutation("run_engine stops checking its argv",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_engine ran \['-ini', '-cnf-line=shell_escape=t'",
                     old="        check_engine_argv(list(args), cwd, graded=False)\n",
                     new=""),
            Mutation("the graded allow-list accepts any option",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex ran the argv \['-shell-escape'",
                     old="        if value is None and name in flags:\n",
                     new="        if value is None:\n"),
            Mutation("TEXMFCONFIG is no longer a private per-run tree",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*graded_env accepted a run without a private TEXMFCONFIG",
                     old='_GRADING_TEXMF = ("TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG")',
                     new='_GRADING_TEXMF = ("TEXMFHOME", "TEXMFVAR")'),
            Mutation("fingerprint stops checking the persistent TeX trees",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*fingerprint \(check_texmf_trees\) accepted",
                     old="            self.check_texmf_trees()\n",
                     new=""),
            Mutation("get_oracle stops scanning the container's state",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*session state scan accepted",
                     old="        _ORACLE.check_state()\n",
                     new=""),
        ]),
    GateTest(
        "check_compile_check_consumers",
        [PY, f"{TOOLS}/check_compile_check_consumers.py"],
        "pure",
        [
            # ADR-012 (M0): the reason scrape must stop at the TIER line, or
            # author source quoted on a why-not-strict line is recorded as a
            # BLOCKING reason. Reverting the stop must fail the gate.
            Mutation("diff_real_roots scrapes the tier block again (C-65)",
                     "scripts/tools/diff_real_roots.py",
                     r"scrape_reasons reads the M0 tier block",
                     old='        if line.startswith("TIER\\t"):\n            break\n',
                     new='        if line.startswith("TIER\\t"):\n            pass\n'),
            Mutation("parse_tier accepts PROVEN outside the proven tier",
                     "scripts/tools/gen_proven_coverage.py",
                     r"parse_tier accepted a PROVEN kind in the heuristic tier",
                     old='        if (tier == "proven") != kind.startswith("PROVEN-"):',
                     new='        if False:'),
            # The gate IMPORTS regrade_sample's filter, so breaking the real
            # filter's T0 prefix must fail it (a hand copy would stay green).
            Mutation("regrade_sample stops keeping T0 reason lines",
                     "scripts/tools/regrade_sample.py",
                     r"regrade_sample lost the leading T0 token",
                     old='REASON_PREFIXES = ("T0", "T2", "T3", "T4", "T5", "MODEL-NOT")',
                     new='REASON_PREFIXES = ("T2", "T3", "T4", "T5", "MODEL-NOT")'),
        ]),
    GateTest(
        "check_fix_allowlist",
        [PY, f"{TOOLS}/check_fix_allowlist.py"],
        "pure",
        [
            Mutation("an implicated rule enters the default fix set",
                     "latex-parse/src/fix_policy.ml",
                     r"CHEM-005 is in the default set but listed as implicated",
                     transform=allowlist_inject_implicated),
            Mutation("an allow-listed rule's review verdict is UNSAFE",
                     "corpora/apply_fixes_real/fix_meaning_review.json",
                     r"is reviewed 'unsafe', not 'safe'",
                     transform=review_flip_first_safe),
            Mutation("the refutation evidence is missing",
                     "corpora/apply_fixes_real/fix_meaning_review.json",
                     r"has no refutation attempt that found no damage",
                     transform=review_drop_refutations),
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
            # The engine anchor must FAIL when the source has moved under a
            # recorded measurement (C-64). Exact, where the commit count is a
            # proxy — and unlike cli_sha256 this one is checkable in CI.
            Mutation("engine anchor names a tree that never existed (C-64)",
                     "corpora/real_roots/proven_coverage_sample1.json",
                     r"not a tree object in this repository",
                     transform=prov_stale_engine_tree),
            # The staleness ratchet must FAIL when it cannot see its own
            # input. Before C-58 this passed: an unresolvable sha made
            # `git rev-list` exit 128 and the guard had no else branch.
            Mutation("provenance sha unresolvable — ratchet blinded (C-58)",
                     "corpora/real_roots/results.json",
                     r"cannot be resolved in this clone",
                     transform=prov_unresolvable_sha),
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
                     # Re-anchored 2026-09-20: the OPEN-103 sweep took the
                     # clause to full coverage, so the old "18/200" anchor
                     # matched 0x and the registry-rot arm fired. Deliberate
                     # update, per the message it prints.
                     old="APPLIED TO ALL 200/200 rows",
                     new="APPLIED TO ALL 42/200 rows"),
            # C-45: a verdict cell that its own row contradicts. The regex
            # names the COMPILES wording specifically, because re-stranding a
            # row also makes the generated block stale and that unrelated
            # finding must not be able to supply a false kill.
            Mutation("ungraded row re-stranded while it compiles (C-45)",
                     "corpora/real_roots/results.json",
                     r"but its recorded outcome says it COMPILES",
                     transform=restrand_ungraded_row),
            # OPEN-119: the three checks above must also watch sample 3, the
            # virgin sample. Each regex names results_sample3 so a finding
            # about another artefact cannot supply a false kill.
            Mutation("virgin-sample provenance unresolvable (OPEN-119)",
                     "corpora/real_roots/results_sample3.json",
                     r"results_sample3\.json.{0,200}cannot be resolved in this clone",
                     transform=prov_unresolvable_sha),
            Mutation("virgin-sample row re-stranded while it compiles (OPEN-119)",
                     "corpora/real_roots/results_sample3.json",
                     r"results_sample3\.json: \S+ is 'ungraded-infra' but its "
                     r"recorded outcome says it COMPILES",
                     transform=restrand_ungraded_row),
            Mutation("virgin-sample protocol claim outruns its rows (OPEN-119)",
                     "corpora/real_roots/results_sample3.json",
                     r"results_sample3\.json protocol claims multi-pass wholesale",
                     transform=drop_one_passes_count),
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
                     # Re-anchored 2026-09-27 (OPEN-119): the read now loops
                     # over results.json and results_sample3.json.
                     old='        except (json.JSONDecodeError, OSError) as exc:\n'
                         '            findings.append(f"corpora/real_roots/{rr.name} is unreadable: {exc}")\n'
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
    # C-98, M-1/M-2 of the round-2 review: the capacity evidence re-derived by
    # the extracted decider (the pure gate cannot run it).
    GateTest(
        "check_strict_capacity", [PY, f"{TOOLS}/check_strict_capacity.py", "--repo", "."],
        "binary",
        [
            Mutation("a frame pair dropped and its count decremented (M-1)",
                     "corpora/strict_s0/capacity.json",
                     r"FAIL capacity: the recorded frame pairs are not the model's",
                     transform=strict_capacity_pair_forged),
            Mutation("a pair's recorded peak is not the model's (M-1)",
                     "corpora/strict_s0/capacity.json",
                     r"FAIL capacity: pair \S+ at: the model gives",
                     transform=strict_capacity_peak_forged),
            Mutation("a memory worst case's recorded account is not the model's (M-2)",
                     "corpora/contracts/strict/article-s1-arg-signatures.json",
                     r"FAIL arg signatures: memory worst case \S+ at: the model gives",
                     transform=strict_memory_bound_forged),
        ]),
    GateTest(
        "check_project_state (binary arm)",
        [PY, f"{TOOLS}/check_project_state.py"],
        "binary",
        [
            Mutation("stale build: same source, different binary (C-68)",
                     "corpora/real_roots/proven_coverage_sample1.json",
                     r"stale or dirty _build",
                     transform=prov_stale_build),
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
