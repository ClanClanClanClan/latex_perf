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
  2. for each registered mutation: records the target file (content + mode +
     mtime), applies a known-bad edit, runs the gate, and asserts BOTH a non-zero exit
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

ISOLATION AND PARALLELISM (default). Every gate run happens in a disposable
`git worktree add --detach` copy of HEAD under the system temp directory, with
the working tree's uncommitted and untracked files overlaid (and the index
copied when it differs from HEAD), so a copy reproduces the checkout byte for
byte — the harness PROVES that (sha256 + executable bit of every tracked and
untracked file) before any gate runs and again after the last mutation.
`_build` is a symlink to the source checkout's, so the CLI a gate hashes is
the one it would hash in place. `--jobs` copies (default: CPU count) run
concurrently; each mutation writes its target in ONE copy, runs the gate end
to end, restores the file (content, mode, mtime) and proves it, and checks
`git status` of the copy is unchanged. Verdicts come from the same `classify`
as the in-place mode, on output with the copy's path rewritten to the
checkout's, and are reported in registry order. Every run also sends a CANARY
through the pool — a no-op edit that MUST come out as a surviving mutant — so
a parallel defect that loses or masks a survivor fails the run (exit 2) instead
of reading as a kill. Mutations are computed once, in registry order, before
any gate runs, so registry rot is reported deterministically. The user's
working tree is never written, and no backup ever lands in it (OPEN-108).

Safety of `--in-place` (the original serial mode, kept for debugging against
the real checkout): refuses to run if any target file is git-dirty (the
mutations are in-place; a crash must not be able to eat uncommitted work)
unless CI=true or --force. Every mutation runs under try/finally restore, from
an fsynced backup in .gate-selftest-backups/. Both modes take the
single-instance lock.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import queue
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

MIN_MUTATIONS = 12

# The harness imports gate helpers (e.g. _measurement_provenance) while
# computing mutation payloads; it must not leave __pycache__ in the checkout
# (review LOW-2).
sys.dont_write_bytecode = True
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
        self.rel = target  # repo-relative: the same file in an isolated copy
        self.expect = re.compile(expect_regex, re.S)
        self.expect_src = expect_regex
        self.old, self.new, self.transform = old, new, transform

    def mutated(self, text: str) -> str:
        """The mutated text of the target, or exit 2 on registry rot.

        Pure: the same function feeds the in-place mode (`apply`) and the
        isolated mode (which computes every mutation ONCE, in registry order,
        before any gate runs — so rot is reported deterministically)."""
        if self.transform is not None:
            return self.transform(text)
        n = text.count(self.old)
        if n != 1:
            # Registry rot: the anchor drifted. Loud infra failure, never a skip.
            print(f"[gate-selftests] REGISTRY ROT: anchor for '{self.label}' "
                  f"occurs {n}x in {self.target.name} (need exactly 1). "
                  f"Update the registry deliberately.")
            sys.exit(2)
        return text.replace(self.old, self.new)

    def mutated_bytes(self) -> bytes:
        """Exactly the bytes `apply` would write (read_text + write_text on
        POSIX: universal-newline read, utf-8 encode, no newline translation)."""
        return self.mutated(
            self.target.read_text(encoding="utf-8")).encode("utf-8")

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
        self.target.write_text(self.mutated(text), encoding="utf-8")
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


def unregister_math106(text: str) -> str:
    """Drop MATH-106 from the producer registry (rule_contracts.yaml).

    gen_candidate_backlog --check used to compare its file only with its own
    output, so a registry/classification disagreement was invisible (it
    reported 67 producers against a registry of 164 for weeks). With MATH-106
    unregistered, the OCaml source still calls a fix constructor for it, so
    the registry cross-check must fire while the regenerate-and-diff alone
    stays green (the rendered file does not change)."""
    pat = re.compile(r"(- rule_id: MATH-106\n(?:  .*\n)*?  produces_fix: )true\n")
    out, n = pat.subn(r"\1null\n", text)
    if n != 1:
        print(f"[gate-selftests] REGISTRY ROT: MATH-106's produces_fix: true "
              f"occurs {n}x in rule_contracts.yaml (need exactly 1)")
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
    # (C-72). Without this the mutation would only produce a note. Recorded
    # exactly as every producer records it, from the CLI's resolved path, so a
    # symlinked _build is fingerprinted as the checkout that really built it
    # (review LOW-1: _root(REPO) made this a false blind spot there).
    from _measurement_provenance import cli_build_root as _root
    tgt["cli_build_root"] = _root(
        REPO / "_build/default/latex-parse/src/validators_cli.exe")
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


def strict_admitted_is_clock(text: str) -> str:
    """OPEN-118 (b) / R-CLOCK: an admitted name that IS \\year (\\let to
    the primitive). R-INERT admits it (an integer parameter is none of its
    classes); only the clock rule sees it."""
    d = json.loads(text)
    d["meanings"][_first_admitted(d)] = "\\year"
    return json.dumps(d, indent=1) + "\n"


def strict_admitted_expands_to_clock(text: str) -> str:
    """OPEN-118 (b) / R-CLOCK: an admitted macro whose expansion reaches
    \\time through another macro (the closure, not the name, reads it)."""
    d = json.loads(text)
    d["meanings"][_first_admitted(d)] = "macro:->\\lpclockstamp x"
    d["meanings"]["lpclockstamp"] = "macro:->\\time "
    d["meanings"]["time"] = "\\time"
    return json.dumps(d, indent=1) + "\n"


def strict_admitted_expands_to_random(text: str) -> str:
    """OPEN-118 (b) / R-CLOCK, clock review MEDIUM-1: an admitted macro whose
    expansion reaches \\pdfuniformdeviate (seeded from the real time on every
    run). Before the rule covered the run-dependent pdfTeX primitives, this
    passed both R-INERT and R-CLOCK."""
    d = json.loads(text)
    d["meanings"][_first_admitted(d)] = "macro:->\\lprandom x"
    d["meanings"]["lprandom"] = "macro:->\\pdfuniformdeviate 10 "
    d["meanings"]["pdfuniformdeviate"] = "\\pdfuniformdeviate"
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


def _debt_case(text: str, name: str, edit) -> str:
    """Apply `edit` to the ONE case called `name` of the release-debt fixture;
    registry rot (the case or its expected shape is gone) is exit 2."""
    d = json.loads(text)
    hits = [c for c in d["cases"] if c.get("name") == name]
    if len(hits) != 1 or not edit(hits[0]):
        print(f"[gate-selftests] REGISTRY ROT: release-debt fixture case "
              f"{name!r} is missing or no longer has the shape this "
              f"mutation edits. Update the registry deliberately.")
        sys.exit(2)
    return json.dumps(d, indent=2) + "\n"


def _set_if(case: dict, key: str, old, new) -> bool:
    if case.get(key) != old:
        return False
    case[key] = new
    return True


def debt_merge_max0(text: str) -> str:
    return _debt_case(text, "merge-shape",
                      lambda c: _set_if(c, "max", 1, 0))


def debt_merge_no_tags(text: str) -> str:
    return _debt_case(text, "merge-shape",
                      lambda c: _set_if(c, "clone", "full", "no-tags"))


def debt_merge_shallow(text: str) -> str:
    return _debt_case(text, "merge-shape",
                      lambda c: _set_if(c, "clone", "full", "shallow"))


def debt_merge_version_behind(text: str) -> str:
    def edit(c):
        c["ops"].append({"op": "version", "v": "0.9.0"})
        return True
    return _debt_case(text, "merge-shape", edit)


def debt_release_prep_unbumped(text: str) -> str:
    def edit(c):
        if c["ops"][-1] != {"op": "version", "v": "1.0.1"}:
            return False
        c["ops"].pop()
        return True
    return _debt_case(text, "release-prep", edit)


def debt_side_tag_max35(text: str) -> str:
    return _debt_case(text, "side-branch-tag",
                      lambda c: _set_if(c, "max", 36, 35))


def debt_numeric_order_max2(text: str) -> str:
    return _debt_case(text, "numeric-order",
                      lambda c: _set_if(c, "max", 3, 2))


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
                     "corpora/strict_s0/differential_v2.json",
                     r"FAIL differential: 1 disagreement",
                     transform=strict_differential_one_disagreement),
            # C-85: the published bound must be one over the generator's
            # distribution, not over L_S0.
            Mutation("the differential's bound drops its scope",
                     "corpora/strict_s0/differential_v2.json",
                     r"FAIL differential: the upper bound does not state",
                     transform=strict_bound_scope_dropped),
            # C-85 / R-INERT: a non-inert name admitted.
            Mutation("an admitted name is a conditional (not inert)",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' is not inert: conditional",
                     transform=strict_admitted_not_inert),
            # OPEN-118 known limit (b) / R-CLOCK: a clock reader admitted,
            # directly and through its expansion closure.
            Mutation("an admitted name is the clock primitive \\year",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' reads the clock: it is the "
                     r"run-dependent primitive \\year \(R-CLOCK\)",
                     transform=strict_admitted_is_clock),
            Mutation("an admitted macro expands to \\time",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' reads the clock: expansion "
                     r"reaches the run-dependent primitive \\time via \\lpclockstamp",
                     transform=strict_admitted_expands_to_clock),
            Mutation("an admitted macro expands to \\pdfuniformdeviate",
                     "corpora/contracts/strict/article-s0-signatures.json",
                     r"FAIL signatures: admitted '.*' reads the clock: expansion "
                     r"reaches the run-dependent primitive \\pdfuniformdeviate via \\lprandom",
                     transform=strict_admitted_expands_to_random),
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
                     old="  in_strict_toks C (flatten_doc d) /\\ bounded (flatten_doc d) = true.",
                     new="  in_strict_toks C (flatten_doc d)."),
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
                     old="    bounded (toks_of ks) = true /\\\n    ends_dollar (toks_of ks) = false.\n",
                     new="    bounded (toks_of ks) = true.\n"),
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
                     old='"$n" "$names" "$e" "$@"; \'',
                     new='"$n" "$names" pdflatex "$@"; \''),
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
                     new="        if m is None:\n            return EngineRun(p.returncode, p.stdout + p.stderr, False, p.stdout)\n"
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
                     old="  if ! grep -q 'This is pdfTeX' \"$rundir/$job.log\" 2>/dev/null; then\n",
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
                     old="        env = graded_env(env)\n        self.clear_outputs(Path(cwd), args)\n",
                     new="        self.clear_outputs(Path(cwd), args)\n"),
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
                     old="            run = o.run_pass(workdir, base, o.tex_env(td), secs)\n",
                     new="            run = o.run_pass(workdir, base, dict(os.environ), secs)\n"),
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
            # C-93: a private TMPDIR per run. MEASURED 2026-09-29: a timed-out
            # repstopdf -> gs left /tmp/gs_* in the long-lived container and
            # check_state then refused every later session. One kill per layer.
            Mutation("the per-run environment drops the private TMPDIR",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*oracle_tex_vars carries no private TMPDIR",
                     old="    return {**private_texmf_vars(td), **private_tmp_vars(td), **ORACLE_TEX_VARS}\n",
                     new="    return {**private_texmf_vars(td), **ORACLE_TEX_VARS}\n"),
            Mutation("TMPDIR is no longer forwarded to the engine",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*TMPDIR=None is not the run's private",
                     old='    r"TMPDIR|TMP|TEMP|JAVA_TOOL_OPTIONS)$")',
                     new='    r"TMP|TEMP|JAVA_TOOL_OPTIONS)$")'),
            Mutation("graded_env stops requiring the run's private TMPDIR",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex graded a run whose TMPDIR is ",
                     old="    if not tmp or tmp != want_tmp:\n",
                     new="    if False:\n"),
            Mutation("graded_env stops deriving TMP/TEMP/JAVA_TOOL_OPTIONS",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*TMPDIR=None is not the run's private",
                     old="        out.update(private_tmp_vars(Path(tmp).parent))\n",
                     new="        pass\n"),
            Mutation("the container backend stops checking the run's TMPDIR",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*ran an engine with a TMPDIR outside the work root",
                     old="        make_private_tmp(env or {}, self._inside)\n",
                     new=""),
            Mutation("the oracle stops creating the run's TMPDIR",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*was not created before the engine started",
                     old="        Path(tmp).mkdir(parents=True, exist_ok=True)\n",
                     new="        pass\n"),
            # C-95: a stale PDF from an earlier pass (or run) was read as the
            # confirming pass's, grading an aux-oscillating document compiles.
            Mutation("run_pdflatex stops clearing the previous run's outputs",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*pdflatex shim left an earlier run's",
                     old="        env = graded_env(env)\n        self.clear_outputs(Path(cwd), args)\n",
                     new="        env = graded_env(env)\n"),
            Mutation("run_engine stops clearing the previous run's outputs",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_engine left an earlier run's",
                     old="        self.clear_outputs(Path(cwd), list(args))\n",
                     new=""),
            # C-97: the long-lived container reaps (--init), is bounded
            # (--pids-limit), and no run starts beside a leaked process.
            Mutation("a container without --init is no longer replaced",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*container with no --init: replaced=False",
                     old='            if img != IMAGE or init != "true" or pids != str(PIDS_LIMIT):\n',
                     new='            if img != IMAGE:\n'),
            Mutation("the oracle starts its container without --init",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*new container flags ok=False",
                     old='                         "--label", "lp-oracle=1", "--init",\n',
                     new='                         "--label", "lp-oracle=1",\n'),
            Mutation("a container still without --init after creation is accepted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*docker ignoring --init: replaced=True \(want True\), accepted=True",
                     old='        if ins.stdout.decode().split() != ["true", str(PIDS_LIMIT)]:\n',
                     new='        if False:\n'),
            Mutation("the per-run leak check is skipped",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*ran the engine despite a zombie left",
                     old='lp_leak "$n" || exit 0; ',
                     new=''),
            Mutation("the leak check stops seeing zombies",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*ran the engine despite a zombie left",
                     old='|| ($3 ~ /^Z/ && $4 >= 2) ',
                     new=''),
            Mutation("the --init directories' contents are allowed too",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*session state scan accepted a container whose changed paths are '/usr/sbin/x'",
                     old='            if typ == "d" and path in self.STATE_ALLOWED_DIRS:\n',
                     new='            if path in self.STATE_ALLOWED_DIRS or path.startswith("/usr/"):\n'),
            # Review round 2 of C-95/C-97: pdfTeX's job name is THE name, the
            # PDF verdict is pdfTeX's own report, clearing never follows a
            # symlink, and the container's configuration is in its name.
            Mutation("the job name strips only a lowercase .tex again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*pdftex_jobname no longer gives pdfTeX's MEASURED job names",
                     old='    return name.rpartition(".")[0] if "." in name else name\n',
                     new='    return name[:-4] if name.endswith(".tex") else name\n'),
            Mutation("the PDF verdict trusts a file named .pdf",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*under plan 'forge' graded compiles=True",
                     old='    return (log_r is not None and log_r[0] == "pdf" and log_r[1] >= 1\n',
                     new='    return pdf.is_file() or (log_r is not None and log_r[0] == "pdf" and log_r[1] >= 1\n'),
            Mutation("the PDF verdict reads the FIRST final line (a forged one)",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*final_report on a forged report before the real one",
                     old="    for m in _REPORT.finditer(flat):\n        last = m\n",
                     new="    for m in _REPORT.finditer(flat):\n        last = m\n        break\n"),
            Mutation("false_ready_oracle.sh reads a file named .pdf again",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*run_pdflatex graded plan 'forge'",
                     old='  oracle_pdf_written "$wd" "$base" "$out" 2>/dev/null || pv=$?\n',
                     new='  [ -f "$wd/${base%.tex}.pdf" ] || pv=1\n'),
            Mutation("diff_compile_check.sh reads a file named .pdf again",
                     "scripts/tools/diff_compile_check.sh",
                     r"\[oracle-infra\] FAIL.*diff_compile_check\.sh no longer takes its PDF verdict",
                     old='  oracle_pdf_written "$d" "$base" "$pout" 2>/dev/null || pv=$?\n',
                     new='  [ -s "$d/${base%.tex}.pdf" ] || pv=1\n'),
            Mutation("clearing follows a symlink to its target again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*remove deleted a symlink's TARGET",
                     old='        paths = [Path(p).parent.resolve() / Path(p).name for p in paths]\n',
                     new='        paths = [Path(p).resolve() for p in paths]\n'),
            Mutation("the container name loses its configuration tag",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*container name no longer carries its",
                     old='                     + CONTAINER_CONFIG_TAG)\n',
                     new='                     )\n'),
            Mutation("a grader forms its own output name again (stem + .log)",
                     "scripts/tools/regrade_sample.py",
                     r"\[oracle-infra\] FAIL.*names an engine output or takes a PDF verdict other than through the oracle API.*regrade_sample\.py",
                     old='    log = job_output(work, toplevel, ".log")  # pdfTeX\'s job name (C-95)\n',
                     new='    log = pathlib.Path(work) / (pathlib.Path(toplevel).stem + ".log")\n'),
            Mutation("a symlinked output name is graded again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*graded a document whose t\.pdf is a symlink",
                     old="        if links:\n            raise OracleError(",
                     new="        if False:\n            raise OracleError("),
            Mutation("the cleared outputs omit the log",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*left an earlier run's \['t\.log'\]",
                     old='    RUN_OUTPUTS = (".pdf", ".log", ".fls", ".fmt")\n',
                     new='    RUN_OUTPUTS = (".pdf", ".fls", ".fmt")\n'),
            # C-99 / OPEN-118 review round 3. H1: the document must not write
            # the oracle's evidence, and the PDF verdict needs the terminal and
            # the log to agree. (The supervisor's own inotify logic is killed
            # by the gate's REAL-supervisor checks, which run on Linux only --
            # CI and the pinned image -- so it has no mutation here: on a Mac
            # it would survive.)
            Mutation("the supervisor's evidence is ignored (a second close-write of the log)",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*whose supervisor reported its own log",
                     old='    twice = sorted(n for n, c in ev.get("cw", {}).items() if c > 1)\n',
                     new='    twice = []\n'),
            Mutation("a supervisor without inotify is trusted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*whose supervisor reported no inotify",
                     old='    if ev.get("err") or ev.get("overflow"):\n',
                     new='    if False:\n'),
            Mutation("the terminal and the log need not agree",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_to_fixpoint graded a forged terminal report",
                     old="    if term_r is not None and log_r is not None and term_r[0] != log_r[0]:\n",
                     new="    if False:\n"),
            Mutation("the terminal's final report is not read",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_to_fixpoint graded (a forged terminal report|text after the terminal)",
                     old='    term_r = final_report(stdout, job, "terminal")\n',
                     new='    term_r = None\n'),
            Mutation("text after the terminal's report is accepted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_to_fixpoint graded text after the terminal",
                     old='        ok = b"".join(tail) in terminal_tails(job)\n',
                     new='        ok = True\n'),
            # Review round 3 LOW (fail-closed branches that survived) and
            # round 4 (the alias, \\synctex, HostDiagnostic, a stale allow).
            Mutation("a terminal report with no report in the log is graded",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_to_fixpoint graded a terminal report and a log with none",
                     old="    if term_r is not None and log_r is None:\n",
                     new="    if False:\n"),
            Mutation("a supervisor that printed no evidence line is trusted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*whose supervisor reported no evidence line at all",
                     old="    if m is None:\n        raise OracleError(f\"{what}: the run's supervisor reported no evidence \"\n",
                     new="    if m is None:\n        return stderr\n        raise OracleError(f\"{what}: the run's supervisor reported no evidence \"\n"),
            Mutation("text after the log's report is accepted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*final_report on text after the log's report",
                     old='        ok = all(ln == b"PDF statistics:" or ln.startswith(b" ") for ln in tail)\n',
                     new='        ok = True\n'),
            Mutation("an alias of an evidence file is graded",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*whose supervisor reported an alias of its own log",
                     old="    if alias:\n",
                     new="    if False:\n"),
            Mutation("an evidence line without an alias list is trusted",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*whose supervisor reported no alias list",
                     old="    if not isinstance(alias, list):\n",
                     new="    if False:\n"),
            Mutation("pdfTeX's own SyncTeX line is refused again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*synctex=1 document that ships a page was REFUSED",
                     old='    for ext in (b".synctex.gz", b".synctex"):\n',
                     new='    for ext in ():\n'),
            Mutation("HostDiagnostic is supervised again (every Mac host run refused)",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*HostDiagnostic (refused a host run|ran the evidence supervisor)",
                     old="    supervised = False\n",
                     new="    supervised = True\n"),
            Mutation("get_oracle hands out an unsupervised backend",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*handed out an unsupervised backend",
                     old="    if not _ORACLE.supervised:  # never a grade without the evidence supervisor\n",
                     new="    if False:\n"),
            Mutation("the leak check confirms after one re-sample again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*container leak check on a sibling's zombie reaped after 2 samples",
                     old="    f'while [ -n \"$l\" ] && [ $i -lt {LEAK_CONFIRM_S} ]; do sleep 1; '\n",
                     new="    f'while [ -n \"$l\" ] && [ $i -lt 1 ]; do sleep 1; '\n"),
            Mutation("the leak check keys a process on its state letter again",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*container leak check on a persistent orphan whose state letter alternates",
                     old="""    'm=" $(lp_leak_list) "; k=""; for x in $l; do case "$m" in *" ${x%%:*}:"*) '\n""",
                     new="""    'm=" $(lp_leak_list) "; k=""; for x in $l; do case "$m" in *" $x "*) '\n"""),
            Mutation("the leak check globs a process name",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*container leak check on a persistent zombie",
                     old="    'lp_leak() { set -f; l=$(lp_leak_list); i=0; '\n",
                     new="    'lp_leak() { l=$(lp_leak_list); i=0; '\n"),
            Mutation("a stale OUTPUT_NAME_ALLOW entry is kept",
                     "scripts/tools/check_oracle_infra_grading.py",
                     r"\[oracle-infra\] FAIL.*OUTPUT_NAME_ALLOW entry matches no line",
                     old="OUTPUT_NAME_ALLOW = {\n",
                     new="OUTPUT_NAME_ALLOW = {\n    (\"scripts/tools/diff_real_roots.py\", \"gone\"): \"stale\",\n"),
            # M1: the file argument is one the oracle can name exactly.
            Mutation("an unnameable file argument reaches the engine",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*run_pdflatex accepted file argument",
                     old="    check_file_argument(p, cwd, what)\n",
                     new=""),
            # stdin: no engine run inherits the grader's stdin.
            Mutation("the native engine run inherits the grader's stdin",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*native engine run read the grader's stdin",
                     old="                                 cwd=cwd, env=env, stdin=subprocess.DEVNULL,\n",
                     new="                                 cwd=cwd, env=env,\n"),
            Mutation("the container's docker client inherits the grader's stdin",
                     "scripts/tools/_oracle.py",
                     r"\[oracle-infra\] FAIL.*docker client of an engine run read the grader's stdin",
                     old="                               timeout=timeout + 90, stdin=subprocess.DEVNULL)\n",
                     new="                               timeout=timeout + 90)\n"),
            # M2: the inverted naming check. The four evasions the review
            # measured against the old pattern list, and a grader that stops
            # taking its PDF verdict from the oracle.
            Mutation("an output name from stem+'.log' (no spaces, single quotes)",
                     "scripts/tools/regrade_sample.py",
                     r"\[oracle-infra\] FAIL.*names an engine output or takes a PDF verdict other than through the oracle API.*regrade_sample\.py",
                     old='    log = job_output(work, toplevel, ".log")  # pdfTeX\'s job name (C-95)\n',
                     new="    log = pathlib.Path(work) / (pathlib.Path(toplevel).stem+'.log')\n"),
            Mutation("an output name from with_suffix('.log')",
                     "scripts/tools/regrade_sample.py",
                     r"\[oracle-infra\] FAIL.*names an engine output or takes a PDF verdict other than through the oracle API.*regrade_sample\.py",
                     old='    log = job_output(work, toplevel, ".log")  # pdfTeX\'s job name (C-95)\n',
                     new="    log = (pathlib.Path(work) / toplevel).with_suffix('.log')\n"),
            Mutation("an output name from rsplit in a transitive oracle client",
                     "scripts/tools/bisect_apply_fixes_break.py",
                     r"\[oracle-infra\] FAIL.*names an engine output or takes a PDF verdict other than through the oracle API.*bisect_apply_fixes_break\.py",
                     old='    log = job_output(work, toplevel, ".log")  # pdfTeX\'s job name (C-95)\n',
                     new='    log = work / (toplevel.rsplit(".", 1)[0] + ".log")\n'),
            Mutation("a shell output name from ${base%.*}",
                     "scripts/tools/false_ready_oracle.sh",
                     r"\[oracle-infra\] FAIL.*names an engine output or takes a PDF verdict other than through the oracle API.*false_ready_oracle\.sh",
                     old='  cp "$rundir/$job.log" "$logfile" 2>/dev/null || : > "$logfile"\n',
                     new='  cp "$rundir/${base%.*}.log" "$logfile" 2>/dev/null || : > "$logfile"\n'),
            Mutation("a grader stops taking its PDF verdict from the oracle",
                     "scripts/tools/regrade_sample.py",
                     r"\[oracle-infra\] FAIL.*regrade_sample\.py: takes no PDF verdict from the oracle",
                     old="    return r.rc, r.passes, r.pdf  # r.pdf: _oracle.pdf_written (C-99)\n",
                     new="    return r.rc, r.passes, True\n"),
            # Review round 3 (c): no cell is decided from error text.
            Mutation("a cell is decided from the first error's text again",
                     "scripts/tools/diff_real_roots.py",
                     r"\[oracle-infra\] FAIL.*forged infrastructure error and then failed was scored 'ungraded-infra'",
                     old='        out["cell"] = "ungraded-timeout"\n    else:\n        compiles = row_compiles(out)\n',
                     new='        out["cell"] = "ungraded-timeout"\n    elif out["pdflatex_rc"] != 0 and "not found" in first_full:\n'
                         '        out["cell"] = "ungraded-infra"\n    else:\n        compiles = row_compiles(out)\n'),
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
    # ADR-011 §6 release-debt gate. Its real input is git state (tags,
    # clone depth, merge shape), which a file edit in a worktree copy cannot
    # vary portably — a copy of a TAGGED HEAD has debt 0, and a release-prep
    # HEAD is exempt, so mutating the live threshold would not reliably kill.
    # The gate therefore runs its SAME `evaluate` on throwaway repos built
    # from the cases of this JSON, and each mutation changes one case. The
    # clean cases kill code mutants on their own: merge-shape passes at max 1
    # ONLY under first-parent counting; release-prep passes ONLY through the
    # exemption, on a PATCH bump; non-release-tags passes ONLY if pre-release,
    # annotation, spike and leading-zero v-tags are ignored. And every run
    # cross-checks MAX_FIRST_PARENT_DEBT against the N in ADR-011 §6.
    GateTest(
        "check_release_debt",
        [PY, f"{TOOLS}/check_release_debt.py", "--selftest-fixture",
         "scripts/tools/fixtures/release_debt_selftest.json"],
        "pure",
        [
            Mutation("--max 0 on an untagged HEAD (debt 1)", 'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[merge-shape\] FAIL: release debt is 1 first-parent "
                     r"commit\(s\) past v1\.0\.0, limit 0",
                     transform=debt_merge_max0),
            # C-55 / OPEN-101: a clone without tags must be exit 2, never a
            # pass. The INFRA line is printed only on the exit-2 path.
            Mutation("clone without tags", 'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[merge-shape\] INFRA \(exit 2, never a pass\): no "
                     r"release tag",
                     transform=debt_merge_no_tags),
            Mutation("shallow clone (actions/checkout default depth)", 'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[merge-shape\] INFRA \(exit 2, never a pass\): "
                     r"shallow clone",
                     transform=debt_merge_shallow),
            Mutation("dune-project version behind the reachable tag", 'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[merge-shape\] FAIL: dune-project version 0\.9\.0 is "
                     r"BEHIND",
                     transform=debt_merge_version_behind),
            # The exemption must be exactly 'dune-project newer than T':
            # without the bump the same 31 commits are debt.
            Mutation("release-prep history without the version bump", 'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[release-prep\] FAIL: release debt is 30 first-parent "
                     r"commit\(s\) past v1\.0\.0, limit 1",
                     transform=debt_release_prep_unbumped),
            # C-116: T must be the highest release tag reachable from HEAD,
            # not `git describe`'s nearest (an older hotfix tag on a merged
            # branch), or the exemption passes any amount of debt.
            Mutation("debt past v2.0.0 with an older tag on a merged branch",
                     'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[side-branch-tag\] FAIL: release debt is 36 "
                     r"first-parent commit\(s\) past v2\.0\.0, limit 35",
                     transform=debt_side_tag_max35),
            # T is ordered as a version, not as a name: by name v1.9.0 sorts
            # above v1.10.0 (on this repo v27.1.9 above v27.1.64), and the
            # exemption would then pass any debt.
            Mutation("debt past v1.10.0 with v1.9.0 sorting higher by name",
                     'scripts/tools/fixtures/release_debt_selftest.json',
                     r"\[numeric-order\] FAIL: release debt is 3 "
                     r"first-parent commit\(s\) past v1\.10\.0, limit 2",
                     transform=debt_numeric_order_max2),
            # The constant is the owner's ADR-011 §6 decision: raising it in
            # one place without the other must not pass.
            Mutation("ADR-011 §6 N edited without the constant",
                     "docs/v27/adr/ADR-011-fund-track-R-and-demote-apply-fixes.md",
                     r"INFRA \(exit 2, never a pass\): ADR-011 §6 states "
                     r"N = 26 but MAX_FIRST_PARENT_DEBT is 25",
                     old="**Decision.** N = 25 counts",
                     new="**Decision.** N = 26 counts"),
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
        "gen_candidate_backlog", [PY, f"{TOOLS}/gen_candidate_backlog.py", "--check"],
        "pure",
        [
            Mutation("a producer the OCaml source wires is missing from the "
                     "producer registry (the backlog gate checked only its own "
                     "output, honesty sweep 2026-09-30)",
                     "specs/rules/rule_contracts.yaml",
                     r"classified producer\(s\) not in the registry: MATH-106",
                     transform=unregister_math106),
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

LOCK_NAME = ".gate-selftests.lock"
BACKUP_DIR = ".gate-selftest-backups"


def run_gate(cmd, cwd: Path = REPO) -> tuple[int, str]:
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                           timeout=GATE_TIMEOUT)
    except subprocess.TimeoutExpired:
        return -1, "GATE TIMEOUT — treated as a crash, never as a kill"
    return r.returncode, r.stdout + r.stderr


def classify(g, m, rc: int, out: str) -> str | None:
    """THE verdict, shared by both modes: None = killed with the expected
    message; otherwise the failure line this run must report."""
    if rc == 0:
        return (f"{g.name} / '{m.label}': gate PASSED a known-bad "
                f"mutation — it is blind to this defect class")
    if "Traceback (most recent call last)" in out or rc == -1:
        # A crash is NEVER a kill, whatever the regex says: a crashing gate
        # prints its own source line, which can contain the very words the
        # regex expects (measured: a KeyError in check_known_false_ready
        # emitted "baseline" twice).
        return (f"{g.name} / '{m.label}': gate CRASHED on the "
                f"mutation instead of detecting it — a crash is "
                f"not detection. Output head: {out[:300]!r}")
    if not m.expect.search(out):
        return (f"{g.name} / '{m.label}': gate failed but WITHOUT "
                f"the expected message /{m.expect_src}/ — it is "
                f"failing for the wrong reason. Output head: "
                f"{out[:300]!r}")
    return None


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
    # A gate need not be named check_*: gen_candidate_backlog.py --check is
    # a spec-drift gate with kill-tests too (honesty sweep, 2026-09-30).
    invoked |= set(re.findall(r"scripts/tools/([a-z_0-9]+\.py)", sd + ci + pf))
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


class HarnessInfra(Exception):
    """The harness itself could not establish a trustworthy run (exit 2)."""


def _git(args, cwd, check=True) -> bytes:
    r = subprocess.run(["git", "--no-optional-locks", *args], cwd=cwd,
                       capture_output=True)
    if check and r.returncode != 0:
        raise HarnessInfra(
            f"`git {' '.join(map(str, args))}` failed in {cwd}: "
            f"{r.stderr.decode('utf-8', 'replace').strip()}")
    return r.stdout


def _zpaths(raw: bytes) -> list[str]:
    return [os.fsdecode(p) for p in raw.split(b"\0") if p]


def _fingerprint(root: Path, paths) -> dict:
    """Content + executable bit (or link target) of every path that exists."""
    fp = {}
    for p in paths:
        f = root / p
        if f.is_symlink():
            fp[p] = ("link", os.readlink(f))
        elif f.is_file():
            fp[p] = (sha(f), bool(f.stat().st_mode & 0o111))
    return fp


class SourceState:
    """What an isolated copy must reproduce: HEAD, the git index, and every
    tracked or untracked-unignored file of the working tree, byte for byte."""

    def __init__(self):
        self.head = _git(["rev-parse", "HEAD"], REPO).decode().strip()
        tracked = _zpaths(_git(["ls-files", "-z"], REPO))
        untracked = [p for p in _zpaths(_git(
            ["ls-files", "-z", "--others", "--exclude-standard"], REPO))
            if p.split("/")[0] not in (LOCK_NAME, BACKUP_DIR)]
        # Working-tree differences from HEAD (staged or not, incl. deletions).
        changed = _zpaths(_git(["diff", "--name-only", "-z", "HEAD"], REPO))
        self.overlay = sorted(set(changed) | set(untracked))
        # A staged state that differs from HEAD (a `git add`ed new file is
        # tracked here and would be untracked in a bare HEAD checkout, which
        # `git ls-files`-driven gates would see).
        self.index_dirty = subprocess.run(
            ["git", "--no-optional-locks", "diff", "--cached", "--quiet",
             "HEAD"], cwd=REPO).returncode != 0
        self.paths = sorted(set(tracked) | set(untracked))
        self.fingerprint = _fingerprint(REPO, self.paths)


class Copy:
    """One disposable git worktree of the source state, owned by one worker
    at a time. The user's working tree is never written by isolated mode."""

    def __init__(self, root: Path):
        self.root = root
        self.status0 = b""

    def status(self) -> bytes:
        return _git(["status", "--porcelain", "-z", "--untracked-files=no"],
                    self.root)


def make_copy(base: Path, i: int, src: SourceState) -> Copy:
    root = base / f"w{i}"
    # Hooks off: a post-checkout hook must not run in (or on) a copy.
    _git(["-c", "core.hooksPath=/dev/null", "worktree", "add", "--detach",
          "--quiet", str(root), src.head], REPO)
    c = Copy(root)
    for p in src.overlay:
        # _build is linked below, never overlaid: a SYMLINKED _build is not
        # matched by .gitignore's directory-only '_build/' and so shows up as
        # untracked (review MEDIUM-1: FileExistsError in make_copy).
        if Path(p).parts[:1] == ("_build",):
            continue
        s, d = REPO / p, root / p
        if d.is_symlink() or d.is_file():
            d.unlink()
        if s.is_symlink() or s.is_file():
            d.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(s, d, follow_symlinks=False)
    if src.index_dirty:
        idx = Path(_git(["rev-parse", "--path-format=absolute",
                         "--git-path", "index"], REPO).decode().strip())
        cidx = Path(_git(["rev-parse", "--path-format=absolute",
                          "--git-path", "index"], root).decode().strip())
        shutil.copy2(idx, cidx)
        subprocess.run(["git", "update-index", "-q", "--refresh"], cwd=root,
                       capture_output=True)
    # Build products are read-only inputs of the binary level (and of pure
    # gates that consult a CLI when one exists). A symlink, not a copy: the
    # resolved path is the SOURCE checkout, so C-72's build-root fingerprint
    # of the CLI is the same one the in-place run computes.
    b = REPO / "_build"
    if b.exists():
        link = root / "_build"
        if link.is_symlink() or link.is_file():
            link.unlink()
        os.symlink(b.resolve(), link)
    got = _fingerprint(root, src.paths)
    if got != src.fingerprint:
        bad = sorted(p for p in set(got) | set(src.fingerprint)
                     if got.get(p) != src.fingerprint.get(p))
        raise HarnessInfra(f"isolated copy {root} does not reproduce the "
                           f"working tree: {bad[:10]}")
    return c


def remove_copies(base: Path) -> None:
    """Deregister and delete EVERY copy under `base` — including one whose
    creation failed half-way, which never made it into the worker list."""
    leftovers = []
    for root in sorted(base.glob("w*")):
        link = root / "_build"
        if link.is_symlink():
            link.unlink()  # never let a recursive delete follow it
        r = subprocess.run(["git", "worktree", "remove", "--force", "--force",
                            str(root)], cwd=REPO, capture_output=True)
        if r.returncode != 0:
            leftovers.append(str(root))
    shutil.rmtree(base, ignore_errors=True)
    if leftovers:
        print(f"[gate-selftests] WARNING: could not deregister worktree(s) "
              f"{leftovers}; `git worktree prune` clears the stale entries")


def run_isolated(gates, jobs: int, records: list) -> int:
    """Every gate run happens in a disposable worktree copy; `jobs` copies
    run concurrently. Verdicts are the in-place mode's, byte for byte:
    same `classify`, output with the copy's path rewritten to REPO's."""
    # Every mutation computed ONCE, in registry order, BEFORE any gate runs:
    # registry rot is reported deterministically and never from a thread.
    payload = {}
    for gi, g in enumerate(gates):
        for mi, m in enumerate(g.mutations):
            payload[gi, mi] = m.mutated_bytes()

    src = SourceState()
    n_tasks = sum(len(g.mutations) for g in gates) + 1
    n = max(1, min(jobs, n_tasks))
    base = Path(tempfile.mkdtemp(prefix="gate-selftests-")).resolve()
    copies = []
    try:
        # Distinct basenames, so concurrent `worktree add`s never contend
        # for the same .git/worktrees/<name> entry.
        with ThreadPoolExecutor(max_workers=n) as ex:
            futs = [ex.submit(make_copy, base, i, src) for i in range(n)]
        for f in futs:
            copies.append(f.result())  # raises the first failure, if any
        # Refresh each copy's index once its files are older than the index
        # (git re-hashes "racily clean" entries on every status otherwise:
        # measured 0.10 s -> 0.03 s per status, one status per task).
        time.sleep(1.1)
        for c in copies:
            subprocess.run(["git", "update-index", "-q", "--refresh"],
                           cwd=c.root, capture_output=True)
            c.status0 = c.status()
        print(f"[gate-selftests] isolated mode: {n} worktree cop"
              f"{'y' if n == 1 else 'ies'} of HEAD {src.head[:12]}"
              f"{f' + {len(src.overlay)} working-tree file(s)' if src.overlay else ''}"
              f", {n} gate run(s) at a time; the working tree is never "
              f"mutated")
        free: queue.Queue = queue.Queue()
        for c in copies:
            free.put(c)

        def norm(out: str, c: Copy) -> str:
            return out.replace(str(c.root), str(REPO))

        def clean_run(g):
            c = free.get()
            try:
                t = time.monotonic()
                rc, out = run_gate(g.cmd, c.root)
                secs = time.monotonic() - t
                if c.status() != c.status0:
                    raise HarnessInfra(
                        f"{g.name}'s clean run modified tracked files in "
                        f"{c.root}")
                return rc, norm(out, c), secs
            finally:
                free.put(c)

        def mutation_run(g, m, data: bytes):
            c = free.get()
            try:
                tgt = c.root / m.rel
                orig = tgt.read_bytes()
                st = tgt.stat()
                t = time.monotonic()
                try:
                    tmp = tgt.with_name(tgt.name + ".mutate-tmp")
                    tmp.write_bytes(data)
                    os.chmod(tmp, st.st_mode)
                    os.replace(tmp, tgt)
                    rc, out = run_gate(g.cmd, c.root)
                finally:
                    tmp = tgt.with_name(tgt.name + ".restore-tmp")
                    tmp.write_bytes(orig)
                    os.chmod(tmp, st.st_mode)
                    os.replace(tmp, tgt)
                    os.utime(tgt, ns=(st.st_atime_ns, st.st_mtime_ns))
                secs = time.monotonic() - t
                now = tgt.stat()
                if (tgt.read_bytes() != orig or now.st_mode != st.st_mode
                        or now.st_mtime_ns != st.st_mtime_ns):
                    raise HarnessInfra(
                        f"restoration of {tgt} in its isolated copy is NOT "
                        f"identical (content, mode or mtime) — the harness "
                        f"is broken; no verdict of this run can be trusted")
                if c.status() != c.status0:
                    raise HarnessInfra(
                        f"{g.name} / '{m.label}' left tracked files modified "
                        f"in {c.root} beyond its restored target")
                return rc, norm(out, c), secs
            finally:
                free.put(c)

        with ThreadPoolExecutor(max_workers=n) as ex:
            # Phase 1 — every gate clean. A red gate cannot be selftested.
            base_res = list(ex.map(clean_run, gates))
            for g, (rc, out, secs) in zip(gates, base_res):
                records.append(dict(gate=g.name, kind="baseline", label=None,
                                    rc=rc, secs=secs, verdict=None, out=out))
            for g, (rc, out, _) in zip(gates, base_res):
                if rc != 0:
                    print(f"[gate-selftests] ABORT: {g.name} is ALREADY RED "
                          f"before any mutation — fix the gate first, then "
                          f"selftest it")
                    print(out[:800])
                    return 2

            # Phase 2 — every mutation, longest gate first (the clean run
            # predicts its mutations' cost), plus the CANARY: a no-op edit
            # that goes through the same pool, the same verdict and the same
            # aggregation, and MUST come out as a surviving mutant. If it does
            # not, the parallel machinery can mask a survivor, and nothing
            # this run says can be trusted.
            gi0 = min(range(len(gates)), key=lambda i: base_res[i][2])
            g0 = gates[gi0]
            canary = Mutation("harness canary: a no-op edit, which MUST be "
                              "reported as a surviving mutant",
                              g0.mutations[0].rel, r"(?!)")
            payload["canary"] = (REPO / canary.rel).read_bytes()
            order = sorted((k for k in payload if k != "canary"),
                           key=lambda k: (-base_res[k[0]][2], k)) + ["canary"]
            pairs = {k: ((g0, canary) if k == "canary"
                         else (gates[k[0]], gates[k[0]].mutations[k[1]]))
                     for k in payload}
            futs = {k: ex.submit(mutation_run, *pairs[k], payload[k])
                    for k in order}
            res = {k: f.result() for k, f in futs.items()}

            # Aggregate in REGISTRY order, canary last, through one path.
            failures = []
            keys = sorted(k for k in res if k != "canary") + ["canary"]
            for k in keys:
                g, m = pairs[k]
                rc, out, secs = res[k]
                v = classify(g, m, rc, out)
                records.append(dict(gate=g.name, kind="canary" if k ==
                                    "canary" else "mutation", label=m.label,
                                    rc=rc, secs=secs, verdict=v, out=out))
                if v is not None:
                    failures.append(v)
            want = (f"{g0.name} / '{canary.label}': gate PASSED a known-bad "
                    f"mutation — it is blind to this defect class")
            if failures.count(want) != 1:
                print(f"[gate-selftests] FATAL: the harness canary (a no-op "
                      f"edit to {canary.rel} under {g0.name}) was NOT "
                      f"reported as a surviving mutant — the parallel "
                      f"machinery can mask a survivor, so no verdict of this "
                      f"run can be trusted. Canary result: rc={res['canary'][0]}")
                return 2
            failures.remove(want)

            # Phase 3 — every copy still reproduces the working tree, then
            # every gate clean again (in any copy: they are all proven equal).
            for c in copies:
                got = _fingerprint(c.root, src.paths)
                if got != src.fingerprint:
                    print(f"[gate-selftests] FATAL: isolated copy {c.root} no "
                          f"longer reproduces the working tree after the "
                          f"mutations — the selftest damaged its inputs")
                    return 2
            post_res = list(ex.map(clean_run, gates))
            for g, (rc, out, secs) in zip(gates, post_res):
                records.append(dict(gate=g.name, kind="post", label=None,
                                    rc=rc, secs=secs, verdict=None, out=out))
            for g, (rc, out, _) in zip(gates, post_res):
                if rc != 0:
                    print(f"[gate-selftests] FATAL: {g.name} is red AFTER "
                          f"restoration — the selftest damaged its inputs")
                    print(out[:800])
                    return 2
    finally:
        remove_copies(base)
    return report(gates, failures)


def report(gates, failures) -> int:
    if failures:
        print(f"[gate-selftests] FAIL: {len(failures)} blind spot(s)")
        for f in failures:
            print(f"  - {f}")
        return 1
    ran = sum(len(g.mutations) for g in gates)
    print(f"[gate-selftests] PASS: {ran} mutation(s) across "
          f"{len(gates)} gate(s) — every one killed its gate with the expected "
          f"message, and every restoration is byte-identical.")
    return 0


def run_in_place(gates, records: list) -> int:
    """The original serial mode: each mutation edits the WORKING TREE.

    Kept for debugging a single gate against the real checkout; isolated mode
    is the default. Backups live on disk before the mutation does."""
    # ⚠ BACKUPS LIVE ON DISK BEFORE THE MUTATION DOES. v1 held the backup only
    # in process memory with a truncate-write restore and no subprocess
    # timeout — a hard kill (SIGKILL skips finally) in the mutation window
    # left the tree mutated with NOTHING on disk to recover from. Now: the
    # original bytes are written to .gate-selftest-backups/<name> and fsynced
    # BEFORE the target is touched, the restore goes through a temp file +
    # os.replace (atomic on POSIX), and the backup is deleted only after the
    # sha256 round-trip is proven.
    bdir = REPO / BACKUP_DIR
    bdir.mkdir(exist_ok=True)

    failures = []
    try:
        for g in gates:
            t = time.monotonic()
            rc, out = run_gate(g.cmd)
            records.append(dict(gate=g.name, kind="baseline", label=None,
                                rc=rc, secs=time.monotonic() - t,
                                verdict=None, out=out))
            if rc != 0:
                print(f"[gate-selftests] ABORT: {g.name} is ALREADY RED before "
                      f"any mutation — fix the gate first, then selftest it")
                print(out[:800])
                return 2
            for m in g.mutations:
                before = sha(m.target)
                st = m.target.stat()
                bfile = bdir / m.target.name
                bfile.write_bytes(m.target.read_bytes())
                bfd = os.open(bfile, os.O_RDONLY)
                os.fsync(bfd)
                os.close(bfd)
                try:
                    t = time.monotonic()
                    m.apply()
                    rc, out = run_gate(g.cmd)
                    v = classify(g, m, rc, out)
                    records.append(dict(gate=g.name, kind="mutation",
                                        label=m.label, rc=rc,
                                        secs=time.monotonic() - t,
                                        verdict=v, out=out))
                    if v is not None:
                        failures.append(v)
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
            t = time.monotonic()
            rc, out = run_gate(g.cmd)
            records.append(dict(gate=g.name, kind="post", label=None, rc=rc,
                                secs=time.monotonic() - t, verdict=None,
                                out=out))
            if rc != 0:
                print(f"[gate-selftests] FATAL: {g.name} is red AFTER "
                      f"restoration — the selftest damaged its inputs")
                print(out[:800])
                return 2
    finally:
        try:
            bdir.rmdir()  # succeeds only when empty = every backup consumed
        except OSError:
            print(f"[gate-selftests] WARNING: {bdir} is not empty — a backup "
                  f"was not consumed; inspect before trusting the tree")
    return report(gates, failures)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--level", choices=["pure", "binary", "all"], default="all")
    ap.add_argument("--force", action="store_true",
                    help="--in-place only: run even if target files are "
                         "git-dirty")
    ap.add_argument("--jobs", "-j", type=int, default=os.cpu_count() or 1,
                    help="isolated worktree copies run concurrently "
                         "(default: CPU count)")
    ap.add_argument("--in-place", action="store_true",
                    help="the old serial mode: mutate the working tree itself "
                         "(backup-restored, refuses a dirty tree)")
    ap.add_argument("--only", action="append", default=[], metavar="GATE",
                    help="restrict to the named gate(s); a PARTIAL run")
    ap.add_argument("--inject-survivor", action="store_true",
                    help="harness self-test: register a no-op mutation on the "
                         "first selected gate; the run MUST fail with exit 1")
    ap.add_argument("--report-json", metavar="PATH",
                    help="write every gate run (rc, seconds, verdict, output)")
    ns = ap.parse_args()
    if ns.jobs < 1:
        ap.error("--jobs must be >= 1")

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

    if ns.only:
        unknown = set(ns.only) - {g.name for g in gates}
        if unknown:
            print(f"[gate-selftests] --only names no selected gate: "
                  f"{sorted(unknown)}")
            return 2
        gates = [g for g in gates if g.name in ns.only]
        print(f"[gate-selftests] note: PARTIAL run (--only) — "
              f"{len(gates)} gate(s); this is not the selftest CI requires")
    if ns.inject_survivor:
        g = gates[0]
        g.mutations = list(g.mutations) + [Mutation(
            "INJECTED SURVIVOR (--inject-survivor): a no-op edit no gate can "
            "detect", g.mutations[0].rel, r"(?!)", transform=lambda t: t)]

    if ns.in_place:
        # In-place mutations must not be able to eat uncommitted work.
        targets = sorted({str(m.target.relative_to(REPO))
                          for g in gates for m in g.mutations})
        # "CI" must mean CI: direnv/nix setups export CI=false, and any
        # non-empty string is truthy in Python — so `CI=false` used to skip
        # the dirty check.
        in_ci = os.environ.get("CI", "").strip().lower() in ("1", "true",
                                                             "yes")
        if not (ns.force or in_ci):
            r = subprocess.run(["git", "--no-optional-locks", "status",
                                "--porcelain", "--", *targets],
                               cwd=REPO, capture_output=True, text=True)
            if r.stdout.strip():
                print("[gate-selftests] REFUSING: mutation targets are "
                      "git-dirty (a crash mid-mutation would eat uncommitted "
                      "work):\n" + r.stdout + "  commit/stash first, or pass "
                      "--force")
                return 2

    # ⚠ A SINGLE-INSTANCE LOCK, because two concurrent runs poison each
    # other's backups: B (started inside A's mutation window) backs up A's
    # MUTATED bytes as its "original", both restore "successfully", and the
    # tree ends permanently mutated while both exit green. Isolated mode takes
    # it too: it COPIES the working tree, and a copy taken inside an in-place
    # run's mutation window would carry that run's mutant. O_EXCL is atomic;
    # a stale lock is reported with its pid, never silently stolen.
    lock = REPO / LOCK_NAME
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, f"{os.getpid()}\n".encode())
        os.close(fd)
    except FileExistsError:
        print(f"[gate-selftests] REFUSING: {lock} exists (pid "
              f"{lock.read_text().strip()!r}). Another selftest run is active "
              f"— or crashed; inspect, restore from {BACKUP_DIR}/ "
              f"if needed, then remove the lock by hand.")
        return 2

    records: list = []
    try:
        if ns.in_place:
            return run_in_place(gates, records)
        bdir = REPO / BACKUP_DIR
        if bdir.is_dir() and any(bdir.iterdir()):
            print(f"[gate-selftests] WARNING: {bdir} is not empty — a backup "
                  f"of an earlier in-place run was not consumed; inspect "
                  f"before trusting the tree")
        try:
            return run_isolated(gates, ns.jobs, records)
        except HarnessInfra as exc:
            print(f"[gate-selftests] FATAL (harness infrastructure): {exc}")
            return 2
    finally:
        lock.unlink(missing_ok=True)
        if ns.report_json:
            Path(ns.report_json).write_text(json.dumps(records, indent=1),
                                            encoding="utf-8")


if __name__ == "__main__":
    sys.exit(main())
