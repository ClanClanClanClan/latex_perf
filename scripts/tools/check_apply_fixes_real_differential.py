#!/usr/bin/env python3
"""Gate: the default fixer must not break MORE real papers than the pinned
baseline (OPEN-071).

WHY THIS GATE EXISTS, and why the one that already existed was not enough.

`check_apply_fixes_roundtrip` asserts the right invariant -- fix a document,
recompile it, and it must still compile -- and it is BLOCKING in tex-oracle.
It nevertheless stayed green through five separate producers that destroyed
real papers, because of its CORPUS, not its logic:

  * 78 in-house documents. grep for `xymatrix`, `elsarticle`,
    `DeclareMathSymbol` or `chardef` across the whole gate corpus returns ZERO
    hits, and `--apply-fixes-for SCRIPT-001` changed 0 of 74 fixtures while
    changing 30 of 80 real roots.
  * `\\input` children are excluded by construction, and a parent is never
    recompiled after a child is fixed -- which is precisely the STRUCT-001
    shape, where a preamble injected into a fragment kills its parent.

Every fixture in it was written by someone who already knew which bug they
were guarding, so it cannot contradict the producers. This gate closes that:
its corpus is real arXiv papers nobody chose, and its fix scope is the whole
tree.

WHAT IT CHECKS. It does NOT re-measure -- CI has no corpus, by design (12 GB,
non-redistributable, mixed licences). It checks the committed artefact:

  1. the recorded break count has not risen above BASELINE_BROKEN;
  2. the artefact is not silently stale -- same provenance ratchet as
     check_project_state (commit distance on latex-parse/src) plus, when the
     binary is present, the cli_sha256 the artefact recorded;
  3. every row's `cell` follows from its own recorded rc pair, so the summary
     cannot drift away from the rows it claims to count (C-45).

Refresh with:
    python3 scripts/tools/gen_apply_fixes_real_differential.py --repo . \\
        --offset 2000 --n 40
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

# TWO WINDOWS, AND THE GATE RATCHETS BOTH. The tuned window is the one whose
# breaks the fixes were designed from; the virgin window has never been used to
# design anything. Measured 2026-09-12, immediately after fixing MATH-009,
# MATH-014 and PKG-011: TUNED 0/38 = 0.0%, VIRGIN 6/39 = 15.4%.
# 2026-09-13, after OPEN-097: those two windows read 0.0% and 2.6%, and a
# never-used window read 18.4% -- statistically indistinguishable from the
# 15.4% of the round before. Two rounds of producer fixes, no measurable
# out-of-sample improvement. See OPEN-100.
#
# ⚠ THE ZERO DOES NOT GENERALISE, AND IT MUST NEVER BE QUOTED ALONE. This is
# C-39/OPEN-034 reproduced on a second corpus: the in-sample number after a
# round of fixes is an optimistic estimate of the fixer's real damage, because
# the sample IS the thing the fixes were fitted to. Same idiom as
# corpora/real_roots' sample 1 / sample 2 split, for the same reason.
# ⚠ THREE WINDOWS, AND ONLY THE LAST ONE IS QUOTABLE ALONE.
#
# A window becomes TUNED the moment a fix is designed from its breaks, and the
# rate on a tuned window collapses toward zero whether or not the underlying
# defect class was closed. That has now happened twice in a row -- offset 2000
# went to 0.0% while a fresh 2100 read 15.4%, then 2100 went to 2.6% while a
# fresh 2300 read 18.4%. So the fresh slot ROTATES: whenever a fix is designed
# from the breaks in `results_fresh.json`, that file's window joins the tuned
# family and the fresh slot must be re-pointed at an offset that has never been
# used for anything. Grep the repo for "offset <n>" before choosing one.
#
# Measured 2026-09-13, all three with cli d2780297, after the OPEN-097 fix:
#   2000 (tuned twice)          0/38 =  0.0%
#   2100 (tuned by OPEN-097)    1/39 =  2.6%
#   2300 (never used)           7/38 = 18.4%   <-- the honest number
ARTEFACTS = [
    ("corpora/apply_fixes_real/results.json", "tuned", 0),
    ("corpora/apply_fixes_real/results_virgin.json", "tuned-by-OPEN-097", 1),
    ("corpora/apply_fixes_real/results_fresh.json", "FRESH (offset 2300)", 7),
]
ARTEFACT = ARTEFACTS[0][0]
# The number of real COMPILING papers the default fixer is currently known to
# break. A RATCHET: lower it when a producer is fixed, in the same commit that
# refreshes the artefact. Raising it needs a ledger row saying why the
# regression is acceptable -- there is no such reason yet.
BASELINE_BROKEN = 7
MAX_MEASUREMENT_LAG = 5


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ns = ap.parse_args()
    repo = pathlib.Path(ns.repo).resolve()
    all_findings = []
    summary_lines = []
    for artefact_rel, window, baseline in ARTEFACTS:
        rc = _check_one(repo, artefact_rel, window, baseline, all_findings,
                        summary_lines)
        if rc == 2:
            return 1
    if all_findings:
        print("[apply-fixes-real] FAIL:")
        for x in all_findings:
            print("   -", x)
        return 1
    for line in summary_lines:
        print(line)
    return 0


def _check_one(repo, artefact_rel, window, baseline, findings, summary_lines):
    ARTEFACT = artefact_rel
    BASELINE_BROKEN = baseline
    f = repo / ARTEFACT

    if not f.is_file():
        findings.append(
            f"{ARTEFACT} is missing. The real-paper fixer rate must live in an "
            f"artefact, not in prose (OPEN-071).")
        return 0
    try:
        doc = json.loads(f.read_text())
    except (json.JSONDecodeError, OSError) as exc:
        findings.append(f"{ARTEFACT} unreadable: {exc}")
        return 0

    rows = doc.get("rows") or []
    summary = doc.get("summary") or {}
    prov = doc.get("provenance") or {}

    # ── 1. the cells must follow from the rows (C-45) ────────────────────
    recount = {"preserved": 0, "broken": 0, "excluded-did-not-compile": 0}
    for r in rows:
        rid, cell = r.get("arxiv_id", "?"), r.get("cell", "")
        rc0, rc1 = r.get("rc_before"), r.get("rc_after")
        if cell == "excluded-did-not-compile":
            if rc0 == 0:
                findings.append(f"{rid}: excluded as non-compiling but "
                                f"rc_before=0. Excluding a paper that DOES "
                                f"compile shrinks the denominator and flatters "
                                f"the rate.")
        elif cell in ("preserved", "broken"):
            want = "preserved" if rc1 == 0 else "broken"
            if want != cell:
                findings.append(f"{rid}: cell {cell!r} but rc_after={rc1}")
            if rc0 != 0:
                findings.append(f"{rid}: graded {cell!r} but rc_before={rc0}; "
                                f"only papers that compiled BEFORE are gradable")
        else:
            findings.append(f"{rid}: unknown cell {cell!r}")
        recount[cell] = recount.get(cell, 0) + 1
    for k in ("preserved", "broken"):
        if summary.get(k) != recount.get(k):
            findings.append(f"summary.{k}={summary.get(k)} but the rows say "
                            f"{recount.get(k)} — the published number does not "
                            f"count the measurement it cites")

    # ── 2. the ratchet ───────────────────────────────────────────────────
    broken = recount.get("broken", 0)
    compiled = recount.get("preserved", 0) + broken
    if broken > BASELINE_BROKEN:
        findings.append(
            f"[{window}] the default fixer breaks {broken} of {compiled} real COMPILING "
            f"papers; the pinned baseline is {BASELINE_BROKEN}. A fix producer "
            f"has regressed. Bisect it — first-error attribution in a "
            f"multi-rule fixer is a hypothesis until bisected (OPEN-076).")
    elif broken < BASELINE_BROKEN:
        findings.append(
            f"[{window}] the fixer now breaks {broken} of {compiled}, BELOW the pinned "
            f"baseline of {BASELINE_BROKEN}. Lower BASELINE_BROKEN to {broken} "
            f"in this commit — a ratchet that is never tightened stops being "
            f"one.")

    # ── 3. staleness ─────────────────────────────────────────────────────
    sha = prov.get("measured_at_sha")
    if not sha:
        findings.append(f"{ARTEFACT} has no provenance.measured_at_sha, so its "
                        f"staleness cannot be checked (OPEN-080).")
    else:
        r = subprocess.run(["git", "--no-optional-locks", "rev-list", "--count",
                            f"{sha}..HEAD", "--", "latex-parse/src"],
                           cwd=repo, capture_output=True, text=True)
        if r.returncode == 0 and r.stdout.strip().isdigit():
            behind = int(r.stdout.strip())
            if behind > MAX_MEASUREMENT_LAG:
                findings.append(
                    f"{ARTEFACT} is {behind} commits behind HEAD on "
                    f"latex-parse/src (limit {MAX_MEASUREMENT_LAG}); the fixer "
                    f"has changed since this was measured.")
    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    if cli.is_file() and prov.get("cli_sha256"):
        h = hashlib.sha256()
        with cli.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        if h.hexdigest() != prov["cli_sha256"]:
            findings.append(
                f"{ARTEFACT} was produced by a DIFFERENT binary "
                f"(records {prov['cli_sha256'][:12]}…, built is "
                f"{h.hexdigest()[:12]}…).")

    pct = (100.0 * broken / compiled) if compiled else 0.0
    summary_lines.append(
        f"[apply-fixes-real] {window.upper():<7} {broken}/{compiled} = "
        f"{pct:.1f}% of real COMPILING papers broken (baseline "
        f"{BASELINE_BROKEN}); "
        f"{recount.get('excluded-did-not-compile', 0)} excluded, pdflatex "
        f"already rejects them.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
