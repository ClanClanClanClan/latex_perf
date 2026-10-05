#!/usr/bin/env python3
"""Generate the MEASURED-POSITION block of docs/v27/PROJECT_STATE.md.

Why this exists. docs/v27/ROADMAP.md carried hand-typed numbers and they rotted:
its banner, its false-READY count, its "0 over-rejection" claim and its
version-of-record were each factually false while check_roadmap_facts.py
reported "Roadmap facts check passed" -- that gate asserts only the numbers it
knows about, and uses re.search, so of two contradictory matrices only the first
was ever checked.

The lesson is not "write a better gate". It is that a number stated by hand in
prose WILL drift. So every number in PROJECT_STATE.md's position table is
generated from the artefact that owns it, and check_project_state.py regenerates
and diffs -- the same authenticity pattern check_release_integrity.py already
applies to project_facts.yaml.

Sources, one owner per fact:
  corpora/false_ready/manifest.json     fixture baseline           (quantity b)
  corpora/apply_fixes/manifest.json     fixer residual damage
  corpora/real_roots/results.json       real-paper matrix          (quantity c)
  corpora/real_roots/results_sample3.json  the VIRGIN sample (OPEN-119)
  scripts/tools/diff_compile_check.sh   differential allowlist     (quantity a)
  governance/project_facts.yaml         version, proof counts
  .github/required-status-checks.json   required CI contexts
  (release debt is NOT in the block: check_release_debt.py gates it, C-13)

Usage:  gen_project_state.py [--repo .]           print the block
        gen_project_state.py --write              splice it into PROJECT_STATE.md
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
# THE one definition of "certified" (in a tier, FOREIGN excluded; OPEN-126).
from gen_proven_coverage import in_tier_certified  # noqa: E402

BEGIN = "<!-- BEGIN GENERATED: measured-position -->"
END = "<!-- END GENERATED: measured-position -->"
DOC = Path("docs/v27/PROJECT_STATE.md")

# The ten sample-3 ids that the repo already NAMES (OPEN-118's pre-draw check):
# each was found by a WHOLE-CORPUS sweep, never by a windowed experiment, so
# the window is untouched by windowed work but not virgin in the strict sense.
# They are published as their own split so the reader can see whether they
# move the reading. Fixed BEFORE the draw; never extend this list after
# looking at sample-3 outcomes (OPEN-119).
SAMPLE3_NAMED_IDS = frozenset({
    # fix_meaning_review.json (the fixer meaning review)
    "2506.14455v1", "2506.23790v1", "2507.08441v1", "2507.08520v1",
    "2507.08692v1", "2507.09560v1", "2507.09851v1",
    # verdict-channel findings in the ledger (2507.08692v1 is in both sets)
    "2507.04008v1", "2507.08309v1", "2507.08913v1",
})
SAMPLE3_LABEL = "**sample 3 (VIRGIN; sealed, OPEN-119)**"
CELLS = ("true-READY", "true-NOT-READY", "FALSE-READY", "false-NOT-READY",
         "ungraded-infra", "ungraded-timeout")


def allowlist_count(repo: Path) -> int:
    t = (repo / "scripts/tools/diff_compile_check.sh").read_text()
    m = re.search(r'KNOWN_FALSE_READY="\n(.*?)\n"', t, re.DOTALL)
    if not m:
        raise SystemExit("FATAL: KNOWN_FALSE_READY block not found")
    return len([l for l in m.group(1).splitlines() if l.strip().endswith(".tex")])


def binom_upper95(k: int, n: int) -> float:
    """Exact (Clopper-Pearson) one-sided 95% upper bound on a rate k/n.

    ADR-012 publishes strict_wrong with its upper bound, because 0/n is weak
    evidence when n is small: for k = 0 this is 1 - 0.05**(1/n), which the
    design rounds to the rule of three, 3/n. Pure Python, bisection on the
    binomial CDF, so the generator has no new dependency.
    """
    from math import comb
    if n <= 0:
        return 1.0
    if k >= n:
        return 1.0

    def cdf(p: float) -> float:
        return sum(comb(n, i) * p**i * (1 - p)**(n - i) for i in range(k + 1))

    lo, hi = k / n, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if cdf(mid) > 0.05:
            lo = mid
        else:
            hi = mid
    return hi


def build(repo: Path) -> str:
    fr = json.loads((repo / "corpora/false_ready/manifest.json").read_text())
    # A fixture whose expected_cli is READY is a LIVE false-READY only when
    # pdflatex REJECTS it. Rows graded `compiles` are ACCEPT-PINS: pdflatex
    # accepts them and READY is the CORRECT verdict, so counting them as
    # "known false-READYs" overstated row (b) by the number of accept-pins
    # (14 of 29 at the time this was fixed). This is the same rule
    # check_known_false_ready.py and manifest.baseline.false_ready_total use;
    # they had drifted apart from this generator.
    live = [f for f in fr["fixtures"]
            if f["expected_cli"] == "READY" and f.get("pdflatex") != "compiles"]
    accept_pins = [f for f in fr["fixtures"]
                   if f["expected_cli"] == "READY" and f.get("pdflatex") == "compiles"]
    af = json.loads((repo / "corpora/apply_fixes/manifest.json").read_text())
    kb = af["known_broken"]

    rr_path = repo / "corpora/real_roots/results.json"
    rr = json.loads(rr_path.read_text()) if rr_path.is_file() else None

    facts = {}
    for line in (repo / "governance/project_facts.yaml").read_text().splitlines():
        m = re.match(r"^(version|release_date):\s*'?([^'\s]+)'?", line)
        if m:
            facts[m.group(1)] = m.group(2)

    req = json.loads((repo / ".github/required-status-checks.json").read_text())["checks"]
    # DELIBERATELY NOT INCLUDED: `git describe --tags` commit distance.
    #
    # It is the natural way to show release debt, and it was in this block until
    # the gate immediately failed on the very next commit. A number that changes
    # on EVERY commit makes the regenerate-and-diff check fire on every PR, which
    # trains the reader to regenerate without looking -- and a gate people
    # silence is worse than one that never existed. The block below therefore
    # holds only facts that change when an ARTEFACT changes. Release debt is
    # GATED instead: check_release_debt.py (ADR-011 §6, required spec-drift)
    # computes it from git on every run, so there is no stored figure to rot.

    L = [BEGIN, "",
         "> Generated by `scripts/tools/gen_project_state.py`. **Do not hand-edit.**",
         "> `check_project_state.py` regenerates this block and fails on any diff,",
         "> so a number here can only be wrong if its source artefact is wrong.", ""]

    L += ["### The three quantities that must never be conflated", "",
          "Each grades a different corpus. They are disjoint. Conflating them is the",
          "single most repeated error in this project's history.", "",
          "| | corpus | value | what moves it |",
          "|---|---|---|---|"]
    # Count the documents the DIFFERENTIAL GRADES — that is what row (a)
    # describes. diff_compile_check.sh:125-130 enumerates `*.tex` and skips only
    # `*_part.tex` (\input children); fail_no_documentclass.tex IS graded (it is
    # a deliberately-failing fixture), so the denominator is 65, not the 64
    # files that contain a literal \documentclass.
    #
    # ⚠ THIS LINE HAS NOW BEEN WRONG TWICE, ONCE IN EACH DIRECTION (C-29).
    # v1 tested the SUBSTRING "documentclass" and published 65 — the right
    # number by accident, because fail_no_documentclass.tex says "There is no
    # documentclass here" in PROSE. v2 "fixed" it to a \\documentclass regex
    # and published 64 — a defensible-looking derivation of the WRONG quantity,
    # shipped inside a commit titled "three honesty defects". The number is not
    # "files containing \documentclass"; it is "documents the matrix grades".
    # Derive it by the SAME RULE the differential uses, and pin the semantic
    # with an assertion so the two scripts cannot drift apart silently.
    cc_dir = repo / "corpora/compile_check"
    graded = [f for f in cc_dir.glob("*.tex") if not f.name.endswith("_part.tex")]
    n_cc = len(graded)
    assert (cc_dir / "fail_no_documentclass.tex") in graded, (
        "semantic pin: fail_no_documentclass.tex is a GRADED document "
        "(diff_compile_check.sh skips only *_part.tex); if this fires, the "
        "enumeration rules have drifted apart — reconcile them, do not delete me")
    L.append(f"| **(a)** differential allowlist | `corpora/compile_check`, {n_cc} "
             f"hand-authored docs | **{allowlist_count(repo)}** | S6/S7-style detectors |")
    sf = sum(1 for f in live if f["pdflatex"] == "strong-fatal")
    eh = sum(1 for f in live if f["pdflatex"] == "error-halt")
    L.append(f"| **(b)** fixture baseline | `corpora/false_ready`, {len(fr['fixtures'])} fixtures "
             f"| **{len(live)}** ({sf} strong-fatal, {eh} error-halt; "
             f"{len(accept_pins)} accept-pins excluded) | R7 fix ranks |")
    if rr:
        c = rr["counts"]
        graded = sum(v for k, v in c.items() if not k.startswith("ungraded"))
        L.append(f"| **(c)** **real papers** | `corpora/real_roots`, {rr['frame']['n']} arXiv trees "
                 f"(frame {rr['frame']['frame_size']}) | **{c.get('FALSE-READY',0)} / {graded} = "
                 f"{100*c.get('FALSE-READY',0)/graded:.1f}%** | the heuristic "
                 f"tier's soundness (the strict tier's is `strict_wrong`, below) |")
    L.append("")

    if rr:
        c = rr["counts"]
        graded = sum(v for k, v in c.items() if not k.startswith("ungraded"))
        ok = c.get("true-READY", 0) + c.get("true-NOT-READY", 0)
        fnr = c.get("false-NOT-READY", 0)
        nr = fnr + c.get("true-NOT-READY", 0)
        L += ["### Real-paper position", "",
              f"Oracle `{rr['oracle']['version']}`, {rr['oracle']['distribution']}, "
              + (f"pinned image `{rr['oracle']['image']}` ({rr['oracle'].get('arch', '?')}, "
                 f"{rr['oracle'].get('backend', '?')} backend), "
                 if rr['oracle'].get('image') else
                 "graded by a HOST TeX Live, not the pinned image (pre-baseline), ")
              + f"protocol `{rr['oracle']['protocol']}`.", "",
              "| cell | n |", "|---|---|"]
        for k in ("true-READY", "true-NOT-READY", "FALSE-READY", "false-NOT-READY",
                  "ungraded-infra", "ungraded-timeout"):
            L.append(f"| {k} | {c.get(k, 0)} |")
        L += ["",
              f"- **Correct verdicts: {ok}/{graded} = {100*ok/graded:.1f}%**",
              f"- **Over-rejection: {fnr}/{graded} = {100*fnr/graded:.1f}%** — i.e. "
              f"**{100*fnr/nr:.1f}% of every NOT-READY verdict issued on a real paper is wrong**",
              f"- **False-READY: {c.get('FALSE-READY',0)}/{graded} = "
              f"{100*c.get('FALSE-READY',0)/graded:.1f}%**, against a definition requiring zero",
              ""]

    # ── THE NORTH-STAR METRIC ITSELF ────────────────────────────────────
    # ROADMAP.md: "Proven-verdict coverage at ZERO false-READY on a committed
    # corpus = (real papers that get a *proven* verdict matching pdflatex,
    # with zero false-READY) / (all real papers)."  Until 2026-09-04 this
    # block published three EMPIRICAL rates and never the metric, so eight
    # consecutive PRs optimised a proxy. It is generated here, from committed
    # per-document artefacts, so it cannot be quietly replaced again.
    def proven_block(path, label):
        f = repo / path
        if not f.is_file():
            return []
        raw = json.loads(f.read_text())
        # Phase A: the artefact gained provenance + summary; rows moved under
        # a key. Accept both shapes so a stale artefact fails LOUDLY on the
        # count rather than silently reading zero rows.
        rows = raw["rows"] if isinstance(raw, dict) else raw
        n = len(rows)
        certified_ok = sum(1 for r in rows
                           if in_tier_certified(r) and r["cell"] == "true-READY")
        core_ok = sum(1 for r in rows
                      if in_tier_certified(r) and r["cell"] == "true-READY"
                      and r.get("profile") == "lp-core")
        heur = sum(1 for r in rows if not in_tier_certified(r) and r.get("ready"))
        fr_cert = sum(1 for r in rows
                      if r["cell"] == "FALSE-READY" and in_tier_certified(r))
        return [f"| {label} | {core_ok}/{n} = {100*core_ok/n:.1f}% | "
                f"{certified_ok}/{n} = {100*certified_ok/n:.1f}% | {heur} | {fr_cert} |"]

    # C-43 taught the drift: this rate was restated as prose in SIX files and
    # went stale the moment a re-grade moved it. It is computed here now, so
    # there is exactly one place it can be wrong.
    def cert_error_row(path, label):
        f = repo / path
        if not f.is_file():
            return []
        raw = json.loads(f.read_text())
        rows = raw["rows"] if isinstance(raw, dict) else raw
        fails = {"true-NOT-READY", "FALSE-READY"}   # pdflatex did NOT compile
        out = []
        for tier_label, sel in (("any tier", rows),
                                ("LP-Core", [r for r in rows
                                             if r.get("profile") == "lp-core"])):
            cert = [r for r in sel if in_tier_certified(r)]
            bad = [r for r in cert if r["cell"] in fails]
            if not cert:
                continue
            out.append(f"| {label} | {tier_label} | {len(bad)}/{len(cert)} = "
                       f"{100*len(bad)/len(cert):.1f}% |")
        return out

    # ── ADR-012: THE NORTH STAR IS STRICT-TIER COVERAGE ─────────────────
    # A document counts only when the CLI printed a PROVEN verdict (the TIER
    # line's tier token is "proven") AND that verdict matches pdflatex. The
    # tier token is recorded per row by gen_proven_coverage.py. A row without
    # it comes from a binary older than ADR-012 and is refused LOUDLY rather
    # than read as "not proven" (C-65: never let a missing field read as 0).
    def strict_row(path, label):
        f = repo / path
        if not f.is_file():
            return []
        raw = json.loads(f.read_text())
        rows = raw["rows"] if isinstance(raw, dict) else raw
        missing = [r["id"] for r in rows if "verdict_tier" not in r]
        if missing:
            raise SystemExit(
                f"FATAL: {path} has {len(missing)} rows without verdict_tier "
                f"(first: {missing[0]}). It predates ADR-012; regenerate it "
                f"with scripts/tools/gen_proven_coverage.py.")
        n = len(rows)
        proven = [r for r in rows if r["verdict_tier"] == "proven"]
        ok = [r for r in proven
              if (r["verdict_kind"] == "PROVEN-READY" and r["cell"] == "true-READY")
              or (r["verdict_kind"] == "PROVEN-NOT-READY"
                  and r["cell"] == "true-NOT-READY")]
        wrong = len(proven) - len(ok)
        k = len(proven)
        ub = ("n/a — no proven verdicts, so no evidence either way" if k == 0
              else f"{100*binom_upper95(wrong, k):.1f}% of {k}")
        heur = sum(1 for r in rows if r["verdict_tier"] == "heuristic")
        foreign = sum(1 for r in rows if r["verdict_tier"] == "foreign")
        return [f"| {label} | **{len(ok)}/{n} = {100*len(ok)/n:.1f}%** | "
                f"{wrong} | {ub} | {heur} | {foreign} |"]

    sr = strict_row("corpora/real_roots/proven_coverage_sample1.json",
                    "sample 1 (tuned)")
    # ADR-012: sample 2 was used for the strict-tier design statistics, so it is
    # DESIGN-SEEN for this metric and must never be labelled virgin here. The
    # North Star's virgin sample is sample 3 (ADR-012 decision 7).
    sr += strict_row("corpora/real_roots/proven_coverage_sample2.json",
                     "sample 2 (design-seen since ADR-012)")
    s3_strict = strict_row("corpora/real_roots/proven_coverage_sample3.json",
                           SAMPLE3_LABEL)
    sr += s3_strict
    if s3_strict:
        virgin_prose = (
            "The North Star is defined on a VIRGIN sample, and that is "
            "sample 3 (frame offset 720, ranks 721-920), drawn and graded "
            "once, under the frozen oracle (CI's digest-pinned TeX Live "
            "image, ADR-012 decision 7), after every earlier graded artefact "
            "had been re-graded under it (OPEN-118). It is SEALED for "
            "measurement only (OPEN-119): nothing is fixed, tuned or triaged "
            "on it, and a future fix is validated elsewhere before sample 3 "
            "is re-measured. Samples 1 and 2 are shown for comparison and "
            "are not virgin: sample 1 is tuned and sample 2 has been "
            "design-seen since ADR-012. ")
    else:
        virgin_prose = (
            "The North Star is defined on a VIRGIN sample, and neither row "
            "below is one: sample 1 is tuned and sample 2 has been "
            "design-seen since ADR-012. The headline figure will come from "
            "sample 3 (frame offset 720, ranks 721-920), drawn and graded "
            "only after every graded artefact has been re-graded under the "
            "frozen oracle, CI's digest-pinned TeX Live image (ADR-012 "
            "decision 7); that re-grade is done and moved no cell "
            "(OPEN-118). ")
    if sr:
        L += ["### Strict-tier coverage — THE North-Star metric (ADR-012)", "",
              "A document counts only when the CLI prints a **PROVEN** verdict "
              "(READY or NOT-READY, decided inside the contract-bounded strict "
              "tier by the Coq-extracted decider) **and** that verdict matches "
              "the pinned pdflatex. `strict_wrong` counts every PROVEN verdict "
              "that disagrees with pdflatex; ADR-012 also counts a wrong reason "
              "or location, which the strict battery and the generated "
              "differential grade. It must be zero, and it is published with "
              "its exact one-sided 95% upper bound, because zero out of a small "
              "number is weak evidence. **In milestone M0 the strict-tier "
              "membership predicate is a stub that returns false, so no "
              "verdict is proven and this number is zero by measurement.** "
              + virgin_prose +
              "Definitions: "
              "`docs/v27/STRICT_TIER_DESIGN.md` §E and "
              "`docs/v27/adr/ADR-012-contract-bounded-proven-tier.md`.", "",
              "| corpus | strict-tier coverage (PROVEN = pdflatex) | strict_wrong "
              "| 95% upper bound on the strict_wrong rate | heuristic verdicts "
              "| foreign verdicts |",
              "|---|---|---|---|---|---|"] + sr + [""]

    pb = proven_block("corpora/real_roots/proven_coverage_sample1.json",
                      "sample 1 (tuned)")
    pb += proven_block("corpora/real_roots/proven_coverage_sample2.json",
                       "**sample 2 (untuned; design-seen since ADR-012)**")
    pb += proven_block("corpora/real_roots/proven_coverage_sample3.json",
                       SAMPLE3_LABEL)
    if pb:
        L += ["### Heuristic-tier statistic: premise-certified coverage (NOT a proof)", "",
              "**This is a heuristic-tier statistic, not the North Star and not "
              "a proof (ADR-012, decision 2).** Before ADR-012 it was published "
              "as the North-Star metric under the name *proven-verdict "
              "coverage*. It counts documents where the Coq-extracted checker "
              "certified its PREMISES over the abstract model "
              "(`PREMISE-CERTIFIED`) **and** pdflatex compiled the document; "
              "the CLI renders every such verdict as `LIKELY OK (heuristic; "
              "premise-certified)`. It is NOT a proof that the document "
              "compiles: the second table below gives how often that reading "
              "is wrong, computed from the same artefacts. Restricting to "
              "LP-Core does not reliably reduce it — the direction differs "
              "between the two samples, so no general claim is made either way "
              "(C-43 withdrew the earlier one). The LP-Core column is the "
              "heuristic figure this project publishes, and only under this "
              "heading.",
              "",
              "| corpus | premise-certified (LP-Core) | certified (any tier) | uncertified READYs | certified FALSE-READY |",
              "|---|---|---|---|---|"] + pb + [""]
        ce = (cert_error_row("corpora/real_roots/proven_coverage_sample1.json",
                             "sample 1 (tuned)")
              + cert_error_row("corpora/real_roots/proven_coverage_sample2.json",
                               "**sample 2 (untuned; design-seen since ADR-012)**")
              + cert_error_row("corpora/real_roots/proven_coverage_sample3.json",
                               SAMPLE3_LABEL))
        if ce:
            L += ["#### Heuristic tier: how often the certificate is wrong", "",
                  "Certified documents that pdflatex nevertheless REJECTS. This "
                  "is the honest size of the gap between "
                  "\"the premises hold over the abstract model\" and "
                  "\"this document compiles\".", "",
                  "| corpus | scope | certified but pdflatex fails |",
                  "|---|---|---|"] + ce + [""]

    # ── OUT-OF-SAMPLE POSITION ──────────────────────────────────────────
    s2_path = repo / "corpora/real_roots/results_sample2.json"
    if s2_path.is_file():
        s2 = json.loads(s2_path.read_text())
        c2 = s2["counts"]
        g2 = sum(v for k, v in c2.items() if not k.startswith("ungraded"))
        ok2 = c2.get("true-READY", 0) + c2.get("true-NOT-READY", 0)
        L += ["### Out-of-sample position (sample 2 — untuned)", "",
              "Ranks 201-400 of the same deterministic ordering. **No fix has "
              "ever been tuned against these documents**, so for the heuristic "
              "tier this remains the out-of-sample position. It is no longer "
              "virgin: ADR-012's strict-tier design used sample 2 for its "
              "configuration statistics, so it is design-seen, and the "
              "strict-tier North Star waits for sample 3. Sample 1 is burned "
              "for soundness claims: every fix in the #565-#572 run was "
              "measured against it, so its false-READY rate is an optimistic "
              "estimate and must never be quoted alone.", "",
              "| cell | n |", "|---|---|"]
        for k in ("true-READY", "true-NOT-READY", "FALSE-READY", "false-NOT-READY",
                  "ungraded-infra"):
            L.append(f"| {k} | {c2.get(k, 0)} |")
        L += ["",
              f"- **Correct verdicts: {ok2}/{g2} = {100*ok2/g2:.1f}%**",
              f"- **False-READY: {c2.get('FALSE-READY',0)}/{g2} = "
              f"{100*c2.get('FALSE-READY',0)/g2:.1f}%** — the in-sample zero "
              f"does NOT generalise (OPEN-034)", ""]

    # ── THE VIRGIN POSITION (sample 3, OPEN-119) ────────────────────────
    s3_path = repo / "corpora/real_roots/results_sample3.json"
    if s3_path.is_file():
        s3 = json.loads(s3_path.read_text())
        ids3 = {d["arxiv_id"] for d in s3["docs"]}
        if not SAMPLE3_NAMED_IDS <= ids3:
            raise SystemExit(
                f"FATAL: SAMPLE3_NAMED_IDS names ids outside sample 3: "
                f"{sorted(SAMPLE3_NAMED_IDS - ids3)}")

        def conf_row(label, counts):
            g = sum(v for k, v in counts.items() if not k.startswith("ungraded"))
            ok = counts.get("true-READY", 0) + counts.get("true-NOT-READY", 0)
            ung = sum(v for k, v in counts.items() if k.startswith("ungraded"))

            def pct(k):
                return f"{k}/{g} = {100*k/g:.1f}%" if g else f"{k}/0"
            return (f"| {label} | {g} | {pct(ok)} "
                    f"| {pct(counts.get('FALSE-READY', 0))} "
                    f"| {pct(counts.get('false-NOT-READY', 0))} "
                    f"| {counts.get('true-NOT-READY', 0)} | {ung} |")

        def counts_of(docs):
            out = {}
            for d in docs:
                out[d["cell"]] = out.get(d["cell"], 0) + 1
            return out

        o3, f3 = s3["oracle"], s3["frame"]
        _rg3 = repo / "corpora/oracle_baseline/regrade_open126_sample3.json"
        rg3 = json.loads(_rg3.read_text()) if _rg3.is_file() else None
        L += ["### Virgin position (sample 3 — sealed for measurement, OPEN-119)", "",
              f"Frame offset {f3['offset']}, ranks {f3['offset'] + 1}-"
              f"{f3['offset'] + f3['n']} of the same deterministic ordering "
              f"(frame {f3['frame_size']}); drawn and graded ONCE"
              + (f", the pdflatex side re-graded under the final oracle at "
                 f"`{str(s3['oracle_regraded_at_sha'])[:8]}` (OPEN-126: "
                 f"{rg3['summary']['cells_moved']} of {rg3['summary']['rows']} "
                 f"cells and {rg3['summary']['outcomes_moved']} rc/PDF/pass "
                 f"outcomes moved, corpora/oracle_baseline/"
                 f"regrade_open126_sample3.json)"
                 if s3.get("oracle_regraded_at_sha") and rg3 else "")
              + f", CLI "
              f"verdicts measured at "
              f"`{str(s3.get('measured_at_sha', '?'))[:8]}`, under the pinned "
              f"image `{o3.get('image', '?')}` ({o3.get('arch', '?')}, "
              f"{o3.get('backend', '?')} backend), protocol "
              f"`{o3.get('protocol', '?')}`. **This is the heuristic tier's "
              "first reading on documents no windowed experiment was fitted to; "
              "10 of its ids were named by whole-corpus sweeps before the draw "
              "and are split out below.** It is sealed: no failure on it is inspected, fixed or "
              "triaged, and a change is validated on other documents before "
              "this sample is re-measured (OPEN-119). The rows beside it are "
              "NOT virgin and are shown only for comparison.", "",
              "| sample | graded | correct | FALSE-READY | false-NOT-READY "
              "| true-NOT-READY | ungraded |",
              "|---|---|---|---|---|---|---|"]
        if rr:
            L.append(conf_row("sample 1 (tuned)", rr["counts"]))
        if s2_path.is_file():
            L.append(conf_row("sample 2 (design-seen)",
                              json.loads(s2_path.read_text())["counts"]))
        L.append(conf_row(SAMPLE3_LABEL, s3["counts"]))
        rest = [d for d in s3["docs"] if d["arxiv_id"] not in SAMPLE3_NAMED_IDS]
        named = [d for d in s3["docs"] if d["arxiv_id"] in SAMPLE3_NAMED_IDS]
        L.append(conf_row(f"sample 3 without the {len(named)} repo-named ids",
                          counts_of(rest)))
        L.append(conf_row(f"sample 3, the {len(named)} repo-named ids only",
                          counts_of(named)))
        L += ["", "| sample 3 cell | n |", "|---|---|"]
        for k in CELLS:
            L.append(f"| {k} | {s3['counts'].get(k, 0)} |")
        L += ["",
              f"The {len(named)} repo-named ids were named by whole-corpus "
              "sweeps before the draw (OPEN-118) and are split out so their "
              "effect is visible; the list was fixed before the draw and is "
              "never extended after looking at outcomes.", ""]

    L += ["### Fixer residual (auto-fix channel)", "",
          "| property | rows |", "|---|---|"]
    for k in ("breaks_compile", "degrades_verdict", "not_idempotent", "manufactured_false_ready"):
        L.append(f"| `{k}` | {sum(1 for r in kb if r.get(k))} |")
    L += ["", f"Total recorded rows: **{len(kb)}**. "
              f"pdflatex-graded: `{af.get('pdflatex_graded')}`.", ""]

    L += ["### Infrastructure", "",
          f"- Required CI contexts: **{len(req)}** — {', '.join(sorted(c['context'] for c in req))}",
          f"- Version of record: **{facts.get('version','?')}** "
          f"(`project_facts.yaml` release_date {facts.get('release_date','?')})",
          "- Release debt: not shown here, because it changes on every commit "
          "(C-13). It is **gated** by `scripts/tools/check_release_debt.py` in "
          "required `spec-drift`: HEAD more first-parent commits past the nearest "
          "`v*` tag than its ADR-011 §6 limit fails, unless `dune-project` already "
          "names a newer version (a release in preparation); a `dune-project` "
          "version behind that tag also fails (OPEN-013). Run the script for "
          "today's figure.",
          "", END]
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--write", action="store_true")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    block = build(repo)
    if not ns.write:
        print(block)
        return 0
    doc = repo / DOC
    t = doc.read_text()
    if BEGIN not in t or END not in t:
        raise SystemExit(f"FATAL: markers missing in {DOC}")
    pre, rest = t.split(BEGIN, 1)
    _, post = rest.split(END, 1)
    doc.write_text(pre + block + post)
    print(f"[gen-project-state] wrote the generated block into {DOC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
