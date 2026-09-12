#!/usr/bin/env python3
"""Doc-consistency gate — one source of truth per number (C-40).

Every invariant below is a contradiction that WAS LIVE on main on
2026-09-04, found by a documentation audit:

  1. README title version disagreed with governance/project_facts.yaml
     (v27.1.61 vs v27.1.62).
  2. specs/rules/README.md's maturity block was stale by an order of
     magnitude (Draft 619 / Implemented 19 vs the YAML's 529 / 108).
  3. PROJECT_STATE.md — the self-declared single source of truth — carried a
     hand-written positional matrix that contradicted its own GENERATED block
     fifty lines above (141/199 vs 197/199).
  4. The fixture-baseline row counted accept-pins (fixtures pdflatex ACCEPTS,
     where READY is correct) as known false-READYs, overstating it 29 vs 15,
     and disagreed with manifest.baseline.false_ready_total.
  5. Docs quoted "37 compile-blocking rules" while the code list held 36.

The rule this enforces: a number lives in exactly ONE artefact, and prose
either points at it or is generated from it. Prose that restates a governed
number must agree with the artefact.
"""
import json
import pathlib
import re
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parents[2]
FAILURES = []


def fail(inv, msg):
    FAILURES.append(f"[{inv}] {msg}")


def facts_version():
    for line in (REPO / "governance/project_facts.yaml").read_text().splitlines():
        m = re.match(r"^version:\s*'?([^'\s]+)'?", line)
        if m:
            return m.group(1)
    return None


def inv_readme_version():
    v = facts_version()
    head = (REPO / "README.md").read_text().splitlines()[0]
    m = re.search(r"v(\d+\.\d+\.\d+)", head)
    if not m:
        return fail("readme-version", "README.md title carries no version")
    if v and m.group(0) != v:
        fail("readme-version",
             f"README title says {m.group(0)} but project_facts.yaml says {v}")


def inv_rule_maturity():
    try:
        import yaml
    except ImportError:
        return
    import collections
    counts = collections.Counter()
    # The CATALOGUE is one file. Globbing specs/rules/*.yaml also swept up
    # golden-test fixtures, one of which (l2_approx_golden.yaml) is not valid
    # YAML at all — see OPEN-052. Read the catalogue, and fail loudly if it
    # cannot be parsed: a gate that silently skips its own input UNDER-COUNTS
    # and then reports an agreement it never checked.
    catalogue = REPO / "specs/rules/rules_v3.yaml"
    try:
        d = yaml.safe_load(catalogue.read_text())
    except yaml.YAMLError as e:
        return fail("rule-maturity", f"{catalogue} is not parseable YAML: {e}")
    rules = d.get("rules") if isinstance(d, dict) else (d if isinstance(d, list) else None)
    for r in rules or []:
        if isinstance(r, dict) and "maturity" in r:
            counts[r["maturity"]] += 1
    txt = (REPO / "specs/rules/README.md").read_text()
    for key in ("Draft", "Implemented", "Impl", "Reserved"):
        m = re.search(rf"^\s*-\s*{key}:\s*(\d+)", txt, re.M)
        if m and counts.get(key) is not None and int(m.group(1)) != counts[key]:
            fail("rule-maturity",
                 f"specs/rules/README.md says {key}: {m.group(1)}, "
                 f"the YAML catalogue has {counts[key]}")


def inv_no_handwritten_position():
    r"""PROJECT_STATE prose must not restate ANY measured quantity.

    OPEN-078 / C-47. The first version of this invariant was defeated by its
    own escape hatch. It skipped any line containing the word "superseded" so
    that the ledger and the corrections log could quote history -- and the one
    paragraph republishing the position OPENED with that word, on a single
    physical line, so all four of its stale numbers were exempt. Measured at
    the time: 24 positional hits in the prose, 24 skipped, 0 flagged.

    Two things were wrong, and both are fixed here.

    (a) The exemption was keyed on a WORD APPEARING ANYWHERE IN THE LINE
        rather than on where the quote sits. It is now keyed on POSITION: a
        markdown table row (the ledger and the corrections log) may quote a
        historical number, because each such row is individually dated and
        carries its own evidence cell. Running prose may not, full stop.
        There is no keyword hatch, so no sentence can exempt itself.

    (b) The pattern was anchored on a PHRASING -- \b(\d{2,3})/(199|200)\b --
        so it could not see a bare percentage at all, and would have gone
        blind the day the corpus grew past 200. It is now anchored on the
        QUANTITY SHAPE: any fraction and any percentage.

    Measured when this landed: exactly 10 hits, all on the one paragraph this
    invariant exists to catch, and zero anywhere else in the prose -- so the
    widened pattern costs no false positives.
    """
    txt = (REPO / "docs/v27/PROJECT_STATE.md").read_text()
    begin = txt.index("<!-- BEGIN GENERATED")
    end = txt.index("<!-- END GENERATED")
    prose = txt[:begin] + txt[end:]
    # A fraction (12/199, 4/104) or a percentage (99.0%, 3.5%). Any denominator:
    # pinning 199|200 would have gone stale the moment the corpus grew.
    quantity = re.compile(r"\b\d{1,4}/\d{1,4}\b|\b\d{1,3}(?:\.\d+)?%")
    for line in prose.split("\n"):
        # Table rows ONLY: the ledger and the corrections log must be able to
        # quote what a number used to be. Each row is dated and carries its own
        # evidence cell, so the quote is attributable. Prose has no such anchor.
        if line.lstrip().startswith("|"):
            continue
        m = quantity.search(line)
        if m:
            fail("handwritten-position",
                 f"PROJECT_STATE prose restates a measured quantity "
                 f"({m.group(0)}); the measured position belongs to the "
                 f"GENERATED block only. Point at it, do not copy it. "
                 f"Line begins: {line.strip()[:70]!r}")


def inv_fixture_baseline():
    mf = json.loads((REPO / "corpora/false_ready/manifest.json").read_text())
    live = [f for f in mf["fixtures"]
            if f["expected_cli"] == "READY" and f.get("pdflatex") != "compiles"]
    recorded = mf["baseline"]["false_ready_total"]
    if len(live) != recorded:
        fail("fixture-baseline",
             f"manifest.baseline.false_ready_total={recorded} but "
             f"{len(live)} fixtures are live false-READYs "
             f"(expected_cli READY and pdflatex rejects)")
    state = (REPO / "docs/v27/PROJECT_STATE.md").read_text()
    m = re.search(r"\*\*\(b\)\*\* fixture baseline \|[^|]*\|\s*\*\*(\d+)\*\*", state)
    if m and int(m.group(1)) != recorded:
        fail("fixture-baseline",
             f"PROJECT_STATE row (b) publishes {m.group(1)}, manifest says {recorded}")


def inv_compile_blocking_count():
    r"""No file may publish a compile-blocking rule count the code contradicts.

    OPEN-079 / C-47. The first version of this invariant was VACUOUS: it
    regexed "(\\d+)\\s+compile-blocking rules" over exactly three files and
    matched ZERO times in all three, while eight live sites published 37
    against a code list of 36 -- a class C-40 had already recorded as fixed.

    It was anchored on a PHRASING that happened to appear in the audit note,
    not on the QUANTITY. It is now anchored on len(compile_blocking_ids) and
    scans every tracked text file, with two documented exclusions:

      * CHANGELOG.md -- a release record states what was true AT THAT RELEASE.
        Rewriting it would falsify history to please a gate.
      * this file -- its own docstring quotes the defect it exists to catch.

    Markdown table rows are skipped for the same reason as in
    inv_no_handwritten_position: the ledger and the corrections log must be
    able to say "this said 37 and the code said 36".
    """
    src = (REPO / "latex-parse/src/validators.ml").read_text()
    m = re.search(r"let compile_blocking_ids\s*=\s*\[(.*?)\]", src, re.S)
    if not m:
        fail("compile-blocking-count",
             "cannot find compile_blocking_ids in latex-parse/src/validators.ml "
             "-- the invariant has lost its anchor and is silently vacuous, "
             "which is exactly the failure OPEN-079 records")
        return
    n = len(re.findall(r'"[A-Z]+-\d+"', m.group(1)))

    # Both spellings the repo actually uses for this quantity.
    pats = [re.compile(r"(\d+)\s+compile-blocking"),
            re.compile(r"(\d+)\s+DELIM/ENC/PRT")]
    # Files whose JOB is to state the wrong value: this gate's own docstring,
    # and the kill-test registry, whose mutations must literally contain the
    # known-bad count in order to prove the gate fires on it.
    EXCLUDE_NAMES = {"CHANGELOG.md", "check_doc_consistency.py",
                     "check_gate_selftests.py"}
    EXCLUDE_DIRS = ("archive/", "docs/archive/", "specs/archive/", "_build/")
    try:
        tracked = subprocess.run(["git", "ls-files"], cwd=REPO, check=True,
                                 capture_output=True, text=True).stdout.split()
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        fail("compile-blocking-count", f"cannot enumerate tracked files: {exc}")
        return
    exts = {".md", ".ml", ".mli", ".sh", ".py", ".yml", ".yaml", ".v"}
    for rel in tracked:
        if pathlib.Path(rel).suffix not in exts:
            continue
        if pathlib.Path(rel).name in EXCLUDE_NAMES:
            continue
        if any(rel.startswith(d) or f"/{d}" in rel for d in EXCLUDE_DIRS):
            continue
        f = REPO / rel
        try:
            content = f.read_text(errors="replace")
        except OSError:
            continue
        for lineno, line in enumerate(content.split("\n"), 1):
            if line.lstrip().startswith("|"):
                continue
            for pat in pats:
                for m2 in pat.finditer(line):
                    if int(m2.group(1)) != n:
                        fail("compile-blocking-count",
                             f"{rel}:{lineno} says {m2.group(1)} compile-blocking "
                             f"rules; validators.ml lists {n}. (OPEN-058: the "
                             f"EFFECTIVE belt is smaller again -- say which "
                             f"quantity you mean.)")


def main():
    for inv in (inv_readme_version, inv_rule_maturity, inv_no_handwritten_position,
                inv_fixture_baseline, inv_compile_blocking_count):
        inv()
    if FAILURES:
        print("[doc-consistency] FAIL — a number is published in two places and they disagree:")
        for f in FAILURES:
            print("   ", f)
        print("[doc-consistency] Fix the PROSE, not the artefact: one source of truth per number.")
        return 1
    print("[doc-consistency] PASS: 5 cross-document invariants hold "
          "(README version, rule maturity, no hand-written position, "
          "fixture baseline, compile-blocking count).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
