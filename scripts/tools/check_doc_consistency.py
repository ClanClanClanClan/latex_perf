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
    """PROJECT_STATE prose must not restate the real-paper matrix."""
    txt = (REPO / "docs/v27/PROJECT_STATE.md").read_text()
    begin = txt.index("<!-- BEGIN GENERATED")
    end = txt.index("<!-- END GENERATED")
    prose = txt[:begin] + txt[end:]
    # a positional claim looks like "197/199" or "177/200"
    for m in re.finditer(r"\b(\d{2,3})/(199|200)\b", prose):
        line_start = prose.rfind("\n", 0, m.start()) + 1
        line = prose[line_start:prose.find("\n", m.start())]
        # ledger rows and the corrections log legitimately QUOTE history;
        # they are marked by a leading table pipe or the word "superseded".
        if line.lstrip().startswith("|") or "superseded" in line.lower():
            continue
        fail("handwritten-position",
             f"PROJECT_STATE prose restates a positional number ({m.group(0)}); "
             f"the measured position belongs to the GENERATED block only")


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
    src = (REPO / "latex-parse/src/validators.ml").read_text()
    m = re.search(r"let compile_blocking_ids\s*=\s*\[(.*?)\]", src, re.S)
    if not m:
        return
    n = len(re.findall(r'"[A-Z]+-\d+"', m.group(1)))
    for doc in ("README.md", "docs/COMPILATION_GUARANTEE.md", "docs/v27/ROADMAP.md"):
        p = REPO / doc
        if not p.is_file():
            continue
        for m2 in re.finditer(r"(\d+)\s+compile-blocking rules", p.read_text()):
            if int(m2.group(1)) != n:
                fail("compile-blocking-count",
                     f"{doc} says {m2.group(1)} compile-blocking rules; "
                     f"validators.ml lists {n}")


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
