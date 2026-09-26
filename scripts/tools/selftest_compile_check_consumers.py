#!/usr/bin/env python3
"""Pin every machine consumer of `--compile-check` output to the M0 surface.

ADR-012 (M0) added a `TIER` line and up to three `why not strict:` lines AFTER
the frozen lines of `--compile-check`. A consumer that parses a rewritten string
can go blind without failing (C-65), so this script feeds each consumer's
actual parsing function a verbatim pre-M0 output and a verbatim M0 output of
the same document and asserts they read the same thing. It is pure: no CLI, no
pdflatex, so it runs in spec-drift.

Consumers covered (every one found by grepping the repository on 2026-09-26):

  diff_real_roots.scrape_reasons     reason tokens over stdout (the one that
                                     needed a change: it now stops at TIER)
  gen_proven_coverage.parse_verdict  the MODEL-CONNECTED state and tier fields
  gen_proven_coverage.parse_tier     the new TIER tokens
  regrade_sample.py                  lines starting T0..T5 or MODEL-NOT
  bench_compile_check.sh             lines matching '^  T[0-5]'
  check_known_false_ready, diff_compile_check.sh, false_ready_oracle.sh,
  check_apply_fixes_roundtrip, bench_wedge.sh, diff_real_roots (cell)
                                     the exit code only; M0 moves none, which
                                     latex-parse/src/test_verdict.ml asserts
                                     on the strict battery.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from diff_real_roots import scrape_reasons  # noqa: E402
from gen_proven_coverage import parse_tier, parse_verdict  # noqa: E402

MODEL_OK = ("MODEL-CONNECTED\tPREMISE-CERTIFIED\ttier=lp-core\tbuild-graph closure "
            "and engine-feature admissibility verified over the abstract model; NOT "
            "a compilation guarantee (docs/COMPILATION_GUARANTEE.md)\n")
M0_TAIL_OK = (
    "TIER\theuristic\tLIKELY-OK\tLIKELY OK (heuristic; premise-certified) — not a proof\n"
    # A why-not-strict line quoting author source that LOOKS like reason tokens:
    # a macro named \T1 and a file named sec-001.tex. The old whole-buffer
    # scrape would have recorded T1 and SEC-001 as blocking reasons.
    "  why not strict: \\def at SEC-001.tex:3 — rewrite \\def\\T1{x} as \\newcommand{\\T1}{x}\n"
    "  why not strict: strict tier not yet available (M0) — no document is decided by proof yet\n")
NR_BODY = ("NOT-READY\t/p/main.tex\n"
           "  T5 rule violations: [DELIM-003; DELIM-004]\n")
M0_TAIL_NR = ("TIER\theuristic\tLIKELY-FAIL\tLIKELY FAIL (heuristic) — not a proof; "
              "1 blocking reason listed above\n"
              "  why not strict: \\makeatletter at T2.tex:1 — @-internal code belongs in a local .sty file\n")

CASES = {
    "ready": (MODEL_OK + "READY\t/p/main.tex\n",
              MODEL_OK + "READY\t/p/main.tex\n" + M0_TAIL_OK),
    "not-ready": (MODEL_OK + NR_BODY, MODEL_OK + NR_BODY + M0_TAIL_NR),
}

fails = 0


def check(cond: bool, msg: str) -> None:
    global fails
    if not cond:
        fails += 1
        print(f"[compile-check-consumers] FAIL: {msg}")


def regrade_reasons(out: str) -> list[str]:
    # Verbatim filter of scripts/tools/regrade_sample.py.
    return [l.strip() for l in out.splitlines()
            if l.strip().startswith(("T0", "T2", "T3", "T4", "T5", "MODEL-NOT"))]


def bench_reasons(out: str) -> list[str]:
    # Verbatim filter of latex-parse/scripts/bench_compile_check.sh.
    return [l for l in out.splitlines() if re.match(r"^  T[0-5]", l)]


for name, (old, new) in CASES.items():
    old_scrape = sorted(set(re.findall(r"\b(T\d|[A-Z]{2,8}-\d{3})\b", old)))
    check(scrape_reasons(old) == old_scrape,
          f"{name}: scrape_reasons on pre-M0 output differs from the old "
          f"whole-buffer scrape")
    check(scrape_reasons(new) == old_scrape,
          f"{name}: scrape_reasons reads the M0 tier block: {scrape_reasons(new)} "
          f"!= {old_scrape}")
    check(parse_verdict(old) == parse_verdict(new) != (None, None),
          f"{name}: parse_verdict changed")
    check(parse_tier(old) == (None, None), f"{name}: pre-M0 output has no tier")
    check(parse_tier(new)[0] == "heuristic", f"{name}: parse_tier on M0 output")
    check(regrade_reasons(old) == regrade_reasons(new),
          f"{name}: regrade_sample filter changed")
    check(bench_reasons(old) == bench_reasons(new),
          f"{name}: bench_compile_check filter changed")

# The negative direction: a tier line that claims PROVEN outside the proven
# tier must be refused, not recorded.
try:
    parse_tier("TIER\theuristic\tPROVEN-READY\tx\n")
    check(False, "parse_tier accepted a PROVEN kind in the heuristic tier")
except SystemExit:
    pass
try:
    parse_tier("TIER\tproven\tLIKELY-OK\tx\n")
    check(False, "parse_tier accepted a heuristic kind in the proven tier")
except SystemExit:
    pass

if fails:
    print(f"[compile-check-consumers] {fails} failure(s)")
    sys.exit(1)
print(f"[compile-check-consumers] PASS: {len(CASES)} documents x 7 consumer "
      f"reads + 2 refusals")
