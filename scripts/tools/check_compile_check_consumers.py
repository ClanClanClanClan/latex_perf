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
  regrade_sample.reason_lines        lines starting T0..T5 or MODEL-NOT
                                     (IMPORTED, not copied)
  bench_compile_check.sh             lines matching '^  T[0-5]' (shell, so the
                                     pattern is READ from the script's own
                                     text and both of its grep sites must use
                                     it; a hand copy is not trusted)
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
from regrade_sample import reason_lines as regrade_reasons  # noqa: E402

REPO = Path(__file__).resolve().parent.parent.parent
BENCH = REPO / "latex-parse/scripts/bench_compile_check.sh"

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

# LP-Foreign, verbatim from the origin/main CLI (old) and the M0 CLI (new) on
# a root containing \catcode`\@=11. The reason line was REWORDED (it was
# mislabelled a parse failure) and must keep its leading T0 token.
MODEL_FOREIGN = MODEL_OK.replace("tier=lp-core", "tier=lp-foreign")
FOREIGN_OLD_BODY = (
    "NOT-READY\tmain.tex\n"
    "  T0 parse fails in main.tex: LP-Foreign construct(s): \\catcode direct "
    "mutation detected; LP-Foreign (line 3)\n")
FOREIGN_NEW_BODY = (
    "NOT-READY\tmain.tex\n"
    "  T0 LP-Foreign construct(s) in main.tex (outside every supported tier; not "
    "a parse failure): \\catcode direct mutation detected; LP-Foreign (line 3)\n")
M0_TAIL_FOREIGN = (
    "TIER\tforeign\tFOREIGN\tFOREIGN — \"\\catcode\" at \"main.tex:3\" is outside "
    "every supported tier (neither the exact tier nor the heuristic tier "
    "applies); not a proof\n"
    "  why not strict: \"\\catcode\" at \"main.tex:3\" — outside every supported "
    "tier by design: shell escape, catcode changes and scripting cannot be "
    "decided without running TeX\n")
# LP-Foreign only in an \input child: the legacy answer is READY (exit 0) and
# only the TIER line says FOREIGN.
M0_TAIL_FOREIGN_CHILD = (
    "TIER\tforeign\tFOREIGN\tFOREIGN — \"\\catcode\" at \"sec.tex:1\" is outside "
    "every supported tier (neither the exact tier nor the heuristic tier "
    "applies); not a proof; the exit code 0 is the legacy heuristic READY, "
    "unchanged in M0, and does not place this document in any tier\n"
    "  why not strict: \"\\catcode\" at \"sec.tex:1\" — outside every supported "
    "tier by design: shell escape, catcode changes and scripting cannot be "
    "decided without running TeX\n")

CASES = {
    "ready": (MODEL_OK + "READY\t/p/main.tex\n",
              MODEL_OK + "READY\t/p/main.tex\n" + M0_TAIL_OK),
    "not-ready": (MODEL_OK + NR_BODY, MODEL_OK + NR_BODY + M0_TAIL_NR),
    "foreign": (MODEL_FOREIGN + FOREIGN_OLD_BODY,
                MODEL_FOREIGN + FOREIGN_NEW_BODY + M0_TAIL_FOREIGN),
    "foreign-child": (MODEL_OK + "READY\t/p/main.tex\n",
                      MODEL_OK + "READY\t/p/main.tex\n" + M0_TAIL_FOREIGN_CHILD),
}
# The cases whose reason WORDING changed on purpose: there, the consumers must
# agree on the leading tokens, not on the text.
REWORDED = {"foreign"}

fails = 0


def check(cond: bool, msg: str) -> None:
    global fails
    if not cond:
        fails += 1
        print(f"[compile-check-consumers] FAIL: {msg}")


# bench_compile_check.sh is shell and cannot be imported, so its pattern is READ
# from its own text: every `grep -E '<pat>'` on --compile-check output must use
# one and the same pattern, and that pattern is what is exercised below.
_bench_pats = re.findall(r"--compile-check(?:-full)?\s+\"\$f\"[^|]*\|\s*grep -E '([^']+)'",
                         BENCH.read_text())
check(len(_bench_pats) >= 2 and len(set(_bench_pats)) == 1,
      f"bench_compile_check.sh: expected its --compile-check greps to share one "
      f"pattern, found {_bench_pats!r}")
BENCH_PAT = _bench_pats[0] if _bench_pats else r"^  T[0-5]"


def bench_reasons(out: str) -> list[str]:
    # grep -E semantics over each line, with the pattern taken from the script.
    return [l for l in out.splitlines() if re.search(BENCH_PAT, l)]


def lead(lines: list[str]) -> list[str]:
    return [l.split()[0] for l in lines]


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
    want_tier = "foreign" if name.startswith("foreign") else "heuristic"
    check(parse_tier(new)[0] == want_tier,
          f"{name}: parse_tier on M0 output is {parse_tier(new)[0]!r}, "
          f"expected {want_tier!r}")
    if name in REWORDED:
        # The leading T0 token is the contract both filters rely on.
        for fname, f in (("regrade_sample", regrade_reasons),
                         ("bench_compile_check", bench_reasons)):
            check(lead(f(old)) == lead(f(new)) and "T0" in lead(f(new)),
                  f"{name}: {fname} lost the leading T0 token: "
                  f"{lead(f(old))} -> {lead(f(new))}")
    else:
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
      f"reads + 2 refusals + the bench pattern read from its script")
