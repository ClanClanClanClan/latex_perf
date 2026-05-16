#!/usr/bin/env python3
"""Generate specs/v27/FIX_PRODUCER_LEDGER.md from rule_contracts.yaml + shipped
producer mapping in the validator source.

The ledger tracks bucket assignment (A/B/C/D) + shipping status for every
catalogued rule. It is required by the cadence plan's acceptance criteria
(V27_FIX_PRODUCER_CADENCE.md).

Usage:
    python3 scripts/tools/generate_fix_producer_ledger.py [--check]

With --check: exit 1 if the on-disk ledger differs from the generated one
(used by pre_release_check to prevent ledger drift). Otherwise: overwrite
the ledger file.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LEDGER_PATH = REPO_ROOT / "specs/v27/FIX_PRODUCER_LEDGER.md"
RULE_CONTRACTS_PATH = REPO_ROOT / "specs/rules/rule_contracts.yaml"
VALIDATORS_DIR = REPO_ROOT / "latex-parse/src"

# Hand-maintained shipped-versions mapping. Each entry: rule-id → version tag.
# Update when a new fix producer ships.
SHIPPED_VERSIONS = {
    "TYPO-002": "v26.2.1",
    "TYPO-003": "v26.2.1",
    "TYPO-006": "v26.3.1",
    "TYPO-007": "v26.3.1",
    "TYPO-008": "v26.3.1",
    "TYPO-009": "v26.3.1",
    "TYPO-013": "v26.3.1",
    "TYPO-014": "v26.3.1",
    "TYPO-015": "v26.3.1",
    "TYPO-016": "v26.3.1",
    "TYPO-018": "v26.3.0",
    "TYPO-021": "v26.3.0",
    "TYPO-022": "v26.3.0",
    "TYPO-024": "v26.3.0",
    "TYPO-025": "v26.3.1",
    "TYPO-026": "v26.3.1",
    "TYPO-027": "v26.3.0",
    "TYPO-033": "v26.3.0",
    "TYPO-035": "v26.3.0",
    "TYPO-037": "v26.3.0",
    "SPC-002": "v26.2.1",
    "SPC-003": "v26.3.1",
    "SPC-004": "v26.3.1",
    "SPC-005": "v26.3.1",
    "SPC-008": "v26.3.0",
    "SPC-009": "v26.3.0",
    "SPC-010": "v26.3.0",
    "SPC-011": "v26.3.0",
    "SPC-012": "v26.3.0",
    "STRUCT-001": "v26.3.0",
    "STRUCT-002": "v26.3.0",
    "ENC-002": "v26.3.0",
    "TYPO-010": "v27.0.5",
    "TYPO-004": "v27.0.6",
    "TYPO-005": "v27.0.7",
    "TYPO-001": "v27.0.8",
    "TYPO-038": "v27.0.9",
    "TYPO-034": "v27.0.11",
    "TYPO-029": "v27.0.12",
    "TYPO-039": "v27.0.13",
    "TYPO-032": "v27.0.14",
    "TYPO-042": "v27.0.15",
    "TYPO-051": "v27.0.16",
    "TYPO-049": "v27.0.17",
    "TYPO-017": "v27.0.18",
    "TYPO-046": "v27.0.19",
    "TYPO-028": "v27.0.20",
    "TYPO-012": "v27.0.21",
    "ENC-007": "v27.0.22",
    "ENC-017": "v27.0.23",
    "ENC-021": "v27.0.24",
    "ENC-020": "v27.0.25",
    "ENC-022": "v27.0.26",
    "ENC-024": "v27.0.27",
    "ENC-012": "v27.0.28",
    "ENC-014": "v27.0.29",
    "ENC-013": "v27.0.30",
    "ENC-018": "v27.0.31",
    "ENC-023": "v27.0.33",
    "ENC-016": "v27.0.35",
    "CHAR-006": "v27.0.37",
    "CHAR-007": "v27.0.38",
    "CHAR-008": "v27.0.39",
    "CHAR-009": "v27.0.40",
    "CHAR-005": "v27.0.41",
    "CHAR-013": "v27.0.41",
    "CHAR-014": "v27.0.41",
    "TYPO-055": "v27.0.43",
    "TYPO-053": "v27.0.44",
    "CHAR-019": "v27.0.44",
}

# Explicitly NLP-deferred rules (Bucket B, marked "deferred (NLP)" in code).
NLP_DEFERRED = {"TYPO-019", "TYPO-020", "TYPO-030", "TYPO-031"}


def discover_shipped_from_source() -> set[str]:
    """Discover rules with mk_result_with_fix in the validator source — these
    are the actually-shipped fix producers. Used to verify SHIPPED_VERSIONS
    is in sync with the code."""
    shipped: set[str] = set()
    pat = re.compile(r'id:"([A-Z]+-[0-9]+)"')
    for f in VALIDATORS_DIR.glob("*.ml"):
        text = f.read_text()
        for m in re.finditer(r"mk_result_with_fix.*?\n", text):
            # Look back a few lines for the id pattern.
            start = max(0, m.start() - 200)
            window = text[start : m.end()]
            for mm in pat.finditer(window):
                shipped.add(mm.group(1))
    return shipped


def discover_all_rules() -> list[str]:
    rules: list[str] = []
    pat = re.compile(r"^- rule_id:\s+(\S+)\s*$")
    for line in RULE_CONTRACTS_PATH.read_text().splitlines():
        m = pat.match(line)
        if m:
            rules.append(m.group(1))
    return sorted(rules)


def assign_bucket(rid: str) -> str:
    family = rid.split("-")[0]
    if rid in SHIPPED_VERSIONS:
        return "A"
    if rid in NLP_DEFERRED:
        return "B"
    if family in ("CHAR", "ENC", "SPC", "STRUCT"):
        return "A"
    if family == "TYPO":
        return "A"
    if family == "MATH":
        return "A"
    if family in ("CMD", "PKG"):
        return "A"
    if family in ("VERB", "SCRIPT", "CJK", "LANG", "RTL"):
        return "A"
    if family == "STYLE":
        return "B"
    if family in ("FIG", "FONT", "PDF", "L3"):
        return "D"
    if family in ("BIB", "REF", "LAY"):
        return "C"
    if family in ("TAB", "TIKZ", "CHEM", "COL", "DELIM"):
        return "A"
    if family in ("MOD", "DOC", "PRJ", "META"):
        return "C"
    if family == "SYS":
        return "D"
    if len(family) <= 3:
        return "A"
    return "A"


def status(rid: str) -> str:
    if rid in SHIPPED_VERSIONS:
        return f"shipped in {SHIPPED_VERSIONS[rid]}"
    if rid in NLP_DEFERRED:
        return "deferred (NLP)"
    return "pending"


def bucket_confidence(rid: str) -> str:
    if rid in SHIPPED_VERSIONS or rid in NLP_DEFERRED:
        return "confirmed"
    return "tentative"


def build_ledger(all_rules: list[str]) -> str:
    out: list[str] = []

    buckets = {"A": 0, "B": 0, "C": 0, "D": 0}
    statuses = {"shipped": 0, "pending": 0, "deferred": 0}
    per_family: dict[str, dict[str, int]] = {}

    for r in all_rules:
        b = assign_bucket(r)
        buckets[b] += 1
        fam = r.split("-")[0]
        per_family.setdefault(
            fam,
            {"count": 0, "shipped": 0, "pending": 0, "deferred": 0, "A": 0, "B": 0, "C": 0, "D": 0},
        )
        per_family[fam]["count"] += 1
        per_family[fam][b] += 1
        if r in SHIPPED_VERSIONS:
            statuses["shipped"] += 1
            per_family[fam]["shipped"] += 1
        elif r in NLP_DEFERRED:
            statuses["deferred"] += 1
            per_family[fam]["deferred"] += 1
        else:
            statuses["pending"] += 1
            per_family[fam]["pending"] += 1

    pct_shipped = 100 * statuses["shipped"] // len(all_rules)

    out.append("# V27_FIX_PRODUCER_LEDGER — Rolling fix-producer status across all 660 rules")
    out.append("")
    out.append("Tracks bucket assignment (per `V27_FIX_PRODUCER_CADENCE.md`) and shipping")
    out.append("status for every catalogued rule. Required by the cadence plan's acceptance")
    out.append("criteria.")
    out.append("")
    out.append("**Auto-generated** by `scripts/tools/generate_fix_producer_ledger.py`.")
    out.append("To update: edit `SHIPPED_VERSIONS` in the generator script and rerun.")
    out.append("The pre-release gate `check_fix_producer_ledger.py` runs the generator with")
    out.append("`--check` and fails if the on-disk file drifts from the generated one.")
    out.append("")
    out.append("## Summary")
    out.append("")
    out.append(f"- **Total rules**: {len(all_rules)}")
    out.append(f"- **Shipped**: {statuses['shipped']} (~{pct_shipped}%)")
    out.append(f"- **Pending**: {statuses['pending']}")
    out.append(f"- **Deferred**: {statuses['deferred']} (NLP-required)")
    out.append("")
    out.append("### Bucket distribution (tentative — heuristic-assigned for unshipped)")
    out.append("")
    out.append("| Bucket | Description | Count | Shipped | Remaining |")
    out.append("|--------|-------------|-------|---------|-----------|")
    out.append(
        f"| **A**  | Mechanical, safe everywhere       | {buckets['A']} | {statuses['shipped']} | {buckets['A']-statuses['shipped']} |"
    )
    out.append(f"| **B**  | Sentence-aware (NLP-required)     | {buckets['B']} | 0 | {buckets['B']} |")
    out.append(
        f"| **C**  | Context-required (--apply-fixes-with-prompt) | {buckets['C']} | 0 | {buckets['C']} |"
    )
    out.append(
        f"| **D**  | Defer indefinitely (compile/runtime) | {buckets['D']} | 0 | {buckets['D']} |"
    )
    out.append("")
    out.append("**Caveat:** Bucket assignments for unshipped rules are TENTATIVE — heuristic-")
    out.append("assigned by family (see classification rules below). Each rule's bucket should")
    out.append("be confirmed during the shipping audit before producer implementation.")
    out.append("")
    out.append("## Bucket classification heuristic")
    out.append("")
    out.append("Heuristic used to assign initial buckets for unshipped rules:")
    out.append("")
    out.append("- **A (mechanical)**: TYPO, ENC, CHAR, SPC, STRUCT, MATH, CMD, PKG, VERB,")
    out.append("  SCRIPT, CJK, LANG, RTL, TAB, TIKZ, CHEM, COL, DELIM, and language-code")
    out.append("  families (DE, FR, ES, …) — pattern-based, no semantic context needed.")
    out.append("- **B (NLP)**: STYLE — sentence-aware / passive-voice / stylistic detection.")
    out.append("  Also TYPO-019/020/030/031 which are explicitly NLP-deferred in the code.")
    out.append("- **C (context-required)**: BIB, REF, LAY, MOD, DOC, PRJ, META — fixes")
    out.append("  depend on bibliography style, label context, layout state, or project")
    out.append("  configuration.")
    out.append("- **D (defer)**: FIG, FONT, PDF, L3, SYS — file-format / compile-state /")
    out.append("  runtime-dependent diagnostics that cannot be fixed via static byte edits.")
    out.append("")
    out.append("Per the cadence plan, Bucket D rules carry `produces_fix: false` in")
    out.append(f"`rule_contracts.yaml` with documented reason.  All {buckets['D']} D-bucket")
    out.append("rules + the 4 NLP-deferred rules + CHAR-010/011 (redundant with ENC-020)")
    out.append("+ CHAR-022 (pending refinement) carry the annotation as of v27.0.42.")
    out.append("")
    out.append("## Per-family breakdown")
    out.append("")
    out.append("| Family | Total | Shipped | Pending | Deferred | A | B | C | D |")
    out.append("|--------|-------|---------|---------|----------|---|---|---|---|")
    for fam in sorted(per_family.keys()):
        s = per_family[fam]
        out.append(
            f"| {fam} | {s['count']} | {s['shipped']} | {s['pending']} | {s['deferred']} | {s['A']} | {s['B']} | {s['C']} | {s['D']} |"
        )
    out.append("")
    out.append("## Per-rule ledger")
    out.append("")
    out.append("| Rule | Family | Bucket | Confidence | Status |")
    out.append("|------|--------|--------|------------|--------|")

    by_family: dict[str, list[str]] = {}
    for r in all_rules:
        by_family.setdefault(r.split("-")[0], []).append(r)
    for fam in sorted(by_family.keys()):
        rules_in_fam = sorted(
            by_family[fam],
            key=lambda x: int(x.split("-")[1]) if x.split("-")[1].isdigit() else 0,
        )
        for r in rules_in_fam:
            b = assign_bucket(r)
            c = bucket_confidence(r)
            st = status(r)
            out.append(f"| `{r}` | {fam} | **{b}** | {c} | {st} |")

    out.append("")
    out.append("## Acceptance-criteria status")
    out.append("")
    out.append("Per `V27_FIX_PRODUCER_CADENCE.md` § Acceptance criteria:")
    out.append("")
    out.append("- [x] `specs/v27/FIX_PRODUCER_LEDGER.md` exists with full bucket")
    out.append(f"  assignments for all {len(all_rules)} rules. **DONE** (this file).")
    out.append("- [ ] At each patch release, ≥10 new producers shipped from Bucket A.")
    out.append("  **PENDING** — actual cadence has been ~1 producer per patch since")
    out.append("  v27.0.5 (user-driven cadence prioritizing audit depth over throughput).")
    out.append("- [x] Bucket D rules carry `produces_fix: false` in `rule_contracts.yaml`")
    out.append("  with documented reason.  **DONE** (v27.0.42 — all 62 Bucket D rules +")
    out.append("  4 NLP-deferred + 2 redundant + 1 deferred-refinement = 69 explicit")
    out.append("  `produces_fix: false` entries, plus 67 `produces_fix: true` for shipped")
    out.append("  producers).  Source: `pick_produces_fix` in")
    out.append("  `scripts/tools/generate_rule_contracts.py`.")
    out.append("- [ ] Differential test passes 0 diffs vs prior tag (default invocation;")
    out.append("  fix producers gated behind `--apply-fixes`).")
    out.append("  **ACHIEVED** every cycle since v27.0.5.")
    out.append("- [ ] Bucket A shipped fully by v27.2.0 (target).")
    out.append(f"  **TRACKING** — {statuses['shipped']} of {buckets['A']} Bucket A")
    out.append("  rules shipped. At current 1/cycle pace, full Bucket A completion")
    out.append("  would arrive much later than v27.2.0; cadence target needs review.")
    out.append("- [ ] Bucket B + C shipped fully by v27.4.0 (target).")
    out.append("  **TRACKING** — 0 of 53 Bucket B + 0 of 87 Bucket C shipped.")
    out.append("")
    out.append("## Next-pick guidance")
    out.append("")
    out.append("For the next mechanical fix-producer cycle, prefer:")
    out.append("")
    out.append("1. **ENC family**: 24 total, 13 shipped, 11 pending. Remaining mostly")
    out.append("   require non-trivial decisions (homoglyph direction, multi-char")
    out.append("   mappings, complex semantics).")
    out.append("2. **MATH family**: 108 total, 0 shipped. Largest untapped Bucket A pool.")
    out.append("   Most rules are simple environment-name / command-syntax checks.")
    out.append("3. **TYPO family**: 63 total, 36 shipped, 23 pending (4 NLP-deferred).")
    out.append("   Remaining 23 include ambiguous-fix cases (TYPO-040 math-too-long,")
    out.append("   TYPO-041 ldots-spacing, TYPO-047 starred section, TYPO-048 en-dash-")
    out.append("   as-minus).")
    out.append("4. **CHAR family**: 22 total, 0 shipped. Each rule targets a specific")
    out.append("   problematic character — all mechanical deletion or substitution.")
    return "\n".join(out) + "\n"


def main() -> int:
    all_rules = discover_all_rules()
    if not all_rules:
        print(
            f"[ledger] ERROR: no rule IDs found in {RULE_CONTRACTS_PATH}", file=sys.stderr
        )
        return 1

    # Cross-check: SHIPPED_VERSIONS must agree with code.
    code_shipped = discover_shipped_from_source()
    missing_from_versions = code_shipped - SHIPPED_VERSIONS.keys()
    spurious_in_versions = SHIPPED_VERSIONS.keys() - code_shipped
    if missing_from_versions or spurious_in_versions:
        print(
            "[ledger] ERROR: SHIPPED_VERSIONS drifts from code:", file=sys.stderr
        )
        if missing_from_versions:
            print(
                f"  In code but missing from SHIPPED_VERSIONS: {sorted(missing_from_versions)}",
                file=sys.stderr,
            )
        if spurious_in_versions:
            print(
                f"  In SHIPPED_VERSIONS but not in code: {sorted(spurious_in_versions)}",
                file=sys.stderr,
            )
        print(
            "  Update SHIPPED_VERSIONS in scripts/tools/generate_fix_producer_ledger.py",
            file=sys.stderr,
        )
        return 1

    content = build_ledger(all_rules)
    if "--check" in sys.argv:
        on_disk = LEDGER_PATH.read_text() if LEDGER_PATH.exists() else ""
        if on_disk != content:
            print(
                f"[ledger] FAIL: {LEDGER_PATH.relative_to(REPO_ROOT)} differs from generated.",
                file=sys.stderr,
            )
            print(
                "  Run scripts/tools/generate_fix_producer_ledger.py to regenerate.",
                file=sys.stderr,
            )
            return 1
        print(f"[ledger] ok: {LEDGER_PATH.relative_to(REPO_ROOT)} in sync.")
        return 0

    LEDGER_PATH.write_text(content)
    print(
        f"[ledger] wrote {len(all_rules)} rules to {LEDGER_PATH.relative_to(REPO_ROOT)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
