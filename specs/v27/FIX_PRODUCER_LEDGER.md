# V27_FIX_PRODUCER_LEDGER — Rolling fix-producer status across all 660 rules

Tracks bucket assignment (per `V27_FIX_PRODUCER_CADENCE.md`) and shipping
status for every catalogued rule. Required by the cadence plan's acceptance
criteria.

**Auto-generated** by `scripts/tools/generate_fix_producer_ledger.py`.
To update: edit `SHIPPED_VERSIONS` in the generator script and rerun.
The pre-release gate `check_fix_producer_ledger.py` runs the generator with
`--check` and fails if the on-disk file drifts from the generated one.

## Summary

- **Total rules**: 660
- **Shipped**: 166 (~25%)
- **Pending**: 490
- **Deferred**: 4 (NLP-required)

### Bucket distribution (tentative — heuristic-assigned for unshipped)

| Bucket | Description | Count | Shipped | Remaining |
|--------|-------------|-------|---------|-----------|
| **A**  | Mechanical, safe everywhere       | 465 | 166 | 299 |
| **B**  | Sentence-aware (NLP-required)     | 49 | 0 | 49 |
| **C**  | Context-required (--apply-fixes-with-prompt) | 84 | 0 | 84 |
| **D**  | Defer indefinitely (compile/runtime) | 62 | 0 | 62 |

**Caveat:** Bucket assignments for unshipped rules are TENTATIVE — heuristic-
assigned by family (see classification rules below). Each rule's bucket should
be confirmed during the shipping audit before producer implementation.

## Bucket classification heuristic

Heuristic used to assign initial buckets for unshipped rules:

- **A (mechanical)**: TYPO, ENC, CHAR, SPC, STRUCT, MATH, CMD, PKG, VERB,
  SCRIPT, CJK, LANG, RTL, TAB, TIKZ, CHEM, COL, DELIM, and language-code
  families (DE, FR, ES, …) — pattern-based, no semantic context needed.
- **B (NLP)**: STYLE — sentence-aware / passive-voice / stylistic detection.
  Also TYPO-019/020/030/031 which are explicitly NLP-deferred in the code.
- **C (context-required)**: BIB, REF, LAY, MOD, DOC, PRJ, META — fixes
  depend on bibliography style, label context, layout state, or project
  configuration.
- **D (defer)**: FIG, FONT, PDF, L3, SYS — file-format / compile-state /
  runtime-dependent diagnostics that cannot be fixed via static byte edits.

Per the cadence plan, Bucket D rules carry `produces_fix: false` in
`rule_contracts.yaml` with documented reason.  All 62 D-bucket
rules + the 4 NLP-deferred rules + CHAR-010/011 (redundant with ENC-020)
+ CHAR-022 (pending refinement) carry the annotation as of v27.0.42.

## Per-family breakdown

| Family | Total | Shipped | Pending | Deferred | A | B | C | D |
|--------|-------|---------|---------|----------|---|---|---|---|
| AR | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| BIB | 17 | 2 | 15 | 0 | 2 | 0 | 15 | 0 |
| CE | 2 | 0 | 2 | 0 | 2 | 0 | 0 | 0 |
| CHAR | 22 | 12 | 10 | 0 | 22 | 0 | 0 | 0 |
| CHEM | 10 | 3 | 7 | 0 | 10 | 0 | 0 | 0 |
| CJK | 16 | 9 | 7 | 0 | 16 | 0 | 0 | 0 |
| CMD | 17 | 0 | 17 | 0 | 17 | 0 | 0 | 0 |
| COL | 7 | 0 | 7 | 0 | 7 | 0 | 0 | 0 |
| CS | 2 | 1 | 1 | 0 | 2 | 0 | 0 | 0 |
| CY | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| DE | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| DELIM | 11 | 0 | 11 | 0 | 11 | 0 | 0 | 0 |
| DOC | 5 | 0 | 5 | 0 | 0 | 0 | 5 | 0 |
| EL | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| ENC | 24 | 16 | 8 | 0 | 24 | 0 | 0 | 0 |
| EXP | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| FIG | 25 | 0 | 25 | 0 | 0 | 0 | 0 | 25 |
| FONT | 13 | 0 | 13 | 0 | 0 | 0 | 0 | 13 |
| FR | 2 | 1 | 1 | 0 | 2 | 0 | 0 | 0 |
| HE | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| HI | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| IB | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| JA | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| KO | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| L3 | 11 | 0 | 11 | 0 | 0 | 0 | 0 | 11 |
| LANG | 16 | 0 | 16 | 0 | 16 | 0 | 0 | 0 |
| LAY | 27 | 0 | 27 | 0 | 0 | 0 | 27 | 0 |
| MATH | 108 | 19 | 89 | 0 | 108 | 0 | 0 | 0 |
| META | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 |
| MOD | 18 | 0 | 18 | 0 | 0 | 0 | 18 | 0 |
| NL | 2 | 0 | 2 | 0 | 2 | 0 | 0 | 0 |
| PDF | 12 | 0 | 12 | 0 | 0 | 0 | 0 | 12 |
| PKG | 25 | 5 | 20 | 0 | 25 | 0 | 0 | 0 |
| PL | 2 | 1 | 1 | 0 | 2 | 0 | 0 | 0 |
| PRJ | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 |
| PRT | 2 | 0 | 2 | 0 | 2 | 0 | 0 | 0 |
| PT | 3 | 0 | 3 | 0 | 3 | 0 | 0 | 0 |
| REF | 12 | 1 | 11 | 0 | 1 | 0 | 11 | 0 |
| RO | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| RTL | 5 | 0 | 5 | 0 | 5 | 0 | 0 | 0 |
| RU | 2 | 1 | 1 | 0 | 2 | 0 | 0 | 0 |
| SCRIPT | 22 | 8 | 14 | 0 | 22 | 0 | 0 | 0 |
| SPC | 35 | 24 | 11 | 0 | 35 | 0 | 0 | 0 |
| STRUCT | 5 | 3 | 2 | 0 | 5 | 0 | 0 | 0 |
| STYLE | 49 | 4 | 45 | 0 | 4 | 45 | 0 | 0 |
| SYS | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 |
| TAB | 16 | 0 | 16 | 0 | 16 | 0 | 0 | 0 |
| TH | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| TIKZ | 10 | 1 | 9 | 0 | 10 | 0 | 0 | 0 |
| TR | 1 | 0 | 1 | 0 | 1 | 0 | 0 | 0 |
| TYPO | 63 | 46 | 13 | 4 | 59 | 4 | 0 | 0 |
| VERB | 17 | 1 | 16 | 0 | 17 | 0 | 0 | 0 |
| ZH | 2 | 0 | 2 | 0 | 2 | 0 | 0 | 0 |

## Per-rule ledger

| Rule | Family | Bucket | Confidence | Status |
|------|--------|--------|------------|--------|
| `AR-002` | AR | **A** | confirmed | shipped in v27.1.11 |
| `BIB-001` | BIB | **C** | tentative | pending |
| `BIB-002` | BIB | **A** | confirmed | shipped in v27.1.13 |
| `BIB-003` | BIB | **C** | tentative | pending |
| `BIB-004` | BIB | **C** | tentative | pending |
| `BIB-005` | BIB | **C** | tentative | pending |
| `BIB-006` | BIB | **C** | tentative | pending |
| `BIB-007` | BIB | **C** | tentative | pending |
| `BIB-008` | BIB | **A** | confirmed | shipped in v27.1.13 |
| `BIB-009` | BIB | **C** | tentative | pending |
| `BIB-010` | BIB | **C** | tentative | pending |
| `BIB-011` | BIB | **C** | tentative | pending |
| `BIB-012` | BIB | **C** | tentative | pending |
| `BIB-013` | BIB | **C** | tentative | pending |
| `BIB-014` | BIB | **C** | tentative | pending |
| `BIB-015` | BIB | **C** | tentative | pending |
| `BIB-016` | BIB | **C** | tentative | pending |
| `BIB-017` | BIB | **C** | tentative | pending |
| `CE-001` | CE | **A** | tentative | pending |
| `CE-002` | CE | **A** | tentative | pending |
| `CHAR-001` | CHAR | **A** | tentative | pending |
| `CHAR-002` | CHAR | **A** | tentative | pending |
| `CHAR-003` | CHAR | **A** | tentative | pending |
| `CHAR-004` | CHAR | **A** | tentative | pending |
| `CHAR-005` | CHAR | **A** | confirmed | shipped in v27.0.41 |
| `CHAR-006` | CHAR | **A** | confirmed | shipped in v27.0.37 |
| `CHAR-007` | CHAR | **A** | confirmed | shipped in v27.0.38 |
| `CHAR-008` | CHAR | **A** | confirmed | shipped in v27.0.39 |
| `CHAR-009` | CHAR | **A** | confirmed | shipped in v27.0.40 |
| `CHAR-010` | CHAR | **A** | tentative | pending |
| `CHAR-011` | CHAR | **A** | tentative | pending |
| `CHAR-012` | CHAR | **A** | confirmed | shipped in v27.0.57 |
| `CHAR-013` | CHAR | **A** | confirmed | shipped in v27.0.41 |
| `CHAR-014` | CHAR | **A** | confirmed | shipped in v27.0.41 |
| `CHAR-015` | CHAR | **A** | tentative | pending |
| `CHAR-016` | CHAR | **A** | confirmed | shipped in v27.0.63 |
| `CHAR-017` | CHAR | **A** | confirmed | shipped in v27.0.54 |
| `CHAR-018` | CHAR | **A** | confirmed | shipped in v27.0.53 |
| `CHAR-019` | CHAR | **A** | confirmed | shipped in v27.0.44 |
| `CHAR-020` | CHAR | **A** | tentative | pending |
| `CHAR-021` | CHAR | **A** | tentative | pending |
| `CHAR-022` | CHAR | **A** | tentative | pending |
| `CHEM-001` | CHEM | **A** | tentative | pending |
| `CHEM-002` | CHEM | **A** | tentative | pending |
| `CHEM-003` | CHEM | **A** | tentative | pending |
| `CHEM-004` | CHEM | **A** | confirmed | shipped in v27.1.21 |
| `CHEM-005` | CHEM | **A** | confirmed | shipped in v27.1.10 |
| `CHEM-006` | CHEM | **A** | tentative | pending |
| `CHEM-007` | CHEM | **A** | tentative | pending |
| `CHEM-008` | CHEM | **A** | tentative | pending |
| `CHEM-009` | CHEM | **A** | confirmed | shipped in v27.1.10 |
| `CHEM-010` | CHEM | **A** | tentative | pending |
| `CJK-001` | CJK | **A** | confirmed | shipped in v27.0.61 |
| `CJK-002` | CJK | **A** | confirmed | shipped in v27.0.61 |
| `CJK-003` | CJK | **A** | tentative | pending |
| `CJK-004` | CJK | **A** | confirmed | shipped in v27.1.12 |
| `CJK-005` | CJK | **A** | tentative | pending |
| `CJK-006` | CJK | **A** | confirmed | shipped in v27.1.12 |
| `CJK-007` | CJK | **A** | tentative | pending |
| `CJK-008` | CJK | **A** | confirmed | shipped in v27.0.64 |
| `CJK-009` | CJK | **A** | confirmed | shipped in v27.1.21 |
| `CJK-010` | CJK | **A** | confirmed | shipped in v27.0.62 |
| `CJK-011` | CJK | **A** | tentative | pending |
| `CJK-012` | CJK | **A** | tentative | pending |
| `CJK-013` | CJK | **A** | tentative | pending |
| `CJK-014` | CJK | **A** | confirmed | shipped in v27.0.62 |
| `CJK-015` | CJK | **A** | confirmed | shipped in v27.0.65 |
| `CJK-016` | CJK | **A** | tentative | pending |
| `CMD-001` | CMD | **A** | tentative | pending |
| `CMD-002` | CMD | **A** | tentative | pending |
| `CMD-003` | CMD | **A** | tentative | pending |
| `CMD-004` | CMD | **A** | tentative | pending |
| `CMD-005` | CMD | **A** | tentative | pending |
| `CMD-006` | CMD | **A** | tentative | pending |
| `CMD-007` | CMD | **A** | tentative | pending |
| `CMD-008` | CMD | **A** | tentative | pending |
| `CMD-009` | CMD | **A** | tentative | pending |
| `CMD-010` | CMD | **A** | tentative | pending |
| `CMD-011` | CMD | **A** | tentative | pending |
| `CMD-012` | CMD | **A** | tentative | pending |
| `CMD-013` | CMD | **A** | tentative | pending |
| `CMD-014` | CMD | **A** | tentative | pending |
| `CMD-015` | CMD | **A** | tentative | pending |
| `CMD-016` | CMD | **A** | tentative | pending |
| `CMD-017` | CMD | **A** | tentative | pending |
| `COL-001` | COL | **A** | tentative | pending |
| `COL-002` | COL | **A** | tentative | pending |
| `COL-003` | COL | **A** | tentative | pending |
| `COL-004` | COL | **A** | tentative | pending |
| `COL-005` | COL | **A** | tentative | pending |
| `COL-006` | COL | **A** | tentative | pending |
| `COL-007` | COL | **A** | tentative | pending |
| `CS-001` | CS | **A** | confirmed | shipped in v27.1.10 |
| `CS-002` | CS | **A** | tentative | pending |
| `CY-001` | CY | **A** | confirmed | shipped in v27.1.11 |
| `DE-006` | DE | **A** | tentative | pending |
| `DELIM-001` | DELIM | **A** | tentative | pending |
| `DELIM-002` | DELIM | **A** | tentative | pending |
| `DELIM-003` | DELIM | **A** | tentative | pending |
| `DELIM-004` | DELIM | **A** | tentative | pending |
| `DELIM-005` | DELIM | **A** | tentative | pending |
| `DELIM-006` | DELIM | **A** | tentative | pending |
| `DELIM-007` | DELIM | **A** | tentative | pending |
| `DELIM-008` | DELIM | **A** | tentative | pending |
| `DELIM-009` | DELIM | **A** | tentative | pending |
| `DELIM-010` | DELIM | **A** | tentative | pending |
| `DELIM-011` | DELIM | **A** | tentative | pending |
| `DOC-001` | DOC | **C** | tentative | pending |
| `DOC-002` | DOC | **C** | tentative | pending |
| `DOC-003` | DOC | **C** | tentative | pending |
| `DOC-004` | DOC | **C** | tentative | pending |
| `DOC-005` | DOC | **C** | tentative | pending |
| `EL-001` | EL | **A** | confirmed | shipped in v27.1.10 |
| `ENC-001` | ENC | **A** | tentative | pending |
| `ENC-002` | ENC | **A** | confirmed | shipped in v26.3.0 |
| `ENC-003` | ENC | **A** | tentative | pending |
| `ENC-004` | ENC | **A** | confirmed | shipped in v27.0.71 |
| `ENC-005` | ENC | **A** | tentative | pending |
| `ENC-006` | ENC | **A** | tentative | pending |
| `ENC-007` | ENC | **A** | confirmed | shipped in v27.0.22 |
| `ENC-008` | ENC | **A** | tentative | pending |
| `ENC-009` | ENC | **A** | tentative | pending |
| `ENC-010` | ENC | **A** | tentative | pending |
| `ENC-011` | ENC | **A** | tentative | pending |
| `ENC-012` | ENC | **A** | confirmed | shipped in v27.0.28 |
| `ENC-013` | ENC | **A** | confirmed | shipped in v27.0.30 |
| `ENC-014` | ENC | **A** | confirmed | shipped in v27.0.29 |
| `ENC-015` | ENC | **A** | confirmed | shipped in v27.1.9 |
| `ENC-016` | ENC | **A** | confirmed | shipped in v27.0.35 |
| `ENC-017` | ENC | **A** | confirmed | shipped in v27.0.23 |
| `ENC-018` | ENC | **A** | confirmed | shipped in v27.0.31 |
| `ENC-019` | ENC | **A** | confirmed | shipped in v27.1.13 |
| `ENC-020` | ENC | **A** | confirmed | shipped in v27.0.25 |
| `ENC-021` | ENC | **A** | confirmed | shipped in v27.0.24 |
| `ENC-022` | ENC | **A** | confirmed | shipped in v27.0.26 |
| `ENC-023` | ENC | **A** | confirmed | shipped in v27.0.33 |
| `ENC-024` | ENC | **A** | confirmed | shipped in v27.0.27 |
| `EXP-001` | EXP | **A** | tentative | pending |
| `FIG-001` | FIG | **D** | tentative | pending |
| `FIG-002` | FIG | **D** | tentative | pending |
| `FIG-003` | FIG | **D** | tentative | pending |
| `FIG-004` | FIG | **D** | tentative | pending |
| `FIG-005` | FIG | **D** | tentative | pending |
| `FIG-006` | FIG | **D** | tentative | pending |
| `FIG-007` | FIG | **D** | tentative | pending |
| `FIG-008` | FIG | **D** | tentative | pending |
| `FIG-009` | FIG | **D** | tentative | pending |
| `FIG-010` | FIG | **D** | tentative | pending |
| `FIG-011` | FIG | **D** | tentative | pending |
| `FIG-012` | FIG | **D** | tentative | pending |
| `FIG-013` | FIG | **D** | tentative | pending |
| `FIG-014` | FIG | **D** | tentative | pending |
| `FIG-015` | FIG | **D** | tentative | pending |
| `FIG-016` | FIG | **D** | tentative | pending |
| `FIG-017` | FIG | **D** | tentative | pending |
| `FIG-018` | FIG | **D** | tentative | pending |
| `FIG-019` | FIG | **D** | tentative | pending |
| `FIG-020` | FIG | **D** | tentative | pending |
| `FIG-021` | FIG | **D** | tentative | pending |
| `FIG-022` | FIG | **D** | tentative | pending |
| `FIG-023` | FIG | **D** | tentative | pending |
| `FIG-024` | FIG | **D** | tentative | pending |
| `FIG-025` | FIG | **D** | tentative | pending |
| `FONT-001` | FONT | **D** | tentative | pending |
| `FONT-002` | FONT | **D** | tentative | pending |
| `FONT-003` | FONT | **D** | tentative | pending |
| `FONT-004` | FONT | **D** | tentative | pending |
| `FONT-005` | FONT | **D** | tentative | pending |
| `FONT-006` | FONT | **D** | tentative | pending |
| `FONT-007` | FONT | **D** | tentative | pending |
| `FONT-008` | FONT | **D** | tentative | pending |
| `FONT-009` | FONT | **D** | tentative | pending |
| `FONT-010` | FONT | **D** | tentative | pending |
| `FONT-011` | FONT | **D** | tentative | pending |
| `FONT-012` | FONT | **D** | tentative | pending |
| `FONT-013` | FONT | **D** | tentative | pending |
| `FR-007` | FR | **A** | confirmed | shipped in v27.1.11 |
| `FR-008` | FR | **A** | tentative | pending |
| `HE-001` | HE | **A** | confirmed | shipped in v27.1.10 |
| `HI-001` | HI | **A** | confirmed | shipped in v27.1.10 |
| `IB-001` | IB | **A** | tentative | pending |
| `JA-001` | JA | **A** | confirmed | shipped in v27.1.13 |
| `JA-002` | JA | **A** | confirmed | shipped in v27.1.9 |
| `KO-001` | KO | **A** | tentative | pending |
| `L3-001` | L3 | **D** | tentative | pending |
| `L3-002` | L3 | **D** | tentative | pending |
| `L3-003` | L3 | **D** | tentative | pending |
| `L3-004` | L3 | **D** | tentative | pending |
| `L3-005` | L3 | **D** | tentative | pending |
| `L3-006` | L3 | **D** | tentative | pending |
| `L3-007` | L3 | **D** | tentative | pending |
| `L3-008` | L3 | **D** | tentative | pending |
| `L3-009` | L3 | **D** | tentative | pending |
| `L3-010` | L3 | **D** | tentative | pending |
| `L3-011` | L3 | **D** | tentative | pending |
| `LANG-001` | LANG | **A** | tentative | pending |
| `LANG-002` | LANG | **A** | tentative | pending |
| `LANG-003` | LANG | **A** | tentative | pending |
| `LANG-004` | LANG | **A** | tentative | pending |
| `LANG-005` | LANG | **A** | tentative | pending |
| `LANG-006` | LANG | **A** | tentative | pending |
| `LANG-007` | LANG | **A** | tentative | pending |
| `LANG-008` | LANG | **A** | tentative | pending |
| `LANG-009` | LANG | **A** | tentative | pending |
| `LANG-010` | LANG | **A** | tentative | pending |
| `LANG-011` | LANG | **A** | tentative | pending |
| `LANG-012` | LANG | **A** | tentative | pending |
| `LANG-013` | LANG | **A** | tentative | pending |
| `LANG-014` | LANG | **A** | tentative | pending |
| `LANG-015` | LANG | **A** | tentative | pending |
| `LANG-016` | LANG | **A** | tentative | pending |
| `LAY-001` | LAY | **C** | tentative | pending |
| `LAY-002` | LAY | **C** | tentative | pending |
| `LAY-003` | LAY | **C** | tentative | pending |
| `LAY-004` | LAY | **C** | tentative | pending |
| `LAY-005` | LAY | **C** | tentative | pending |
| `LAY-006` | LAY | **C** | tentative | pending |
| `LAY-007` | LAY | **C** | tentative | pending |
| `LAY-008` | LAY | **C** | tentative | pending |
| `LAY-009` | LAY | **C** | tentative | pending |
| `LAY-010` | LAY | **C** | tentative | pending |
| `LAY-011` | LAY | **C** | tentative | pending |
| `LAY-012` | LAY | **C** | tentative | pending |
| `LAY-013` | LAY | **C** | tentative | pending |
| `LAY-014` | LAY | **C** | tentative | pending |
| `LAY-015` | LAY | **C** | tentative | pending |
| `LAY-016` | LAY | **C** | tentative | pending |
| `LAY-017` | LAY | **C** | tentative | pending |
| `LAY-018` | LAY | **C** | tentative | pending |
| `LAY-019` | LAY | **C** | tentative | pending |
| `LAY-020` | LAY | **C** | tentative | pending |
| `LAY-021` | LAY | **C** | tentative | pending |
| `LAY-022` | LAY | **C** | tentative | pending |
| `LAY-023` | LAY | **C** | tentative | pending |
| `LAY-024` | LAY | **C** | tentative | pending |
| `LAY-025` | LAY | **C** | tentative | pending |
| `LAY-026` | LAY | **C** | tentative | pending |
| `LAY-027` | LAY | **C** | tentative | pending |
| `MATH-001` | MATH | **A** | tentative | pending |
| `MATH-002` | MATH | **A** | tentative | pending |
| `MATH-003` | MATH | **A** | tentative | pending |
| `MATH-004` | MATH | **A** | tentative | pending |
| `MATH-005` | MATH | **A** | tentative | pending |
| `MATH-006` | MATH | **A** | tentative | pending |
| `MATH-007` | MATH | **A** | tentative | pending |
| `MATH-008` | MATH | **A** | tentative | pending |
| `MATH-009` | MATH | **A** | confirmed | shipped in v27.1.11 |
| `MATH-010` | MATH | **A** | confirmed | shipped in v27.0.50 |
| `MATH-011` | MATH | **A** | tentative | pending |
| `MATH-012` | MATH | **A** | tentative | pending |
| `MATH-013` | MATH | **A** | tentative | pending |
| `MATH-014` | MATH | **A** | confirmed | shipped in v27.0.67 |
| `MATH-015` | MATH | **A** | confirmed | shipped in v27.0.48 |
| `MATH-016` | MATH | **A** | tentative | pending |
| `MATH-017` | MATH | **A** | tentative | pending |
| `MATH-018` | MATH | **A** | tentative | pending |
| `MATH-019` | MATH | **A** | tentative | pending |
| `MATH-020` | MATH | **A** | tentative | pending |
| `MATH-021` | MATH | **A** | tentative | pending |
| `MATH-022` | MATH | **A** | tentative | pending |
| `MATH-023` | MATH | **A** | tentative | pending |
| `MATH-024` | MATH | **A** | tentative | pending |
| `MATH-025` | MATH | **A** | tentative | pending |
| `MATH-026` | MATH | **A** | tentative | pending |
| `MATH-027` | MATH | **A** | tentative | pending |
| `MATH-028` | MATH | **A** | tentative | pending |
| `MATH-029` | MATH | **A** | confirmed | shipped in v27.1.5 |
| `MATH-030` | MATH | **A** | tentative | pending |
| `MATH-031` | MATH | **A** | tentative | pending |
| `MATH-032` | MATH | **A** | tentative | pending |
| `MATH-033` | MATH | **A** | tentative | pending |
| `MATH-034` | MATH | **A** | tentative | pending |
| `MATH-035` | MATH | **A** | tentative | pending |
| `MATH-036` | MATH | **A** | tentative | pending |
| `MATH-037` | MATH | **A** | tentative | pending |
| `MATH-038` | MATH | **A** | tentative | pending |
| `MATH-039` | MATH | **A** | tentative | pending |
| `MATH-040` | MATH | **A** | tentative | pending |
| `MATH-041` | MATH | **A** | tentative | pending |
| `MATH-042` | MATH | **A** | tentative | pending |
| `MATH-043` | MATH | **A** | confirmed | shipped in v27.1.11 |
| `MATH-044` | MATH | **A** | confirmed | shipped in v27.1.5 |
| `MATH-045` | MATH | **A** | tentative | pending |
| `MATH-046` | MATH | **A** | confirmed | shipped in v27.1.10 |
| `MATH-047` | MATH | **A** | tentative | pending |
| `MATH-048` | MATH | **A** | tentative | pending |
| `MATH-049` | MATH | **A** | tentative | pending |
| `MATH-050` | MATH | **A** | tentative | pending |
| `MATH-051` | MATH | **A** | tentative | pending |
| `MATH-052` | MATH | **A** | tentative | pending |
| `MATH-053` | MATH | **A** | confirmed | shipped in v27.0.66 |
| `MATH-054` | MATH | **A** | tentative | pending |
| `MATH-055` | MATH | **A** | tentative | pending |
| `MATH-056` | MATH | **A** | tentative | pending |
| `MATH-057` | MATH | **A** | tentative | pending |
| `MATH-058` | MATH | **A** | tentative | pending |
| `MATH-059` | MATH | **A** | tentative | pending |
| `MATH-060` | MATH | **A** | tentative | pending |
| `MATH-061` | MATH | **A** | confirmed | shipped in v27.1.11 |
| `MATH-062` | MATH | **A** | tentative | pending |
| `MATH-063` | MATH | **A** | tentative | pending |
| `MATH-064` | MATH | **A** | tentative | pending |
| `MATH-065` | MATH | **A** | tentative | pending |
| `MATH-066` | MATH | **A** | tentative | pending |
| `MATH-067` | MATH | **A** | tentative | pending |
| `MATH-068` | MATH | **A** | tentative | pending |
| `MATH-069` | MATH | **A** | tentative | pending |
| `MATH-070` | MATH | **A** | tentative | pending |
| `MATH-071` | MATH | **A** | tentative | pending |
| `MATH-072` | MATH | **A** | confirmed | shipped in v27.1.21 |
| `MATH-073` | MATH | **A** | tentative | pending |
| `MATH-074` | MATH | **A** | tentative | pending |
| `MATH-075` | MATH | **A** | tentative | pending |
| `MATH-076` | MATH | **A** | tentative | pending |
| `MATH-077` | MATH | **A** | tentative | pending |
| `MATH-078` | MATH | **A** | confirmed | shipped in v27.0.49 |
| `MATH-079` | MATH | **A** | tentative | pending |
| `MATH-080` | MATH | **A** | tentative | pending |
| `MATH-081` | MATH | **A** | tentative | pending |
| `MATH-082` | MATH | **A** | confirmed | shipped in v27.0.46 |
| `MATH-083` | MATH | **A** | confirmed | shipped in v27.1.5 |
| `MATH-084` | MATH | **A** | tentative | pending |
| `MATH-085` | MATH | **A** | tentative | pending |
| `MATH-086` | MATH | **A** | tentative | pending |
| `MATH-087` | MATH | **A** | tentative | pending |
| `MATH-088` | MATH | **A** | tentative | pending |
| `MATH-089` | MATH | **A** | tentative | pending |
| `MATH-090` | MATH | **A** | tentative | pending |
| `MATH-091` | MATH | **A** | confirmed | shipped in v27.1.21 |
| `MATH-092` | MATH | **A** | tentative | pending |
| `MATH-093` | MATH | **A** | tentative | pending |
| `MATH-094` | MATH | **A** | tentative | pending |
| `MATH-095` | MATH | **A** | confirmed | shipped in v27.1.13 |
| `MATH-096` | MATH | **A** | tentative | pending |
| `MATH-097` | MATH | **A** | confirmed | shipped in v27.0.51 |
| `MATH-098` | MATH | **A** | tentative | pending |
| `MATH-099` | MATH | **A** | tentative | pending |
| `MATH-100` | MATH | **A** | tentative | pending |
| `MATH-101` | MATH | **A** | tentative | pending |
| `MATH-102` | MATH | **A** | tentative | pending |
| `MATH-103` | MATH | **A** | tentative | pending |
| `MATH-104` | MATH | **A** | tentative | pending |
| `MATH-105` | MATH | **A** | tentative | pending |
| `MATH-106` | MATH | **A** | confirmed | shipped in v27.0.47 |
| `MATH-107` | MATH | **A** | tentative | pending |
| `MATH-108` | MATH | **A** | confirmed | shipped in v27.0.47 |
| `META-001` | META | **C** | tentative | pending |
| `META-002` | META | **C** | tentative | pending |
| `META-003` | META | **C** | tentative | pending |
| `META-004` | META | **C** | tentative | pending |
| `MOD-001` | MOD | **C** | tentative | pending |
| `MOD-002` | MOD | **C** | tentative | pending |
| `MOD-003` | MOD | **C** | tentative | pending |
| `MOD-004` | MOD | **C** | tentative | pending |
| `MOD-005` | MOD | **C** | tentative | pending |
| `MOD-006` | MOD | **C** | tentative | pending |
| `MOD-007` | MOD | **C** | tentative | pending |
| `MOD-008` | MOD | **C** | tentative | pending |
| `MOD-009` | MOD | **C** | tentative | pending |
| `MOD-010` | MOD | **C** | tentative | pending |
| `MOD-011` | MOD | **C** | tentative | pending |
| `MOD-012` | MOD | **C** | tentative | pending |
| `MOD-013` | MOD | **C** | tentative | pending |
| `MOD-020` | MOD | **C** | tentative | pending |
| `MOD-021` | MOD | **C** | tentative | pending |
| `MOD-022` | MOD | **C** | tentative | pending |
| `MOD-023` | MOD | **C** | tentative | pending |
| `MOD-024` | MOD | **C** | tentative | pending |
| `NL-001` | NL | **A** | tentative | pending |
| `NL-002` | NL | **A** | tentative | pending |
| `PDF-001` | PDF | **D** | tentative | pending |
| `PDF-002` | PDF | **D** | tentative | pending |
| `PDF-003` | PDF | **D** | tentative | pending |
| `PDF-004` | PDF | **D** | tentative | pending |
| `PDF-005` | PDF | **D** | tentative | pending |
| `PDF-006` | PDF | **D** | tentative | pending |
| `PDF-007` | PDF | **D** | tentative | pending |
| `PDF-008` | PDF | **D** | tentative | pending |
| `PDF-009` | PDF | **D** | tentative | pending |
| `PDF-010` | PDF | **D** | tentative | pending |
| `PDF-011` | PDF | **D** | tentative | pending |
| `PDF-012` | PDF | **D** | tentative | pending |
| `PKG-001` | PKG | **A** | tentative | pending |
| `PKG-002` | PKG | **A** | confirmed | shipped in v27.1.13 |
| `PKG-003` | PKG | **A** | tentative | pending |
| `PKG-004` | PKG | **A** | tentative | pending |
| `PKG-005` | PKG | **A** | tentative | pending |
| `PKG-006` | PKG | **A** | tentative | pending |
| `PKG-007` | PKG | **A** | confirmed | shipped in v27.1.13 |
| `PKG-008` | PKG | **A** | tentative | pending |
| `PKG-009` | PKG | **A** | tentative | pending |
| `PKG-010` | PKG | **A** | tentative | pending |
| `PKG-011` | PKG | **A** | confirmed | shipped in v27.1.12 |
| `PKG-012` | PKG | **A** | confirmed | shipped in v27.1.12 |
| `PKG-013` | PKG | **A** | tentative | pending |
| `PKG-014` | PKG | **A** | tentative | pending |
| `PKG-015` | PKG | **A** | tentative | pending |
| `PKG-016` | PKG | **A** | tentative | pending |
| `PKG-017` | PKG | **A** | tentative | pending |
| `PKG-018` | PKG | **A** | tentative | pending |
| `PKG-019` | PKG | **A** | tentative | pending |
| `PKG-020` | PKG | **A** | tentative | pending |
| `PKG-021` | PKG | **A** | tentative | pending |
| `PKG-022` | PKG | **A** | tentative | pending |
| `PKG-023` | PKG | **A** | confirmed | shipped in v27.1.13 |
| `PKG-024` | PKG | **A** | tentative | pending |
| `PKG-025` | PKG | **A** | tentative | pending |
| `PL-001` | PL | **A** | confirmed | shipped in v27.1.11 |
| `PL-002` | PL | **A** | tentative | pending |
| `PRJ-001` | PRJ | **C** | tentative | pending |
| `PRJ-002` | PRJ | **C** | tentative | pending |
| `PRJ-003` | PRJ | **C** | tentative | pending |
| `PRJ-004` | PRJ | **C** | tentative | pending |
| `PRT-001` | PRT | **A** | tentative | pending |
| `PRT-002` | PRT | **A** | tentative | pending |
| `PT-001` | PT | **A** | tentative | pending |
| `PT-002` | PT | **A** | tentative | pending |
| `PT-003` | PT | **A** | tentative | pending |
| `REF-001` | REF | **C** | tentative | pending |
| `REF-002` | REF | **C** | tentative | pending |
| `REF-003` | REF | **C** | tentative | pending |
| `REF-004` | REF | **C** | tentative | pending |
| `REF-005` | REF | **C** | tentative | pending |
| `REF-006` | REF | **C** | tentative | pending |
| `REF-007` | REF | **C** | tentative | pending |
| `REF-008` | REF | **C** | tentative | pending |
| `REF-009` | REF | **C** | tentative | pending |
| `REF-010` | REF | **C** | tentative | pending |
| `REF-011` | REF | **A** | confirmed | shipped in v27.1.12 |
| `REF-012` | REF | **C** | tentative | pending |
| `RO-001` | RO | **A** | confirmed | shipped in v27.1.9 |
| `RTL-001` | RTL | **A** | tentative | pending |
| `RTL-002` | RTL | **A** | tentative | pending |
| `RTL-003` | RTL | **A** | tentative | pending |
| `RTL-004` | RTL | **A** | tentative | pending |
| `RTL-005` | RTL | **A** | tentative | pending |
| `RU-001` | RU | **A** | confirmed | shipped in v27.1.11 |
| `RU-002` | RU | **A** | tentative | pending |
| `SCRIPT-001` | SCRIPT | **A** | confirmed | shipped in v27.1.5 |
| `SCRIPT-002` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-003` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-004` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-005` | SCRIPT | **A** | confirmed | shipped in v27.1.9 |
| `SCRIPT-006` | SCRIPT | **A** | confirmed | shipped in v27.1.9 |
| `SCRIPT-007` | SCRIPT | **A** | confirmed | shipped in v27.1.12 |
| `SCRIPT-008` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-009` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-010` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-011` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-012` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-013` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-014` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-015` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-016` | SCRIPT | **A** | confirmed | shipped in v27.1.3 |
| `SCRIPT-017` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-018` | SCRIPT | **A** | confirmed | shipped in v27.1.21 |
| `SCRIPT-019` | SCRIPT | **A** | confirmed | shipped in v27.1.5 |
| `SCRIPT-020` | SCRIPT | **A** | tentative | pending |
| `SCRIPT-021` | SCRIPT | **A** | confirmed | shipped in v27.1.21 |
| `SCRIPT-022` | SCRIPT | **A** | tentative | pending |
| `SPC-001` | SPC | **A** | tentative | pending |
| `SPC-002` | SPC | **A** | confirmed | shipped in v26.2.1 |
| `SPC-003` | SPC | **A** | confirmed | shipped in v26.3.1 |
| `SPC-004` | SPC | **A** | confirmed | shipped in v26.3.1 |
| `SPC-005` | SPC | **A** | confirmed | shipped in v26.3.1 |
| `SPC-006` | SPC | **A** | confirmed | shipped in v27.1.5 |
| `SPC-007` | SPC | **A** | tentative | pending |
| `SPC-008` | SPC | **A** | confirmed | shipped in v26.3.0 |
| `SPC-009` | SPC | **A** | confirmed | shipped in v26.3.0 |
| `SPC-010` | SPC | **A** | confirmed | shipped in v26.3.0 |
| `SPC-011` | SPC | **A** | confirmed | shipped in v26.3.0 |
| `SPC-012` | SPC | **A** | tentative | pending |
| `SPC-013` | SPC | **A** | tentative | pending |
| `SPC-014` | SPC | **A** | tentative | pending |
| `SPC-015` | SPC | **A** | tentative | pending |
| `SPC-016` | SPC | **A** | confirmed | shipped in v27.0.60 |
| `SPC-017` | SPC | **A** | tentative | pending |
| `SPC-018` | SPC | **A** | tentative | pending |
| `SPC-019` | SPC | **A** | confirmed | shipped in v27.0.55 |
| `SPC-020` | SPC | **A** | confirmed | shipped in v27.0.69 |
| `SPC-021` | SPC | **A** | confirmed | shipped in v27.0.60 |
| `SPC-022` | SPC | **A** | confirmed | shipped in v27.0.70 |
| `SPC-023` | SPC | **A** | tentative | pending |
| `SPC-024` | SPC | **A** | tentative | pending |
| `SPC-025` | SPC | **A** | confirmed | shipped in v27.0.59 |
| `SPC-026` | SPC | **A** | tentative | pending |
| `SPC-027` | SPC | **A** | confirmed | shipped in v27.0.68 |
| `SPC-028` | SPC | **A** | confirmed | shipped in v27.0.58 |
| `SPC-029` | SPC | **A** | confirmed | shipped in v27.1.9 |
| `SPC-030` | SPC | **A** | confirmed | shipped in v27.0.56 |
| `SPC-031` | SPC | **A** | confirmed | shipped in v27.1.5 |
| `SPC-032` | SPC | **A** | confirmed | shipped in v27.1.10 |
| `SPC-033` | SPC | **A** | confirmed | shipped in v27.1.9 |
| `SPC-034` | SPC | **A** | confirmed | shipped in v27.1.5 |
| `SPC-035` | SPC | **A** | confirmed | shipped in v27.0.56 |
| `STRUCT-001` | STRUCT | **A** | confirmed | shipped in v26.3.0 |
| `STRUCT-002` | STRUCT | **A** | confirmed | shipped in v26.3.0 |
| `STRUCT-003` | STRUCT | **A** | confirmed | shipped in v27.1.21 |
| `STRUCT-004` | STRUCT | **A** | tentative | pending |
| `STRUCT-005` | STRUCT | **A** | tentative | pending |
| `STYLE-001` | STYLE | **B** | tentative | pending |
| `STYLE-002` | STYLE | **B** | tentative | pending |
| `STYLE-003` | STYLE | **B** | tentative | pending |
| `STYLE-004` | STYLE | **B** | tentative | pending |
| `STYLE-005` | STYLE | **B** | tentative | pending |
| `STYLE-006` | STYLE | **B** | tentative | pending |
| `STYLE-007` | STYLE | **B** | tentative | pending |
| `STYLE-008` | STYLE | **B** | tentative | pending |
| `STYLE-009` | STYLE | **B** | tentative | pending |
| `STYLE-010` | STYLE | **B** | tentative | pending |
| `STYLE-011` | STYLE | **B** | tentative | pending |
| `STYLE-012` | STYLE | **B** | tentative | pending |
| `STYLE-013` | STYLE | **B** | tentative | pending |
| `STYLE-014` | STYLE | **B** | tentative | pending |
| `STYLE-015` | STYLE | **A** | confirmed | shipped in v27.1.6 |
| `STYLE-016` | STYLE | **B** | tentative | pending |
| `STYLE-017` | STYLE | **B** | tentative | pending |
| `STYLE-018` | STYLE | **B** | tentative | pending |
| `STYLE-019` | STYLE | **B** | tentative | pending |
| `STYLE-020` | STYLE | **B** | tentative | pending |
| `STYLE-021` | STYLE | **B** | tentative | pending |
| `STYLE-022` | STYLE | **B** | tentative | pending |
| `STYLE-023` | STYLE | **A** | confirmed | shipped in v27.1.6 |
| `STYLE-024` | STYLE | **A** | confirmed | shipped in v27.1.8 |
| `STYLE-025` | STYLE | **B** | tentative | pending |
| `STYLE-026` | STYLE | **B** | tentative | pending |
| `STYLE-027` | STYLE | **B** | tentative | pending |
| `STYLE-028` | STYLE | **B** | tentative | pending |
| `STYLE-029` | STYLE | **B** | tentative | pending |
| `STYLE-030` | STYLE | **B** | tentative | pending |
| `STYLE-031` | STYLE | **B** | tentative | pending |
| `STYLE-032` | STYLE | **B** | tentative | pending |
| `STYLE-033` | STYLE | **A** | confirmed | shipped in v27.1.8 |
| `STYLE-034` | STYLE | **B** | tentative | pending |
| `STYLE-035` | STYLE | **B** | tentative | pending |
| `STYLE-036` | STYLE | **B** | tentative | pending |
| `STYLE-037` | STYLE | **B** | tentative | pending |
| `STYLE-038` | STYLE | **B** | tentative | pending |
| `STYLE-039` | STYLE | **B** | tentative | pending |
| `STYLE-040` | STYLE | **B** | tentative | pending |
| `STYLE-041` | STYLE | **B** | tentative | pending |
| `STYLE-042` | STYLE | **B** | tentative | pending |
| `STYLE-043` | STYLE | **B** | tentative | pending |
| `STYLE-044` | STYLE | **B** | tentative | pending |
| `STYLE-045` | STYLE | **B** | tentative | pending |
| `STYLE-046` | STYLE | **B** | tentative | pending |
| `STYLE-047` | STYLE | **B** | tentative | pending |
| `STYLE-048` | STYLE | **B** | tentative | pending |
| `STYLE-049` | STYLE | **B** | tentative | pending |
| `SYS-001` | SYS | **D** | tentative | pending |
| `TAB-001` | TAB | **A** | tentative | pending |
| `TAB-002` | TAB | **A** | tentative | pending |
| `TAB-003` | TAB | **A** | tentative | pending |
| `TAB-004` | TAB | **A** | tentative | pending |
| `TAB-005` | TAB | **A** | tentative | pending |
| `TAB-006` | TAB | **A** | tentative | pending |
| `TAB-007` | TAB | **A** | tentative | pending |
| `TAB-008` | TAB | **A** | tentative | pending |
| `TAB-009` | TAB | **A** | tentative | pending |
| `TAB-010` | TAB | **A** | tentative | pending |
| `TAB-011` | TAB | **A** | tentative | pending |
| `TAB-012` | TAB | **A** | tentative | pending |
| `TAB-013` | TAB | **A** | tentative | pending |
| `TAB-014` | TAB | **A** | tentative | pending |
| `TAB-015` | TAB | **A** | tentative | pending |
| `TAB-016` | TAB | **A** | tentative | pending |
| `TH-001` | TH | **A** | tentative | pending |
| `TIKZ-001` | TIKZ | **A** | tentative | pending |
| `TIKZ-002` | TIKZ | **A** | tentative | pending |
| `TIKZ-003` | TIKZ | **A** | tentative | pending |
| `TIKZ-004` | TIKZ | **A** | tentative | pending |
| `TIKZ-005` | TIKZ | **A** | tentative | pending |
| `TIKZ-006` | TIKZ | **A** | tentative | pending |
| `TIKZ-007` | TIKZ | **A** | confirmed | shipped in v27.1.13 |
| `TIKZ-008` | TIKZ | **A** | tentative | pending |
| `TIKZ-009` | TIKZ | **A** | tentative | pending |
| `TIKZ-010` | TIKZ | **A** | tentative | pending |
| `TR-001` | TR | **A** | tentative | pending |
| `TYPO-001` | TYPO | **A** | confirmed | shipped in v27.0.8 |
| `TYPO-002` | TYPO | **A** | confirmed | shipped in v26.2.1 |
| `TYPO-003` | TYPO | **A** | confirmed | shipped in v26.2.1 |
| `TYPO-004` | TYPO | **A** | confirmed | shipped in v27.0.6 |
| `TYPO-005` | TYPO | **A** | confirmed | shipped in v27.0.7 |
| `TYPO-006` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-007` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-008` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-009` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-010` | TYPO | **A** | confirmed | shipped in v27.0.5 |
| `TYPO-011` | TYPO | **A** | tentative | pending |
| `TYPO-012` | TYPO | **A** | confirmed | shipped in v27.0.21 |
| `TYPO-013` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-014` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-015` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-016` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-017` | TYPO | **A** | confirmed | shipped in v27.0.18 |
| `TYPO-018` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-019` | TYPO | **B** | confirmed | deferred (NLP) |
| `TYPO-020` | TYPO | **B** | confirmed | deferred (NLP) |
| `TYPO-021` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-022` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-023` | TYPO | **A** | confirmed | shipped in v27.1.5 |
| `TYPO-024` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-025` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-026` | TYPO | **A** | confirmed | shipped in v26.3.1 |
| `TYPO-027` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-028` | TYPO | **A** | confirmed | shipped in v27.0.20 |
| `TYPO-029` | TYPO | **A** | confirmed | shipped in v27.0.12 |
| `TYPO-030` | TYPO | **B** | confirmed | deferred (NLP) |
| `TYPO-031` | TYPO | **B** | confirmed | deferred (NLP) |
| `TYPO-032` | TYPO | **A** | confirmed | shipped in v27.0.14 |
| `TYPO-033` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-034` | TYPO | **A** | confirmed | shipped in v27.0.11 |
| `TYPO-035` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-036` | TYPO | **A** | tentative | pending |
| `TYPO-037` | TYPO | **A** | confirmed | shipped in v26.3.0 |
| `TYPO-038` | TYPO | **A** | confirmed | shipped in v27.0.9 |
| `TYPO-039` | TYPO | **A** | confirmed | shipped in v27.0.13 |
| `TYPO-040` | TYPO | **A** | tentative | pending |
| `TYPO-041` | TYPO | **A** | tentative | pending |
| `TYPO-042` | TYPO | **A** | confirmed | shipped in v27.0.15 |
| `TYPO-043` | TYPO | **A** | tentative | pending |
| `TYPO-044` | TYPO | **A** | tentative | pending |
| `TYPO-045` | TYPO | **A** | tentative | pending |
| `TYPO-046` | TYPO | **A** | confirmed | shipped in v27.0.19 |
| `TYPO-047` | TYPO | **A** | tentative | pending |
| `TYPO-048` | TYPO | **A** | tentative | pending |
| `TYPO-049` | TYPO | **A** | confirmed | shipped in v27.0.17 |
| `TYPO-050` | TYPO | **A** | tentative | pending |
| `TYPO-051` | TYPO | **A** | confirmed | shipped in v27.0.16 |
| `TYPO-052` | TYPO | **A** | confirmed | shipped in v27.1.3 |
| `TYPO-053` | TYPO | **A** | confirmed | shipped in v27.0.44 |
| `TYPO-054` | TYPO | **A** | confirmed | shipped in v27.1.3 |
| `TYPO-055` | TYPO | **A** | confirmed | shipped in v27.0.43 |
| `TYPO-056` | TYPO | **A** | confirmed | shipped in v27.1.13 |
| `TYPO-057` | TYPO | **A** | confirmed | shipped in v27.0.72 |
| `TYPO-058` | TYPO | **A** | confirmed | shipped in v27.1.9 |
| `TYPO-059` | TYPO | **A** | tentative | pending |
| `TYPO-060` | TYPO | **A** | tentative | pending |
| `TYPO-061` | TYPO | **A** | confirmed | shipped in v27.0.52 |
| `TYPO-062` | TYPO | **A** | confirmed | shipped in v27.1.5 |
| `TYPO-063` | TYPO | **A** | tentative | pending |
| `VERB-001` | VERB | **A** | tentative | pending |
| `VERB-002` | VERB | **A** | confirmed | shipped in v27.1.6 |
| `VERB-003` | VERB | **A** | tentative | pending |
| `VERB-004` | VERB | **A** | tentative | pending |
| `VERB-005` | VERB | **A** | tentative | pending |
| `VERB-006` | VERB | **A** | tentative | pending |
| `VERB-007` | VERB | **A** | tentative | pending |
| `VERB-008` | VERB | **A** | tentative | pending |
| `VERB-009` | VERB | **A** | tentative | pending |
| `VERB-010` | VERB | **A** | tentative | pending |
| `VERB-011` | VERB | **A** | tentative | pending |
| `VERB-012` | VERB | **A** | tentative | pending |
| `VERB-013` | VERB | **A** | tentative | pending |
| `VERB-014` | VERB | **A** | tentative | pending |
| `VERB-015` | VERB | **A** | tentative | pending |
| `VERB-016` | VERB | **A** | tentative | pending |
| `VERB-017` | VERB | **A** | tentative | pending |
| `ZH-001` | ZH | **A** | tentative | pending |
| `ZH-002` | ZH | **A** | tentative | pending |

## Acceptance-criteria status

Per `V27_FIX_PRODUCER_CADENCE.md` § Acceptance criteria:

- [x] `specs/v27/FIX_PRODUCER_LEDGER.md` exists with full bucket
  assignments for all 660 rules. **DONE** (this file).
- [ ] At each patch release, ≥10 new producers shipped from Bucket A.
  **PENDING** — actual cadence has been ~1 producer per patch since
  v27.0.5 (user-driven cadence prioritizing audit depth over throughput).
- [x] Bucket D rules carry `produces_fix: false` in `rule_contracts.yaml`
  with documented reason.  **DONE** (v27.0.42 — all 62 Bucket D rules +
  4 NLP-deferred + 2 redundant + 1 deferred-refinement = 69 explicit
  `produces_fix: false` entries, plus 67 `produces_fix: true` for shipped
  producers).  Source: `pick_produces_fix` in
  `scripts/tools/generate_rule_contracts.py`.
- [ ] Differential test passes 0 diffs vs prior tag (default invocation;
  fix producers gated behind `--apply-fixes`).
  **ACHIEVED** every cycle since v27.0.5.
- [ ] Bucket A shipped fully by v27.2.0 (target).
  **TRACKING** — 166 of 465 Bucket A
  rules shipped. At current 1/cycle pace, full Bucket A completion
  would arrive much later than v27.2.0; cadence target needs review.
- [ ] Bucket B + C shipped fully by v27.4.0 (target).
  **TRACKING** — 0 of 53 Bucket B + 0 of 87 Bucket C shipped.

## Next-pick guidance

For the next mechanical fix-producer cycle, prefer:

1. **ENC family**: 24 total, 13 shipped, 11 pending. Remaining mostly
   require non-trivial decisions (homoglyph direction, multi-char
   mappings, complex semantics).
2. **MATH family**: 108 total, 0 shipped. Largest untapped Bucket A pool.
   Most rules are simple environment-name / command-syntax checks.
3. **TYPO family**: 63 total, 36 shipped, 23 pending (4 NLP-deferred).
   Remaining 23 include ambiguous-fix cases (TYPO-040 math-too-long,
   TYPO-041 ldots-spacing, TYPO-047 starred section, TYPO-048 en-dash-
   as-minus).
4. **CHAR family**: 22 total, 0 shipped. Each rule targets a specific
   problematic character — all mechanical deletion or substitution.
