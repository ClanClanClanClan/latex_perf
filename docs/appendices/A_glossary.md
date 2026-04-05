# Appendix A — Glossary & Notation

Per v25 master plan §15, Table A (8 pages).

## Core Terminology

| Term | Definition |
|------|-----------|
| **Arena** | Bump-allocated memory region for token storage; freed as a unit |
| **Catcode** | TeX category code (0–15) assigned to each input character |
| **Delta** | Incremental change between two layer snapshots |
| **Elder** | Orchestrator process managing cross-layer state synchronisation |
| **Fuel** | Bounded recursion counter preventing non-termination in macro expansion |
| **Generation** | Monotonically increasing counter for snapshot versioning |
| **Golden test** | Corpus file with expected validator results in YAML (fire/no-fire assertions) |
| **Layer** | One of five processing stages: L0 (Lexer), L1 (Expander), L2 (Parser), L3 (Semantics), L4 (Style) |
| **Pilot** | Feature-flagged subset of validators enabled via `L0_VALIDATORS=pilot` |
| **Rule** | A single validation check with ID, severity, message, and run function |
| **Snapshot** | Immutable view of all layer states at a given generation |
| **VPD** | Variable Pattern Detection — catalogue of regex/substring patterns for proof generation |

## Rule Families

| Prefix | Layer | Count | Domain |
|--------|-------|-------|--------|
| TYPO | L0 | 63 | Typography (quotes, dashes, accents) |
| SPC | L0 | 35 | Spacing and whitespace |
| ENC | L0 | 24 | Encoding and character validation |
| CHAR | L0 | 22 | Control characters and Unicode |
| VERB | L0 | 17 | Verbatim and code environments |
| CMD | L0/L2 | 14 | Command definition and usage |
| DELIM | L1 | 11 | Delimiter matching |
| MATH | L1/L2 | 100 | Mathematical notation |
| REF | L1/L2 | 12 | Cross-references and citations |
| SCRIPT | L1 | 22 | Sub/superscript formatting |
| TAB | L2 | 16 | Table structure |
| FIG | L2/L3 | 25 | Figure and float handling |
| PKG | L2/L3 | 25 | Package compatibility |
| TIKZ | L2/L3 | 10 | TikZ/PGF diagrams |
| LAY | L3 | 24 | Page layout and typography |
| COL | L3 | 7 | Color management |
| PDF | L3 | 12 | PDF structure and accessibility |
| FONT | L1/L3 | 13 | Font selection and metrics |
| LANG | L2/L4 | 16 | Language consistency |
| RTL | L1/L3 | 5 | Right-to-left text |
| CJK | L0/L3 | 16 | CJK character handling |
| STYLE | L4 | 49 | Prose style and consistency |
| CHEM | L1 | 10 | Chemistry notation |
| L3 (expl3) | L1/L2 | 11 | LaTeX3 programming |
| META | L2/L3 | 4 | PDF metadata |
| DOC | L2/L3 | 5 | Document structure |
| BIB | L3 | 17 | Bibliography hygiene |

## Severity Levels

| Level | Meaning | CI Gate |
|-------|---------|---------|
| **Error** | Likely compilation failure or broken output | Blocks merge |
| **Warning** | Probable issue requiring attention | Informational |
| **Info** | Style suggestion or best practice | Informational |

## Notation

- `p95` — 95th percentile latency
- `QED` — Proof completed with no admits
- `SLA` — Service Level Agreement (performance gate threshold)
- `FPR` — False Positive Rate
- `BIO` — Begin/Inside/Outside tagging scheme for span extraction
