# Candidate Coverage Backlog — the remaining fixable rules

> Source: rule-coverage audit @ v27.1.40. **119 candidate-able rules still diagnose-only**
> (34 medium, 85 large). Resume the systematic "all rules" work from here — wire each as a
> Bucket-C candidate (`mk_result_with_candidates`, `--apply-fixes-for` byte-identical) with the
> adversarial-verify catching genuine meaning-changes. Current: 167 producers + 69 candidates.

Total remaining: **119** (34 medium, 85 large).

## BIB (6)
- **BIB-003** [medium] — BIB field normalization; varies by bibliography style
- **BIB-006** [medium] — BIB name-parsing and formatting; review gate needed
- **BIB-014** [medium] — BIB key-rename; updates every \cite atomically (corruption risk)
- **BIB-015** [medium] — BIB local field edit
- **BIB-016** [medium] — BIB field normalization
- **BIB-017** [medium] — BIB field normalization

## CHAR (1)
- **CHAR-020** [medium] — Sharp-S ß→SS in uppercase context (orthography-dependent, CP-3-risky like DE-006)

## CHEM (3)
- **CHEM-002** [medium] — Chemical formula brace/wrap
- **CHEM-003** [medium] — Chemistry notation fix
- **CHEM-008** [medium] — Chemical charge/subscript notation

## CS (1)
- **CS-002** [large] — Czech-specific localization

## DOC (1)
- **DOC-005** [medium] — Documentation environment fix

## LANG (8)
- **LANG-001** [large] — Language-specific spelling/case variant; dictionary-driven with config choice
- **LANG-003** [large] — Quote localization; language/script-detection heuristics
- **LANG-006** [large] — Language-specific quote nesting
- **LANG-007** [large] — Language-aware localization
- **LANG-010** [large] — Locale-specific character normalization
- **LANG-011** [large] — Language variant detection
- **LANG-014** [large] — Language variant detection
- **LANG-015** [large] — Language-specific normalization

## MATH (22)
- **MATH-020** [large] — Math normalization; may change rendering intent
- **MATH-021** [large] — Math rendering/intent change
- **MATH-024** [large] — Remove/simplify redundant math markup; may change rendering
- **MATH-028** [large] — Heterogeneous math edits
- **MATH-030** [large] — Math normalization; rendering implications
- **MATH-033** [large] — Redundancy elimination; heterogeneous transformations
- **MATH-037** [large] — Math rendering intent normalization
- **MATH-040** [large] — Simplify/remove redundancy in math
- **MATH-041** [large] — Math simplification
- **MATH-049** [medium] — Differential or unit spacing suggestion
- **MATH-056** [large] — Multi-site math refactor; coordination required
- **MATH-065** [large] — Math mode rendering/simplification
- **MATH-073** [large] — Normalize math rendering style (displaystyle/textstyle/limits)
- **MATH-075** [large] — Math rendering intent change; review needed
- **MATH-079** [large] — Redundancy/rendering normalization
- **MATH-081** [medium] — Differential-d or unit spacing
- **MATH-084** [large] — Math simplification with rendering implications
- **MATH-088** [medium] — Math spacing normalization
- **MATH-092** [large] — Normalize math intent; may affect visual output
- **MATH-094** [large] — Heterogeneous math refactor
- **MATH-099** [large] — Math rendering style change
- **MATH-105** [large] — Rendering-intent normalization

## NL (2)
- **NL-001** [large] — Dutch IJ digraph capitalization at sentence start
- **NL-002** [large] — Dutch-specific localization

## PKG (12)
- **PKG-001** [large] — Preamble package reordering; ordering/engine-detection heuristics
- **PKG-004** [large] — Package option/load normalization
- **PKG-006** [large] — Package hygiene suggestion
- **PKG-008** [large] — Package option reordering/addition
- **PKG-009** [large] — Package configuration change; may affect build behavior
- **PKG-010** [large] — Package option normalization
- **PKG-013** [large] — Package-specific hygiene
- **PKG-015** [large] — Package reordering/configuration
- **PKG-016** [large] — Package option suggestion
- **PKG-018** [large] — Package load/option fix
- **PKG-020** [large] — Package configuration change
- **PKG-024** [large] — Preamble package ordering/engine-detection

## PL (1)
- **PL-002** [large] — Polish-specific character/quote normalization

## PT (2)
- **PT-001** [large] — Portuguese spelling variant; dictionary-driven choice
- **PT-003** [large] — Portuguese-specific normalization

## REF (4)
- **REF-003** [large] — Label/cite-key rename; cross-file atomic update (corruption risk)
- **REF-004** [large] — Cross-reference normalization; atomic \ref/\cite update
- **REF-005** [large] — Reference key renaming
- **REF-007** [large] — Label consistency normalization

## RTL (2)
- **RTL-001** [large] — Right-to-left text normalization
- **RTL-002** [large] — RTL script handling

## SCRIPT (8)
- **SCRIPT-002** [medium] — Wrap/reorder sub/superscript; identifier vs product ambiguity
- **SCRIPT-003** [medium] — Brace sub/superscript notation
- **SCRIPT-004** [medium] — Script notation normalization
- **SCRIPT-012** [medium] — Script brace/wrap suggestion
- **SCRIPT-013** [medium] — Script notation fix
- **SCRIPT-014** [medium] — Subscript/superscript normalization
- **SCRIPT-020** [medium] — Script notation in math
- **SCRIPT-022** [medium] — Sub/superscript wrapping

## SPC (3)
- **SPC-001** [medium] — Whitespace normalization
- **SPC-015** [medium] — Spacing edge case fix
- **SPC-026** [medium] — Indentation/reflow suggestion; review-heavy

## STYLE (21)
- **STYLE-001** [large] — Prose punctuation normalization; majority-convention detection needed
- **STYLE-002** [large] — Dictionary-driven spelling variant; config-dependent target
- **STYLE-007** [large] — Style punctuation fix; review gate needed
- **STYLE-011** [large] — Prose styling normalization
- **STYLE-014** [large] — Punctuation/style convention alignment
- **STYLE-016** [large] — Prose style fix
- **STYLE-022** [large] — Punctuation normalization
- **STYLE-026** [large] — Style convention detection and suggestion
- **STYLE-030** [large] — Spelling/case variant normalization
- **STYLE-032** [large] — Spelling variant detection and suggestion
- **STYLE-034** [large] — Punctuation/spacing style fix
- **STYLE-035** [large] — Prose style normalization
- **STYLE-036** [large] — Style convention alignment
- **STYLE-039** [large] — Punctuation style suggestion
- **STYLE-040** [large] — Prose/punctuation normalization
- **STYLE-041** [large] — Style convention fix
- **STYLE-043** [large] — Punctuation normalization
- **STYLE-046** [large] — Style convention detection
- **STYLE-047** [large] — Quote-punctuation normalization; corruption-prone—needs careful review
- **STYLE-048** [large] — Case/spelling normalization
- **STYLE-049** [large] — Prose punctuation fix

## TAB (10)
- **TAB-002** [large] — Table column/row normalization
- **TAB-007** [large] — Table structure simplification
- **TAB-008** [large] — Longtable conversion; heavy restructuring needed
- **TAB-009** [large] — Table environment transformation
- **TAB-010** [large] — Table footnote handling
- **TAB-011** [large] — Table normalization; booktabs preconditions
- **TAB-013** [large] — Table structure edit
- **TAB-014** [large] — Table formatting/normalization
- **TAB-015** [large] — Table column rule simplification
- **TAB-016** [large] — Table environment edit

## TH (1)
- **TH-001** [large] — Thai script handling

## TIKZ (4)
- **TIKZ-001** [medium] — TikZ code/options normalization
- **TIKZ-003** [medium] — TikZ environment/option fix
- **TIKZ-004** [medium] — TikZ code simplification
- **TIKZ-005** [medium] — TikZ build-config change; review-heavy

## TR (1)
- **TR-001** [large] — Turkish locale-specific normalization

## TYPO (5)
- **TYPO-041** [medium] — Ellipsis spacing; ldots-spacing ambiguity
- **TYPO-043** [medium] — Typo fix in verbatim/lstlisting; gate interaction
- **TYPO-047** [medium] — Starred section detection; count-drift history
- **TYPO-048** [medium] — En-dash vs minus normalization; semantic ambiguity
- **TYPO-060** [medium] — Literal typo in verbatim/lstlisting; gate interaction

## ZH (1)
- **ZH-002** [large] — Chinese punctuation localization; RTL/CJK edge cases

## ✅ Correction (2026-07-12): candidates ARE intent/render-changing-tolerant

Bucket-C candidates are review-only, author-confirmed suggestions (docs/CANDIDATE_FIXES.md;
fixability audit category C4 = "rendering-intent normalization" is a CANDIDATE target).
So RENDER-CHANGING is NOT a deferral reason — the author reviews. A rule is candidate-able
iff its intended fix has a DETERMINATE, well-bounded edit that is byte-safe (never
auto-applied). Defer ONLY when there is genuinely no determinate edit target (e.g. SPC-001
"line too long" has no canonical break point) or an inherently unbounded multi-site refactor
with no single coherent edit. Cross-file renames (REF) ARE candidate-able as in-file
multi-edit or label-only candidates (byte-safe; the author applies + propagates). The prior
"render-changing -> diagnose-only" deferrals were WRONG and are being re-wired.

