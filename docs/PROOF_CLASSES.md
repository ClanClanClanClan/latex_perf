# Proof Taxonomy

Canonical reference for the three proof classes in LaTeX Perfectionist.
Counts sourced from `governance/project_facts.yaml`.

---

## Classification

### Formal Faithful (606 rules)

The Coq check function mirrors the OCaml validator's logic. If the Coq model
says "no violation," the OCaml validator agrees.

**VPD pattern families**: count_substring, multi_substring, count_char,
byte_ge, byte_range, line_pred, multi_substring_all, substring_pair,
terminated_command_pair, paragraph_terminated_command_pair.

**Proof tactic**: `qed_text_sound` from `RegexFamily.v`.

### Formal Conservative (20 rules)

The Coq check function returns `false` — vacuously sound. Used for rules
that check external binary files (PNG metadata, PDF structure, font cmap
tables) where no Coq string model is possible.

**All 20 rules are L3 file-based validators**:
FIG-004, FIG-006, FIG-016, FIG-021, FIG-023,
COL-001, COL-002, COL-003, COL-004, COL-005, COL-007,
PDF-006, PDF-007, PDF-008, PDF-009, PDF-011, PDF-012,
TIKZ-002, TIKZ-008, CJK-007.

### Statistical / ML-Validated (8 rules)

The v2 ByteClassifier provides empirical precision/recall bounds for
8 ambiguous TYPO rules. The bounds are proved in
`proofs/ML/SpanExtractorSound.v`:

- Measured FP rate: 0.025 (precision ≥ 0.94 threshold)
- Measured FN rate: 0.015 (recall ≥ 0.94 threshold)
- Theorem: `v2_span_extractor_sound` (QED)

**Rules**: TYPO-001, TYPO-005, TYPO-012, TYPO-028,
TYPO-048, TYPO-052, TYPO-056, TYPO-062.

Note: These rules also have formal faithful proofs for their deterministic
substring patterns. The ML bound is an additional statistical guarantee
for context-dependent disambiguation.

---

## Execution Classes (v26 planned)

| Class | Name | Latency | Proof requirement |
|-------|------|---------|-------------------|
| A | Keystroke-critical | <1ms | Formal faithful |
| B | Debounce-semantic | <100ms | Formal faithful or conservative |
| C | Build-coupled | Async | Conservative + build verification |
| D | Heuristic/advisory | Best-effort | Statistical or none |

---

## Summary

| Class | Count | Percentage |
|-------|-------|-----------|
| Formal faithful | 606 | 96.8% |
| Formal conservative | 20 | 3.2% |
| Statistical (ML) | 8 | (overlay on faithful) |
| **Total with proofs** | **626** | **100%** |
