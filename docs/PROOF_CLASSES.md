# Proof Taxonomy

Canonical reference for the proof classes in LaTeX Perfectionist.
Counts sourced from `governance/project_facts.yaml` (regenerated per release).

---

## Classification

### Formal Faithful (637 rules)

The Coq check function mirrors the OCaml validator's logic. If the Coq
model says "no violation," the OCaml validator agrees.

**VPD pattern families**: count_substring, multi_substring, count_char,
byte_ge, byte_range, line_pred, multi_substring_all, substring_pair,
terminated_command_pair, paragraph_terminated_command_pair.

**Proof tactic**: `qed_text_sound` from `RegexFamily.v`.

### Formal Conservative (20 rules)

The Coq check function returns `false` — vacuously sound. Used for rules
that check external binary files (PNG metadata, PDF structure, font cmap
tables) where no Coq string model is possible.

**The 20 rules are L3 file-based validators**:
FIG-004, FIG-006, FIG-016, FIG-021, FIG-023,
COL-001, COL-002, COL-003, COL-004, COL-005, COL-007,
PDF-006, PDF-007, PDF-008, PDF-009, PDF-011, PDF-012,
TIKZ-002, TIKZ-008, CJK-007.

### Formal Conditional (3 rules) — new in v26.1

Sound *given a compile-log predicate*. The Coq theorem has the shape
`P (log) → validator(src, log) correct`, where `P` is a declared
contract on the log event list. Safe when the log is produced by an
admissible engine run; no claim otherwise.

**The 3 rules are compile-log LAY diagnostics**:
LAY-025 (rerun required), LAY-026 (citation undefined), LAY-027 (font
substitution). Proved in `proofs/BuildLog.v` via
`lay_025_conditional_sound` / `lay_026_conditional_sound` /
`lay_027_conditional_sound` (QED, zero admits).

### Hypothesis-parametric (v26.2 substrate, memo §5 + §7.4)

Load-bearing Coq scaffolding whose final step is parametric in an
abstract hypothesis discharged by v27 WS8 (concrete toolchain model)
or v26.3 (runtime/structure discharge). Per ADR-004, this pattern
keeps the v26.2 substrate honest without making unbounded toolchain
promises.

**Files & their parametric hypotheses** (documented in
`proofs/ADMISSIBILITY_MAP.md`):

- `CompileProgress.v` — `compile_progress_rule` (T6).
- `CompileWellFormed.v` — `output_wellformed_rule` (T7).
- `CSTRoundTrip.v` — `builder_partitions` + `parse_serialize_is_id_on_subset`
  (structure-lossless; byte-lossless is unconditional).
- `RewritePreservesCST.v` — `apply_total` (edit-application totality).
- `RewritePreservesSemantics.v` — `tokens_ws_empty` + `tokens_concat`
  (whitespace-preservation lemmas).

The `proofs/CSTtoASTSound.v` and `proofs/ArtifactGraphSound.v` files
(memo §7.4 / §8.5 aliases) re-export the relevant substantive
theorems under the memo-prescribed names.

### Statistical / ML-Validated (8 rules, overlay)

The v2 ByteClassifier provides empirical precision/recall bounds for
8 ambiguous TYPO rules. Bounds are proved in
`proofs/ML/SpanExtractorSound.v`:

- Measured FP rate: 0.025 (precision ≥ 0.94 threshold)
- Measured FN rate: 0.015 (recall ≥ 0.94 threshold)
- Theorem: `v2_span_extractor_sound` (QED)

**Rules**: TYPO-001, TYPO-005, TYPO-012, TYPO-028,
TYPO-048, TYPO-052, TYPO-056, TYPO-062.

These rules also have formal faithful proofs for their deterministic
substring patterns. The ML bound is an additional statistical guarantee
for context-dependent disambiguation.

---

## Execution Classes (v26)

See `docs/SUPPORT_MATRIX.yaml` (machine-readable) and
`proofs/ExecutionClasses.v` (formal isolation theorems).

| Class | Name | Latency | Proof requirement |
|-------|------|---------|-------------------|
| A | Keystroke-critical | p95 ≤ 1.2 ms | Formal faithful; hot-path state only |
| B | Debounce semantic | p95 ≤ 100 ms | Formal faithful or conservative |
| C | Build-coupled | Async (save/build) | Conservative or conditional + build evidence |
| D | Heuristic/advisory | Best-effort | Statistical or none; never mutates A results |

Each rule carries its execution class in `specs/rules/rule_contracts.yaml`
(`execution_class` field). CI enforces runtime/contract parity.

---

## Summary

Per-rule classification (rule-level soundness proofs):

| Class | Count | Percentage |
|-------|-------|-----------|
| Formal faithful | 637 | 98.9% |
| Formal conservative | 20 | 3.1% |
| Formal conditional | 3 | 0.5% |
| Statistical (ML) | 8 | (overlay on faithful) |
| **Total with proofs** | **660** | **100% (of 644 shipped; 16 Reserved excluded)** |

Substrate proofs (not per-rule; memo §4–§8):

| Area | Files | Status |
|------|-------|--------|
| Language contract (memo §4) | LanguageContract.v | Formal faithful |
| Compile-guarantee T0–T5 (memo §5) | ProjectClosure, BuildProfileSound, T0/T1/T4/T5_wrapper | Formal faithful |
| Compile-guarantee T6/T7 (memo §5) | CompileProgress, CompileWellFormed | Hypothesis-parametric |
| Partial-document E0–E3 (memo §6) | PartialParseLocality, DamageContainment, RepairMonotonicity, StableNodeIds | Formal faithful |
| CST round-trip (memo §7) | CSTRoundTrip, CSTtoASTSound (alias) | Byte-lossless formal faithful + structure-lossless hypothesis-parametric |
| Rewrite preservation (memo §7) | RewritePreservesCST, RewritePreservesSemantics | Hypothesis-parametric |
| Artefact graph (memo §8) | ProjectClosure, ArtifactGraphSound (alias) | Formal faithful |
| Execution classes (memo §11) | ExecutionClasses.v | Formal faithful |
