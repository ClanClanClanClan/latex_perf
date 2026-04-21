# Proof-Writers Guide

Revision 2026-04-13. Updated every MINOR release (spec L-9).

---

## Quick Start

1. All proofs live in `proofs/` (core) or `proofs/generated/` (auto-generated)
2. Build: `dune build proofs` (or `dune build` for everything)
3. Zero admits required — CI blocks on any `Admitted` or `Axiom`
4. Coq version: 8.18.0 (exact, pinned in opam)

---

## Proof Organization

```
proofs/
├── CoreProofs.v            # Foundation imports
├── Catcode.v               # Catcode bijection (nat_catcode_inverse)
├── LexerDeterminism.v      # lexer_step_determinism
├── LexerTotality.v         # lexer_step_total_nonempty
├── LexerFaithfulStep.v     # step_deterministic, step_progress
├── LexerSmallstep.v        # Small-step lexer semantics
├── LexerIncremental.v      # Incremental re-lex correctness (379 lines)
├── LexerSoA.v              # SoA layout proofs (715 lines)
├── L0Smallstep.v           # Catcode-sensitive classifier
├── L0SmallstepControl.v    # Control-flow small-step
├── Expand.v                # Full expansion proofs (597 lines)
├── ExpandProofsFinal.v     # sufficient_fuel, expand_no_teof
├── RegexFamily.v           # Generic soundness tactic (292 lines)
├── ParserSound.v           # 12 parser theorems
├── InterpLocality.v        # Diff algebra (8 theorems)
├── LabelsUnique.v          # Duplicate label detection
├── ValidatorGraphProofs.v  # DAG acyclicity
├── SnapshotConsistency.v   # Cross-layer snapshot consistency
├── ElderProofs.v           # Update preserves length
├── Arena_safe.v            # Arena memory safety (217 lines)
├── ListWindow.v            # List windowing correctness
├── SectionRebalance.v      # Renumber preserves shape
├── SplitPreservesOrder.v   # Sorted segments increasing
├── generated/              # 108 auto-generated per-rule proofs
│   ├── L0_TYPO.v ... L4_STYLE.v
│   └── Catalogue.v         # Master import of all generated files
└── ML/
    └── SpanExtractorSound.v  # ML model precision/recall bounds
```

---

## Writing a New Proof

### Step 1: Identify the theorem

Each validator rule needs a soundness theorem stating: "if the check function
returns true, then the document contains the pattern."

### Step 2: Choose the proof strategy

**For text-scanning rules** (substring, character count, byte range):

Use the `qed_text_sound` tactic from `RegexFamily.v`:

```coq
Require Import LaTeXPerfectionist.RegexFamily.

Definition my_rule_chk (s : string) : bool :=
  string_contains_substring s "\\textbf".

Theorem my_rule_sound :
  forall doc, text_validator my_rule_chk
    (mk_iss "MY-001" "Description" Warning None) doc = [] ->
  text_check_absent my_rule_chk doc.
Proof. qed_text_sound. Qed.
```

**For complex rules** (cross-reference, semantic, external file):

Use conservative models (`false`) — vacuously sound:

```coq
Definition my_complex_chk (s : string) : bool := false.
(* Conservative: no VPD pattern — check function returns false. *)
```

### Step 3: Register in the generator

Add the rule to `specs/rules/vpd_patterns.json` with the appropriate pattern
family. Then run:

```bash
python3 scripts/infra/proof_farm/gen_coq_proofs.py
```

This generates/updates `proofs/generated/L{0-4}_{FAMILY}.v` files.

---

## Pattern Families (VPD)

| Family | Coq Function | Example |
|--------|-------------|---------|
| `count_char` | `string_contains` | Single character presence |
| `count_substring` | `string_contains_substring` | Substring presence |
| `multi_substring` | `multi_substring_check` | Any of N substrings |
| `byte_ge` | `string_has_byte_ge` | Byte ≥ threshold |
| `byte_range` | `string_has_byte_in_range` | Byte in [lo, hi] |
| `line_pred` | (custom) | Per-line predicate |
| `multi_substring_all` | `multi_substring_all_check` | ALL of N substrings present |
| `substring_pair` | `substring_pair_check` | Any of group A AND any of group B |
| `terminated_command_pair` | `terminated_command_pair_check` | Command with boundary + any of group B |

Rules that can't be modeled with these families get conservative proofs.

---

## Proof Conventions

1. **Zero admits**: Never use `Admitted`. Use `sorry` only during development
   (CI will block it).
2. **No axioms**: No `Axiom` or `Parameter` declarations. Use `@proof-debt`
   tags if absolutely necessary (currently 0/10 budget used).
3. **Naming**: `rule_id_chk` for check functions, `rule_id_sound` for theorems.
4. **Generated proofs**: Don't edit files in `proofs/generated/` — they're
   overwritten by `gen_coq_proofs.py`.
5. **Archive**: Superseded proofs go in `proofs/archive/` with `.v.disabled`.

---

## CI Gate

The `proof.yml` workflow:

1. Compiles all proofs with `dune build proofs -j 4`
2. Greps for `Admitted.` and `admit.` — exit 1 if found
3. Greps for `Axiom` and `Parameter` — exit 1 if found
4. Reports timing and theorem count

Runs on every push and PR. Cannot be bypassed.

---

## Current State (v26.1)

- **1,182 theorems/lemmas** across 142 files
- **622 faithful proofs** (VPD-pattern match, exact Coq model)
- **20 conservative proofs** (L3 file-based rules — external binary checks, no Coq string model possible)
- **3 conditional proofs** (LAY-025/026/027 — sound given compile-log predicate)
- **0 admits, 0 axioms**
- **ML proof**: `v2_span_extractor_sound` — ByteClassifier meets 0.94 F1 gate (measured 0.9799)
- **v26.1 substrate**: LanguageContract, ValidatorGraphProofs (strengthened), ExecutionClasses, RepairMonotonicity, StableNodeIds (+31 new core theorems)
