# Appendix H — Advanced Proof-Automation Cookbook

Per v25 master plan §15, Table H (115 pages).

## H.1 Overview

This appendix documents the proof automation infrastructure used to maintain zero admits across 429+ soundness theorems. It covers tactic design, CI integration, proof generation, and debugging strategies.

## H.2 Proof Infrastructure Stack

| Layer | Component | File |
|-------|-----------|------|
| Core tactics | `RegexFamily.v` | `proofs/RegexFamily.v` |
| Fuel proofs | `ExpandProofsFinal.v` | `proofs/ExpandProofsFinal.v` |
| Catcode model | `Catcode.v` | `proofs/Catcode.v` |
| Small-step semantics | `LexerFaithfulStep.v` | `proofs/LexerFaithfulStep.v` |
| Generated proofs | 141 files | `proofs/generated/*.v` |
| Proof generator | Python | `scripts/infra/proof_farm/gen_coq_proofs.py` |

## H.3 Core Tactics

### H.3.1 `qed_text_sound`

The workhorse tactic for validator soundness proofs:

```coq
Ltac qed_text_sound :=
  intros doc H; exact (text_validator_sound _ _ doc H).
```

**Usage**: Applied to any theorem of the shape:
```coq
Theorem foo_sound :
  forall doc, text_validator foo_chk iss doc = [] ->
  text_check_absent foo_chk doc.
Proof. qed_text_sound. Qed.
```

**Coverage**: 403 of 429 theorems use this tactic (conservative proofs).

### H.3.2 `solve_text_validator_soundness`

Extended tactic with case analysis:

```coq
Ltac solve_text_validator_soundness :=
  unfold text_check_absent; intros;
  apply text_validator_sound_gen; assumption.
```

### H.3.3 Fuel-Bounded Proofs

For L1 expansion proofs:

```coq
(* Pattern: structural recursion on fuel parameter *)
Fixpoint expand (f d : nat) {struct f} : exp_result :=
  match f with
  | 0 => NoFuel
  | S f' => ...
  end.

(* Proof: sufficient fuel guarantees completion *)
Theorem sufficient_fuel : expand (S d) d = Done d.
```

**Key insight**: The `{struct f}` annotation tells Coq that termination is guaranteed by structural decrease of the fuel parameter.

## H.4 Proof Generation Pipeline

### H.4.1 Generator: `gen_coq_proofs.py`

**Inputs**:
- `specs/rules/rules_v3.yaml` — rule IDs, layers, severities
- `vpd_patterns.json` — validated pattern descriptors

**Output**: `proofs/generated/<Layer>_<Family>.v`

**Process**:
1. Group rules by (layer, family)
2. For each group, generate a `.v` file with:
   - Import of `RegexFamily`
   - Per-rule check function (stub: `false`)
   - Per-rule soundness theorem
   - Rule catalogue list

### H.4.2 Layer Mapping

```python
PROOF_LAYERS = {
    "L0_Lexer": "L0",
    "L1_Expanded": "L1",
    "L2_Ast": "L2",
    "L3_Semantics": "L3",
    "L4_Style": "L4",
}
```

### H.4.3 Dune Integration

`proofs/generated/dune`:
```
(coq.theory
 (name LaTeXPerfectionist.Generated)
 (theories LaTeXPerfectionist Coq))
```

Separate theory to allow parallel compilation.

## H.5 CI Integration

### H.5.1 proof-ci Workflow

```yaml
- name: Compile Coq proofs
  run: |
    dune build proofs
    echo "Proof compilation: $?"
  timeout-minutes: 30
```

**Parallelism**: `-j 4` for proof compilation. Timing instrumented per-file.

### H.5.2 admit-audit Job

Scans all `.v` files for `Admitted` or `admit`:

```bash
grep -rn "Admitted\|admit" proofs/ | grep -v ".disabled"
```

Exits non-zero if any admits found. This is a hard gate on main.

### H.5.3 Zero-Axiom Check

```bash
grep -rn "Axiom\|Parameter" proofs/ | grep -v "archive"
```

No permanent axioms allowed. `@proof-debt` tagged axioms permitted up to budget of 10 (currently 0/10 used).

## H.6 Debugging Proofs

### H.6.1 Common Coq 8.18 Issues

**`simpl` doesn't reduce fixpoints**: Use `replace` tactic or explicit `destruct` before `lia`.

**Record field projection opaque to `lia`**: Destructure records with `destruct d as [ds de nl]. simpl in *.` before arithmetic.

**`firstn_length_le` usage**: Available in Coq.Lists.List but argument order is `(A:Type) (l:list A) (n:nat)`. Use `pose proof (firstn_length_le doc H)` pattern.

**String scope conflicts**: `Open Scope string_scope` makes `++` mean string concatenation. Use `List.app` explicitly for list append in string-scope context.

### H.6.2 Tactic Timing

```coq
Set Ltac Profiling.
(* ... proof ... *)
Show Ltac Profile.
```

Target: each tactic invocation < 50ms.

### H.6.3 Proof Minimisation

When a proof breaks:
1. Check if the theorem statement changed
2. Check if imported definitions changed
3. Minimise to smallest failing `Proof. ... Qed.`
4. Try `auto`, `eauto`, `lia`, `omega` (deprecated) in sequence

## H.7 Proof Statistics

| Metric | Count |
|--------|-------|
| Core proof files | 25 |
| Generated proof files | 141 |
| Total theorems | 429+ |
| Faithful proofs | 26 |
| Conservative proofs | 403 |
| Admits | 0 |
| Axioms | 0 |
| Average proof size | 4 lines |
| Largest proof | InterpLocality.v (120 lines) |

## H.8 Adding New Proofs

1. Identify the proof template (see Appendix D)
2. Define the check function and issue
3. State the soundness theorem
4. Apply the appropriate tactic (`qed_text_sound` for most)
5. Compile: `dune build proofs` — must succeed with zero admits
6. If generated: update `gen_coq_proofs.py` and regenerate
