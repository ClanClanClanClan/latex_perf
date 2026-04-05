# Appendix D — Proof Template Catalogue (v25)

Per v25 master plan §15, Table D (22 pages).

**Status**: Authoritative for v25.
**Scope**: Generic, reusable Coq proof templates and instantiation guidance covering the validator families and phases defined in `rules_v3.yaml` (623 rules across TYPO/SPC/ENC/... families).

## D.1 Goals and Non-goals

**Goals**:
- Provide template-level proof obligations for each validator family
- Guarantee determinism, totality, no-panic properties
- Prove semantic preservation for normalisation fixes
- Enable auto-generation of per-rule soundness theorems

**Non-goals**:
- Proving full semantic equivalence with TeX engine output
- Verifying package-specific behaviour
- Runtime performance proofs (handled by measurement, not formal proof)

## D.2 Notation and Conventions

| Symbol | Meaning |
|--------|---------|
| `doc` | Input document (`document_state` in Coq) |
| `run r x` | Rule evaluation: apply rule `r` to input `x` |
| `wf_Lk(x)` | Well-formedness predicate for layer `k` |
| `TText s` | A text token containing string `s` |
| `TCommand s` | A command token `\s` |
| `mk_iss id msg sev fix` | Construct a validation issue |

## D.3 Core Infrastructure: RegexFamily.v

**File**: `proofs/RegexFamily.v` (292 lines)

The foundation of all validator proofs. Defines:

### D.3.1 Token Types
```coq
Inductive latex_token :=
  | TText : string -> latex_token
  | TCommand : string -> latex_token
  | TGroup : list latex_token -> latex_token
  | TMath : string -> latex_token
  | TNewline : latex_token
  | TComment : string -> latex_token
  | TWhitespace : latex_token.
```

### D.3.2 Generic Validator Shape
```coq
Definition text_validator
    (check : string -> bool)
    (iss : validation_issue)
    (doc : document_state)
    : list validation_issue :=
  flat_map (fun tok => match tok with
    | TText s => if check s then [iss] else []
    | _ => []
    end) (tokens doc).
```

### D.3.3 Soundness Theorem
```coq
Theorem text_validator_sound :
  forall check iss doc,
    text_validator check iss doc = [] ->
    text_check_absent check doc.
```

### D.3.4 Automation Tactic
```coq
Ltac solve_text_validator_soundness :=
  unfold text_check_absent; intros;
  apply text_validator_sound_gen; assumption.

Ltac qed_text_sound :=
  intros doc H; exact (text_validator_sound _ _ doc H).
```

## D.4 Template Catalogue

### Template 1: Text-Scan Validator
**Applies to**: TYPO, SPC, ENC families (L0 layer)
**Pattern**: Check if a string predicate holds on any text token
**Proof obligation**: `check s = true → issue emitted`
**Tactic**: `qed_text_sound`

### Template 2: Fuel-Bounded Expansion
**Applies to**: L1 macro expansion
**File**: `proofs/ExpandProofsFinal.v`
**Pattern**: Recursive expansion with fuel parameter
**Proof obligation**: `expand (S d) d = Done d` (sufficient fuel)

### Template 3: Parser Soundness
**Applies to**: L2 parser
**File**: `proofs/ParserSound.v`
**Pattern**: Parse produces valid AST; flatten preserves word order
**Proof obligations**:
- `flat_map flatten (map NWord tokens) = tokens` (identity parse)
- `well_formed n = true → n ≠ NError msg` (no errors in well-formed AST)

### Template 4: Label Uniqueness
**Applies to**: REF family (L3 semantics)
**File**: `proofs/LabelsUnique.v`
**Pattern**: Duplicate label detection
**Proof obligation**: Detected duplicates are actual duplicates

### Template 5: Diff Algebra
**Applies to**: Incremental re-parse
**File**: `proofs/InterpLocality.v`
**Pattern**: Independent diffs compose; empty diff is identity
**Proof obligations**:
- `independent r1 r2 = independent r2 r1` (symmetry)
- `apply_diff doc (mk_diff pos pos 0) [] = doc` (identity)
- Length preservation for insert/delete/replace

### Template 6: DAG Acyclicity
**Applies to**: Validator dependency graph
**File**: `proofs/ValidatorGraphProofs.v`
**Pattern**: Topological sort produces valid ordering
**Proof obligation**: No cycles in dependency graph

### Template 7: Snapshot Consistency
**Applies to**: Cross-layer synchronisation
**File**: `proofs/SnapshotConsistency.v`
**Pattern**: Version vectors ensure consistent reads
**Proof obligation**: Validators see either old or new snapshot, never interleaved

### Template 8: Section Renumbering
**Applies to**: Document structure
**File**: `proofs/SectionRebalance.v`
**Pattern**: Renumbering preserves tree shape
**Proof obligations**:
- `tree_level (renumber t n) = tree_level t`
- `length (renumber_forest ts n) = length ts`

### Template 9: Split Order Preservation
**Applies to**: Unicode text segmentation
**File**: `proofs/SplitPreservesOrder.v`
**Pattern**: Concatenating split segments preserves content
**Proof obligation**: Sorted segments have strictly increasing start positions

### Template 10: Catcode Totality
**Applies to**: L0 lexer
**File**: `proofs/Catcode.v`
**Pattern**: Every byte maps to exactly one catcode
**Proof obligations**:
- `nat_catcode_inverse` — round-trip bijection
- `catcode_eq_dec` — decidable equality
- `classify_ascii` — total function

## D.5 Generated Proof Pattern

The proof generator (`scripts/infra/proof_farm/gen_coq_proofs.py`) produces per-rule `.v` files in `proofs/generated/` using Template 1:

```coq
From LaTeXPerfectionist Require Import RegexFamily.

Definition <rule_id>_chk (s : string) : bool := false.

Theorem <rule_id>_sound :
  forall doc, text_validator <rule_id>_chk
    (mk_iss "<RULE-ID>" "<message>" <severity> None) doc = [] ->
  text_check_absent <rule_id>_chk doc.
Proof. qed_text_sound. Qed.
```

**Current coverage**: 429 per-rule soundness theorems across 141 generated files.

## D.6 Adding New Proof Templates

1. Define the validator shape as a Coq `Definition`
2. State the soundness theorem as `validator ... doc = [] → property doc`
3. Prove using structural induction or automation tactics
4. Register in `gen_coq_proofs.py` for auto-generation
5. Verify: `dune build proofs` — zero admits
