# Appendix G — ML-Assisted Pattern Pipeline & Extended Glossary

Per v25 master plan §15, Table G (161 pages).

## G.1 Overview

The ML pipeline provides an empirical bound for formally verified pattern rules. It operates as a secondary validation layer: deterministic rules handle 47% of spans with F1=1.0; the ML classifier handles the remaining 53% of ambiguous spans.

## G.2 Architecture: v2 Candidate Classification Pipeline

### G.2.1 Design Rationale

**v1 (Retired)**: SciBERT multi-head BIO tagger. Ceiling at F1=0.8503 due to:
1. WordPiece tokenization lossy for character-level patterns
2. Labels depend on state outside 300-char window (math/text mode)
3. Dense BIO tagging harder than necessary

**v2 (Current)**: Two-stage pipeline:

```
Source document
  │
  ├─ Stage 1: Deterministic Rules (8 rules, F1=1.0)
  │    TYPO-002, 003, 004, 013, 030, 043, 047, 061
  │
  └─ Stage 2: Byte-level CNN+BiLSTM Classifier (8 rules)
       TYPO-001, 005, 012, 028, 048, 052, 056, 062
       │
       └─ 128-byte context + rule embedding + parser-state features
            → MLP → P(violation)
```

### G.2.2 Deterministic Rules (Stage 1)

Handled by replay functions in `ml/data/candidate_extractor.py`:
- Anchored pattern matching (regex or direct string search)
- Context-free: no model inference needed
- **47% of all spans** in the training corpus

### G.2.3 Ambiguous Rules (Stage 2)

Byte-level CNN+BiLSTM candidate classifier:
- **Input**: 128-byte context window + rule embedding + parser-state features
- **Parser-state features**: `in_math`, `in_verbatim`, `in_comment`, `env_depth`
- **Architecture**: ~538K parameters (vs 110M SciBERT)
- **Output**: P(violation) per candidate

## G.3 Data Pipeline

### G.3.1 Candidate Extraction (`ml/data/candidate_extractor.py`)

For each of 16 rules, extracts candidate positions from source documents:
- Deterministic anchor identification (e.g., `$$` for TYPO-028, `<>` for TYPO-052)
- 128-byte context window centred on anchor
- Positive/negative label from gold annotations

### G.3.2 Dataset Construction (`ml/data/build_candidate_dataset.py`)

Produces JSONL files with:
```json
{
  "rule_id": "TYPO-028",
  "context": "... 128 bytes ...",
  "label": 1,
  "in_math": true,
  "in_verbatim": false,
  "in_comment": false,
  "env_depth": 2
}
```

### G.3.3 Parser State (`ml/data/parser_state.py`)

Computes per-character state features:
- `in_math`: Inside `$...$`, `\[...\]`, or math environment
- `in_verbatim`: Inside verbatim/lstlisting/minted
- `in_comment`: After `%` to end of line
- `env_depth`: Nesting depth of `\begin{...}`

### G.3.4 Data Split (`ml/data/split_data.py`)

`stratified_three_way_split(70/15/15)`:
- **Train** (70%): Model training
- **Dev** (15%): Hyperparameter tuning
- **Test** (15%): **Frozen** — never used for tuning

## G.4 Model Architecture

### G.4.1 Byte Classifier (`ml/models/byte_classifier.py`)

```
Input: 128 bytes (uint8) + rule_id embedding + 4 parser-state features
  │
  ├─ Byte embedding (256 → 32 dim)
  ├─ 1D CNN (kernel=3, filters=64)
  ├─ BiLSTM (hidden=64, layers=1)
  ├─ Concat with rule embedding + parser features
  ├─ MLP (128 → 64 → 1)
  └─ Sigmoid → P(violation)
```

**Parameters**: ~538K (vs 110M SciBERT)

### G.4.2 Training Loop (`ml/models/train_byte_classifier.py`)

- Optimizer: Adam (lr=1e-3)
- AMP (automatic mixed precision) for GPU training
- Checkpointing every epoch
- Early stopping on dev F1

## G.5 Identifiability Audit

`ml/scripts/identifiability_audit.py` measures whether violations are identifiable from 300-char windows:

| Rule | Not Identifiable | Root Cause |
|------|-----------------|------------|
| TYPO-028 (`$$`) | 47% | Math state starts outside window |
| TYPO-052 (`<>`) | 43% | Same issue |
| TYPO-062 (`\\`) | 0% | No math dependency |
| TYPO-012 (`5'`) | 0% | No math dependency |

**Conclusion**: Parser-state features are essential for TYPO-028 and TYPO-052. This validates the v2 architecture decision.

## G.6 Coq Proof Integration

### G.6.1 Proof Refactor

**Old** (unsound): `delta = 1 - F1`
**New** (sound): Separate `measured_fp_rate` (1-precision) and `measured_fn_rate` (1-recall) bounds

File: `proofs/ML/SpanExtractorSound.v`

Evaluation on **frozen test split** (not reused dev split).

### G.6.2 Formal Bound

The ML classifier provides an empirical bound:
- If measured precision ≥ P on frozen test set, then `measured_fp_rate ≤ 1 - P`
- If measured recall ≥ R on frozen test set, then `measured_fn_rate ≤ 1 - R`
- Target: F1 ≥ 0.94 → fp_rate ≤ 0.06, fn_rate ≤ 0.06

## G.7 Training Infrastructure

**Blocked on**: A100 GPU access for BERT diagnostic + v2 byte classifier training.

**Colab notebook**: Cells 9-11 provide:
1. Build candidates from corpus
2. Train byte classifier
3. Per-rule breakdown (precision, recall, F1)

## G.8 Test Coverage

- 80+ Python tests across 4 test files
- `test_candidate_extractor.py` — anchor extraction correctness
- `test_build_dataset.py` — JSONL format, feature correctness
- `test_identifiability.py` — per-rule identifiability rates
- `test_byte_classifier.py` — model forward pass, loss computation

## G.9 Extended Glossary

| Term | Definition |
|------|------------|
| BIO tagging | Begin/Inside/Outside labelling for span extraction |
| Candidate | A position in the source that might be a rule violation |
| Context window | Fixed-size byte region around a candidate (128 bytes) |
| Deterministic rule | A rule whose violations can be identified without ML |
| Frozen test set | Evaluation data never used for training or tuning |
| Parser-state feature | Per-character annotation (in_math, in_verbatim, etc.) |
| Replay function | Deterministic anchor extraction for a specific rule |
| VPD | Validated Pattern Descriptor — regex proven in Coq |
| WordPiece | BERT's subword tokenisation (lossy for char-level patterns) |
