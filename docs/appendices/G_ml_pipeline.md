# Appendix G -- ML-Assisted Pattern Pipeline & Extended Glossary

Revision 2026-04-05. The ML pipeline provides an empirical bound for formally
verified pattern rules. It operates as a secondary validation layer: deterministic
rules handle 47% of spans with F1=1.0; the ML classifier handles the remaining
53% of ambiguous spans.

Design constraint: human-in-the-loop pipeline that *proposes* candidates; all
merges remain rule-/proof-driven. The ML path never bypasses the proof-first gate.

---

## G-1 Why ML Here?

Some typographic patterns are ambiguous at the character level:

- `$$` may be a display-math delimiter (correct) or a double-dollar error
  (TYPO-028) -- resolution depends on whether the cursor is inside math mode.
- `<>` may be an angle-bracket comparison (correct in math) or a misused
  HTML-style tag (TYPO-052) -- depends on surrounding context.
- Straight quotes (`"`) may be intentional in code/verbatim or an error in
  body text (TYPO-001) -- depends on environment nesting.

Deterministic regex cannot resolve these ambiguities without parser state. The
ML classifier receives explicit parser-state features to disambiguate.

---

## G-2 Architecture: v1 vs v2

### G-2.1 v1 (Retired): SciBERT Multi-Head BIO Tagger

- Architecture: SciBERT (110M params) + K=16 independent 3-class heads, fused
  `nn.Linear(768, K*3)`.
- Four iterations:
  1. CRF collapse: F1 = 0.13 (CRF killed gradient flow)
  2. Single-head: F1 = 0.70
  3. Multi-head + B->I fix: F1 = 0.82
  4. Longer training: F1 = 0.8503
- **Ceiling at F1 = 0.8503** -- diagnosed as problem-formulation ceiling.

### G-2.2 Expert Diagnosis (Three Root Causes)

1. **WordPiece tokenisation is lossy** for character-level patterns. Sequences
   like `\\`, `$$`, `----`, `<>` are split into meaningless subwords.
2. **Labels depend on state outside the 300-char window.** Math/text/verbatim
   mode may be established thousands of characters earlier.
3. **Dense BIO tagging is harder than necessary.** Forces the model to
   simultaneously discover anchors, classify context, and set boundaries.

### G-2.3 v2 (Current): Candidate Classification Pipeline

```
Source document
  |
  +-- Stage 1: Deterministic Rules (8 rules, F1=1.0)
  |     TYPO-002, 003, 004, 013, 030, 043, 047, 061
  |
  +-- Stage 2: Byte-level CNN+BiLSTM Classifier (8 rules)
        TYPO-001, 005, 012, 028, 048, 052, 056, 062
        |
        +-- 128-byte context + rule embedding + parser-state features
             -> MLP -> P(violation)
```

---

## G-3 Rule Partitions

### G-3.1 Deterministic Rules (Stage 1)

Handled by replay functions in `ml/data/candidate_extractor.py`. These rules
have unambiguous anchors that can be detected without ML:

```python
# ml/data/candidate_extractor.py
DETERMINISTIC_RULES: Set[str] = {
    "TYPO-002",   # Double spaces
    "TYPO-003",   # Trailing whitespace
    "TYPO-004",   # Tab characters
    "TYPO-013",   # Multiple blank lines
    "TYPO-030",   # Consecutive hyphens (not em-dash)
    "TYPO-043",   # Ellipsis as three dots
    "TYPO-047",   # Space before comma/period
    "TYPO-061",   # Non-breaking space misuse
}
```

F1 = 1.0 by construction (deterministic pattern matching).
47% of all spans in the training corpus.

### G-3.2 Ambiguous Rules (Stage 2)

Require ML disambiguation due to context-dependent semantics:

```python
AMBIGUOUS_RULES: Set[str] = {
    "TYPO-001",   # Straight quotes (context: verbatim vs body)
    "TYPO-005",   # Hyphen vs en-dash (context: number range vs word)
    "TYPO-012",   # Prime symbol (context: math vs text)
    "TYPO-028",   # Double dollar sign (context: math mode state)
    "TYPO-048",   # Backtick quotes (context: code vs text)
    "TYPO-052",   # Angle brackets (context: math vs HTML-like)
    "TYPO-056",   # Tilde usage (context: macro vs text)
    "TYPO-062",   # Double backslash (context: line break vs escape)
}
```

53% of all spans in the training corpus.

---

## G-4 Data Pipeline

### G-4.1 Candidate Extraction (`ml/data/candidate_extractor.py`)

For each of the 16 v2 rules, extracts candidate positions from source documents
by reusing the deterministic `replay_pattern()` function.

```python
@dataclass(frozen=True)
class Candidate:
    """A candidate violation site in a document."""
    rule_id: str
    start: int         # byte offset, inclusive
    end: int           # byte offset, exclusive
    is_positive: bool = False  # True if gold-annotated as violation
```

Each candidate represents a potential violation site. Labelling against gold
spans determines true positives.

### G-4.2 Parser State Features (`ml/data/parser_state.py`)

Computes per-character state annotations as oracle features:

```python
@dataclass
class ParserState:
    """Per-character parser-state annotations."""
    in_math: List[bool]       # Inside $...$, \[...\], equation, etc.
    in_verbatim: List[bool]   # Inside verbatim/lstlisting/minted
    in_comment: List[bool]    # After % to end-of-line (not \%)
    env_depth: List[int]      # \begin{...}/\end{...} nesting depth
```

Math environment coverage:

```python
_MATH_ENV_NAMES = [
    'equation', r'equation\*', 'align', r'align\*',
    'gather', r'gather\*', 'multline', r'multline\*',
    'flalign', r'flalign\*', 'alignat', r'alignat\*',
    'eqnarray', r'eqnarray\*', 'math', 'displaymath', 'split',
]
```

### G-4.3 Dataset Construction (`ml/data/build_candidate_dataset.py`)

Produces JSONL files with 128-byte context windows:

```json
{
  "rule_id": "TYPO-028",
  "context_bytes": [92, 91, 36, 36, ...],
  "anchor_start": 52,
  "anchor_end": 54,
  "label": 1,
  "in_math": true,
  "in_verbatim": false,
  "in_comment": false,
  "env_depth": 2
}
```

Context window is centred on the anchor pattern. Padding with zero bytes if the
anchor is near a document boundary.

### G-4.4 Data Split (`ml/data/split_data.py`)

Stratified three-way split preserving rule-ID distribution:

| Split | Proportion | Purpose |
|-------|-----------|---------|
| Train | 70% | Model training |
| Dev | 15% | Hyperparameter tuning |
| Test | 15% | **Frozen** -- never used for tuning or development |

The frozen test split is critical for the Coq proof integration (see G-7).

---

## G-5 Model Architecture (`ml/models/byte_classifier.py`)

### G-5.1 Architecture Diagram

```
Input: 128 bytes (uint8)  -->  Embedding(256, 64)
                          -->  Conv1d(kernel=3, dilation=1, channels=128)
                          -->  BatchNorm1d + ReLU
                          -->  Conv1d(kernel=5, dilation=2, channels=128)
                          -->  BatchNorm1d + ReLU
                          -->  Conv1d(kernel=7, dilation=4, channels=128)
                          -->  BatchNorm1d + ReLU
                          -->  BiLSTM(input=128, hidden=128, layers=1)
                          -->  Anchor-pooled (mean over [start, end))
                          -->  256-dim vector

rule_id (int)             -->  Embedding(8, 16)  -->  16-dim

parser_features (4 floats) -->  [in_math, in_verbatim, in_comment, env_depth]

                          Concat: 256 + 16 + 4 = 276-dim
                          -->  Linear(276, 128) + ReLU + Dropout(0.3)
                          -->  Linear(128, 1)
                          -->  Sigmoid --> P(violation)
```

### G-5.2 Key Implementation Details

```python
class ByteClassifier(nn.Module):
    def __init__(self, num_rules=8, context_size=128,
                 byte_embed_dim=64, cnn_channels=128,
                 lstm_hidden=128, rule_embed_dim=16,
                 parser_feat_dim=4, mlp_hidden=128, dropout=0.3):
        # Byte encoder
        self.byte_embed = nn.Embedding(256, byte_embed_dim)
        # Dilated CNN stack (increasing receptive field)
        self.conv1 = nn.Conv1d(byte_embed_dim, cnn_channels,
                               kernel_size=3, dilation=1, padding=1)
        self.conv2 = nn.Conv1d(cnn_channels, cnn_channels,
                               kernel_size=5, dilation=2, padding=4)
        self.conv3 = nn.Conv1d(cnn_channels, cnn_channels,
                               kernel_size=7, dilation=4, padding=12)
        # BiLSTM
        self.bilstm = nn.LSTM(cnn_channels, lstm_hidden,
                              bidirectional=True, batch_first=True)
        # Rule encoder
        self.rule_embed = nn.Embedding(num_rules, rule_embed_dim)
        # Classifier MLP
        classifier_in = 2 * lstm_hidden + rule_embed_dim + parser_feat_dim
        self.fc1 = nn.Linear(classifier_in, mlp_hidden)
        self.fc2 = nn.Linear(mlp_hidden, 1)
```

### G-5.3 Anchor Pooling

The BiLSTM output is mean-pooled over the anchor span `[start, end)` for each
batch item:

```python
for i in range(batch_size):
    s = anchor_start[i].item()
    e = anchor_end[i].item()
    if e <= s:
        pooled[i] = x[i].mean(dim=0)  # degenerate: full-sequence mean
    else:
        pooled[i] = x[i, s:e].mean(dim=0)
```

### G-5.4 Parameter Count

Target budget: < 1M parameters.

```python
def count_parameters(model) -> int:
    return sum(p.numel() for p in model.parameters() if p.requires_grad)
```

Measured: ~538K--650K depending on hyperparameters (vs 110M for SciBERT v1).

---

## G-6 Training (`ml/models/train_byte_classifier.py`)

| Hyperparameter | Value |
|---------------|-------|
| Optimizer | Adam |
| Learning rate | 1e-3 |
| Mixed precision | AMP (automatic mixed precision) |
| Checkpointing | Every epoch |
| Early stopping | On dev F1 (patience TBD) |
| Batch size | TBD (depends on GPU memory) |
| Epochs | TBD |

Training infrastructure: blocked on A100 GPU access. Colab notebook cells 9--11
provide the full pipeline:
1. Build candidates from corpus
2. Train byte classifier
3. Per-rule breakdown (precision, recall, F1)

---

## G-7 Identifiability Audit (`ml/scripts/identifiability_audit.py`)

Measures whether violations are structurally identifiable from 300-character
context windows (without parser-state features):

| Rule | % Not Identifiable | Root Cause |
|------|-------------------|------------|
| TYPO-028 (`$$`) | 47% | Math state established outside window |
| TYPO-052 (`<>`) | 43% | Math state established outside window |
| TYPO-056 (`~`) | ~20% | Active character context |
| TYPO-001 (`"`) | ~15% | Verbatim/code context |
| TYPO-062 (`\\`) | 0% | No math dependency |
| TYPO-012 (`5'`) | 0% | No math dependency |

**Overall:** 15% of spans are structurally unidentifiable from 300-char windows.

**Conclusion:** Parser-state features (`in_math`, `in_verbatim`) are essential
for TYPO-028 and TYPO-052. This validates the v2 architecture decision to
include explicit parser-state annotations rather than relying on implicit
context.

---

## G-8 Coq Proof Integration

### G-8.1 Old Proof (Unsound)

The v1 proof used a single delta bound: `delta = 1 - F1`. This conflates
false-positive rate and false-negative rate, which is unsound -- a model with
high precision but low recall would have the same delta as one with low
precision but high recall.

### G-8.2 New Proof (Sound)

File: `proofs/ML/SpanExtractorSound.v`

Separate bounds for false-positive and false-negative rates:

```
measured_fp_rate = 1 - precision     (fraction of flagged items that are wrong)
measured_fn_rate = 1 - recall        (fraction of true violations missed)
```

### G-8.3 Formal Bound

The ML classifier provides an empirical bound:
- If measured precision >= P on frozen test set, then `fp_rate <= 1 - P`
- If measured recall >= R on frozen test set, then `fn_rate <= 1 - R`

Target: F1 >= 0.94 implies fp_rate <= 0.06, fn_rate <= 0.06.

Key requirement: evaluation must use the **frozen test split** (never reused
for dev or training).

---

## G-9 Data Sources

### G-9.1 Training Corpus

- **Curated papers:** Under `corpus/` (SHA-256 locked)
- **Synthetic suites:** Generated LaTeX fragments with known violations
- **Gold annotations:** YAML files enumerating expected issues per document

### G-9.2 Feature Extraction

| Feature class | Source | Dimension |
|--------------|--------|-----------|
| Raw bytes | 128-byte context window | 128 |
| Byte embeddings | Learned | 64 per byte |
| Rule ID | One-hot -> embedding | 16 |
| Parser state | `parser_state.py` | 4 floats |

### G-9.3 Distant Supervision

Existing rule fires serve as weak labels. Near-miss mining uncovers new variants
(e.g., Unicode look-alikes). Negative sampling from clean regions of corpora.

---

## G-10 Risk, Fairness, and Privacy

### G-10.1 Fairness

- Non-English corpora drive candidate discovery proportionally.
- Per-language hold-out to detect drift.
- No language pack should have systematically lower recall than others.

### G-10.2 Privacy

- No user-private documents in training data.
- Only opt-in corpora.
- No telemetry of document content (only aggregate rule-fire statistics).

### G-10.3 Reproducibility

- Dataset fingerprints and exact training configs recorded.
- Builds are hermetic (seeded randomness, pinned library versions).
- All training artefacts stored with SBOM metadata.

---

## G-11 Test Coverage

80+ Python tests across 4 test files:

| Test file | Tests | Coverage |
|-----------|-------|----------|
| `test_candidate_extractor.py` | Anchor extraction correctness per rule | All 16 rules |
| `test_build_dataset.py` | JSONL format, feature correctness, window centering | All fields |
| `test_identifiability.py` | Per-rule identifiability rates | 8 ambiguous rules |
| `test_byte_classifier.py` | Model forward pass, loss computation, gradient flow | Architecture |

---

## G-12 Key Files

| File | Purpose |
|------|---------|
| `ml/data/candidate_extractor.py` | Deterministic anchor extraction for 16 rules |
| `ml/data/build_candidate_dataset.py` | 128-byte context windows + parser features to JSONL |
| `ml/data/parser_state.py` | Per-char in_math/in_verbatim/in_comment/env_depth |
| `ml/data/split_data.py` | Stratified 70/15/15 train/dev/test split |
| `ml/models/byte_classifier.py` | CNN+BiLSTM model (~538K--650K params) |
| `ml/models/train_byte_classifier.py` | Full training loop (Adam, AMP, checkpointing) |
| `ml/scripts/identifiability_audit.py` | Parser-state recovery measurement per window |
| `ml/ARCHITECTURE.md` | Full v2 technical documentation |
| `proofs/ML/SpanExtractorSound.v` | Formal bound on fp/fn rates |

---

## G-13 Roadmap

| Phase | Status | Description |
|-------|--------|-------------|
| v1 BERT tagger | Retired | Ceiling at F1=0.8503 |
| v2 candidate pipeline | Code complete | Data pipeline + model architecture |
| v2 training | Blocked | Requires A100 GPU access |
| v2 evaluation | Pending | Per-rule precision/recall on frozen test |
| Coq proof update | Pending | Update SpanExtractorSound.v with measured rates |
| v26 cross-language transfer | Future | Per-script adapters |
| v27 structure-aware models | Future | Complex math spacing (still proof-gated) |

---

## G-14 Extended Glossary

| Term | Definition |
|------|-----------|
| Anchor | The specific byte pattern that triggers a candidate (e.g., `$$`, `<>`) |
| BIO tagging | Begin/Inside/Outside labelling for span extraction |
| Candidate | A position in the source that might be a rule violation |
| Context window | Fixed-size byte region around a candidate (128 bytes in v2) |
| Deterministic rule | A rule whose violations can be identified without ML |
| Frozen test set | Evaluation data never used for training or tuning |
| Identifiability | Whether a violation can be determined from a fixed-size window |
| Parser-state feature | Per-character annotation (in_math, in_verbatim, etc.) |
| Replay function | Deterministic anchor extraction for a specific rule |
| VPD | Validated Pattern Descriptor -- regex proven in Coq |
| WordPiece | BERT's subword tokenisation (lossy for char-level patterns) |
| AMP | Automatic Mixed Precision -- half/full precision training |

---

End of Appendix G.
