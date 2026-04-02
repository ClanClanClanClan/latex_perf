# ML Span Extractor — Results

## CPU Baseline Models (April 2026)

Data pipeline validated end-to-end on CPU:
- **261 labeled documents** from golden corpus (pilot_v1 + locale + l2 batches)
- **18,122 training samples** (3.1% positive), **5,083 dev samples** (8.5% positive)
- Feature extraction: character class, token kind, in_math, line features, position

### Logistic Regression Baseline

| Metric | Value |
|--------|-------|
| Span-level F1 | 0.00 |
| Token predictions | 1,202 / 5,083 positive (23.6%) |
| Config | C=1.0, max_iter=1000, solver=lbfgs |

### Gradient Boosted Trees Baseline

| Metric | Value |
|--------|-------|
| Span-level F1 | 0.00 |
| Token predictions | 321 / 5,083 positive (6.3%) |
| Config | n_estimators=200, max_depth=6, lr=0.1 |
| Top features | line_length (0.35), pos_in_line (0.23), char_ord (0.17) |

### Analysis

Both baselines produce per-token predictions but fail span-level evaluation (seqeval
requires exact BIO boundary matching). This confirms the v1 architecture finding:
character-level classifiers cannot reconstruct exact span boundaries.

The v2 candidate classification pipeline (byte-level CNN+BiLSTM on 128-byte windows)
addresses this by operating on pre-extracted candidate anchors rather than raw BIO
tagging. Training the v2 model requires GPU (A100, blocked).

### Pipeline Status

| Stage | Status | Output |
|-------|--------|--------|
| Label spans | OK | ml/data/labeled_spans.jsonl (261 docs) |
| Feature extraction | OK | ml/data/features.jsonl (21,860 chars) |
| Train/dev split | OK | 210 train / 83 dev (80/20 stratified) |
| Logistic regression | OK | ml/eval_logreg.json |
| Gradient boosting | OK | ml/eval_gbt.json |
| Byte classifier (v2) | Blocked | Needs A100 GPU |

### v1 History (Retired)

| Iteration | Architecture | F1 |
|-----------|-------------|-----|
| v1.0 | SciBERT + CRF (multi-head) | 0.13 (collapsed) |
| v1.1 | SciBERT + single head | 0.70 |
| v1.2 | SciBERT + multi-head + B→I fix | 0.82 |
| v1.3 | v1.2 + 50 epochs | 0.8503 (ceiling) |

Expert diagnosis: WordPiece tokenization is lossy for character-level patterns,
labels depend on state outside 300-char window, dense BIO tagging is harder
than necessary. v2 pipeline designed to address all three.
