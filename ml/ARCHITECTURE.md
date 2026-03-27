# ML Span Extractor Architecture (v2 — Candidate Classification)

> **Status**: Design approved, implementation pending.
> **Previous**: v1 (BERT multi-head BIO tagger) archived at F1=0.8503.
> **Date**: 2026-03-22

---

## 1. Overview

The ML span extractor identifies character-level rule violations in LaTeX source text. Its predictions provide an empirical bound imported into a Coq soundness proof (`proofs/ML/SpanExtractorSound.v`).

### v1 (Retired): End-to-End BIO Tagger

SciBERT multi-head model performing dense BIO sequence labeling over 300-char windows. Reached **F1=0.8503** after 4 iterations. Diagnosed as a problem-formulation ceiling by external expert review.

### v2 (Current): Candidate Classification Pipeline

Hybrid architecture: **deterministic candidate extraction** + **byte-level ML disambiguation** + **deterministic verification**. Separates trivial anchor-finding from hard context disambiguation.

---

## 2. Architecture Comparison

| Property | v1 (BIO Tagger) | v2 (Candidate Classifier) |
|----------|-----------------|---------------------------|
| Input scope | 300-char window | Full document |
| Tokenizer | WordPiece (lossy) | Raw bytes (lossless) |
| Task framing | Tag every token O/B/I | Binary classify each candidate |
| Class balance | 99.5% O (extreme imbalance) | ~50/50 (balanced by design) |
| Span boundaries | Predicted (error-prone) | Deterministic (exact) |
| Math-awareness | None (implicit) | Explicit features |
| Model size | 110M params (SciBERT) | ~2M params (CNN+BiLSTM) |
| Eval split | 1 dev split (overfit risk) | Frozen test split |
| Coq metric | 1 - F1 (unsound) | Separate precision + recall |

---

## 3. Rule Triage

### 3.1 Deterministic Rules (No ML Needed)

These rules have unambiguous character-level patterns. The existing Python replay functions in `label_spans.py` produce exact matches (F1=1.0 by construction).

| Rule | Pattern | Replay function | Gold spans (dev) |
|------|---------|-----------------|------------------|
| TYPO-002 | `--` | `replay_count_substring` | 1,001 |
| TYPO-003 | `---` | `replay_count_substring` | 179 |
| TYPO-004 | ` `` ` and `''` | `replay_multi_substring` | 518 |
| TYPO-013 | Single `` ` `` (not double) | `replay_custom_TYPO_013` | 86 |
| TYPO-030 | `----` (4+ hyphens) | `replay_count_substring` | 4,029 |
| TYPO-043 | Smart quotes in verbatim | `replay_multi_substring` | 100 |
| TYPO-047 | `\section*` | `replay_count_substring` | 34 |
| TYPO-061 | Unicode `x` in text | `replay_count_substring_strip_math` | 2 |
| **Total** | | | **5,949** (47%) |

**Rationale**: These patterns are context-free. A `--` is always a TYPO-002 violation regardless of surrounding context, math mode, or environment. The replay function is the ground truth by definition.

### 3.2 Ambiguous Rules (Need ML Disambiguator)

These rules have anchors that can be found deterministically, but the **violation status depends on context** (math/text mode, environment, preceding commands).

| Rule | Anchor | Why ambiguous | Gold spans (dev) |
|------|--------|---------------|------------------|
| TYPO-062 | `\\` | `\\` as line break (OK) vs literal backslash (violation). Depends on what follows (`[`, `*`, command name) and environment (tabular, align). | 3,580 |
| TYPO-028 | `$$` | Opening vs closing `$$`. Depends on math-mode nesting state. | 1,394 |
| TYPO-052 | `<` or `>` | Text-mode (violation) vs math-mode (OK). Requires parser state. | 864 |
| TYPO-005 | `...` | Text-mode (violation, use `\dots`) vs math-mode (OK). | 364 |
| TYPO-001 | `"` | Text-mode (violation, use curly) vs math/verbatim (OK). | 427 |
| TYPO-012 | `[0-9]'` | Digit+apostrophe: prime mark vs possessive. Context-dependent. | 92 |
| TYPO-048 | `\u2013` | Text-mode en-dash (violation) vs math context (OK). | 38 |
| TYPO-056 | `\'{e}` etc. | TeX accent macro: requires regex match in non-math context. | 36 |
| **Total** | | | **6,795** (53%) |

**Key insight**: For these rules, **candidate extraction is trivial** (find the anchor substring). The hard part is **disambiguation** — determining whether the context makes it a real violation.

---

## 4. Data Pipeline

### 4.1 Candidate Extraction

**File**: `ml/data/candidate_extractor.py`

For each rule and document, run the replay function to find all candidate anchor positions. Each candidate is a `(rule_id, start, end)` tuple with exact byte offsets.

**Critical property**: Candidate extraction must have **recall=1.0** — every gold span must have a corresponding candidate. This is guaranteed because the replay functions are the same ones that generate the gold labels.

### 4.2 Parser State Computation

**File**: `ml/data/parser_state.py`

Compute per-character annotations for the full document:

| Feature | Type | Source |
|---------|------|--------|
| `in_math` | bool | `find_math_segments()` from `label_spans.py` |
| `in_verbatim` | bool | `\begin{verbatim}...\end{verbatim}`, `\verb\|...\|` |
| `in_comment` | bool | `%` to end-of-line |
| `env_depth` | int | `\begin{...}` / `\end{...}` nesting depth |
| `after_command` | bool | Position follows a `\commandname` |

The `in_math` implementation reuses the existing `find_math_segments()` which handles `$...$`, `$$...$$`, `\(...\)`, `\[...\]`. Extended for `\begin{equation}`, `\begin{align}`, etc.

### 4.3 Context Window Construction

For each candidate, extract a **128-byte context window** centered on the anchor:

```
context_start = max(0, anchor_start - 64)
context_end = min(len(text), anchor_end + 64)
```

The anchor position within the window is recorded as `(anchor_start - context_start, anchor_end - context_start)`.

### 4.4 Label Assignment

- **Positive** (label=1): Candidate whose `(rule_id, start, end)` appears in the gold span set
- **Negative** (label=0): Candidate found by replay but NOT in gold spans

For ambiguous rules, this naturally produces hard negatives — the same pattern in different contexts.

### 4.5 Data Split

| Split | Documents | Purpose | Usage |
|-------|-----------|---------|-------|
| Train | 70% (~876) | Model training | Updated each run |
| Dev | 15% (~188) | Hyperparameter tuning, threshold calibration | May be reused |
| Test | 15% (~187) | Final evaluation for Coq bound | **Frozen, never tuned against** |

The test split is used exactly once: after the pipeline is frozen, to produce the precision/recall numbers imported into the Coq proof.

---

## 5. Model Architecture

### 5.1 Byte-Level Candidate Classifier

**File**: `ml/models/byte_classifier.py`

```
Input: 128-byte context + rule_id + parser_state features

Byte Encoder:
  nn.Embedding(256, 64)              # 256 possible byte values
  -> 1D Conv(64, 128, kernel=3, dilation=1, padding=1) + ReLU + BatchNorm
  -> 1D Conv(128, 128, kernel=5, dilation=2, padding=4) + ReLU + BatchNorm
  -> 1D Conv(128, 128, kernel=7, dilation=4, padding=12) + ReLU + BatchNorm
  -> BiLSTM(input=128, hidden=128, layers=1)
  -> Anchor pooling: mean over anchor positions -> 256-dim vector

Rule Encoder:
  nn.Embedding(num_rules, 16)        # 8 ambiguous rules

Parser Features:
  [in_math, in_verbatim, after_command, env_depth] -> 4 floats

Classifier:
  Concatenate [byte_repr(256), rule_emb(16), parser_feats(4)] = 276-dim
  -> Linear(276, 128) + ReLU + Dropout(0.3)
  -> Linear(128, 1) + Sigmoid
  -> P(violation | candidate, rule, context)
```

### 5.2 Design Rationale

- **Byte embeddings**: Raw bytes preserve every character. No information loss from tokenization. `\`, `$`, `-`, `<`, `>`, `"` all have distinct embeddings.
- **Dilated CNN stack**: Captures patterns at multiple scales without parameter explosion:
  - Layer 1 (dilation=1): 3-char patterns (`$$`, `\\[`)
  - Layer 2 (dilation=2): 9-char effective receptive field (`\\begin{`)
  - Layer 3 (dilation=4): 27-char effective receptive field (environment context)
- **BiLSTM**: Captures sequential dependencies (e.g., whether `$$` opened or closed math). Single layer is sufficient for 128-byte sequences.
- **Anchor pooling**: Instead of global pooling, mean-pool only over the anchor's byte positions. Focuses the classifier on the candidate region while still having context from CNN+LSTM.
- **Rule conditioning**: Shared backbone, rule-specific decision boundary via rule embedding. This is more parameter-efficient than separate models per rule.
- **Parser features**: Explicit in_math/in_verbatim state eliminates the primary source of ambiguity identified in the expert review.

### 5.3 Model Size

| Component | Parameters |
|-----------|-----------|
| Byte embedding | 256 * 64 = 16K |
| CNN layers (3) | ~200K |
| BiLSTM | ~400K |
| Rule embedding | 8 * 16 = 128 |
| MLP classifier | 276*128 + 128*1 = ~36K |
| **Total** | **~650K** |

Compare: SciBERT has 110M parameters. This model is **170x smaller**.

### 5.4 Training Configuration

| Parameter | Value |
|-----------|-------|
| Loss | Binary cross-entropy |
| Optimizer | Adam, lr=1e-3 |
| Scheduler | ReduceLROnPlateau (patience=5, factor=0.5) |
| Batch size | 256 |
| Max epochs | 50 |
| Early stopping patience | 10 |
| Dropout | 0.3 |
| Weight decay | 1e-5 |

No class weighting needed — candidates are approximately balanced by construction.

---

## 6. Inference Pipeline

### 6.1 Full Document Processing

```python
def predict_spans(text: str, model, vpd_patterns: dict, thresholds: dict) -> List[Span]:
    # Phase 1: Deterministic rules (F1=1.0)
    deterministic_spans = []
    for rule_id in DETERMINISTIC_RULES:
        raw_spans = replay_pattern(text, rule_id, vpd_patterns[rule_id])
        deterministic_spans.extend(Span(s, e, rule_id) for s, e in raw_spans)

    # Phase 2: Ambiguous rules (ML-assisted)
    parser_state = compute_parser_state(text)
    ml_spans = []
    for rule_id in AMBIGUOUS_RULES:
        candidates = extract_candidates(text, rule_id, vpd_patterns)
        if not candidates:
            continue
        contexts = build_context_windows(text, candidates, parser_state)
        probs = model.predict_batch(contexts)  # batched inference
        for cand, prob in zip(candidates, probs):
            if prob >= thresholds[rule_id]:
                ml_spans.append(Span(cand.start, cand.end, rule_id))

    return deterministic_spans + ml_spans
```

### 6.2 Per-Rule Thresholds

Thresholds are tuned on the **dev split** (not test) to optimize F1 per rule:

```python
thresholds = calibrate_thresholds(model, dev_candidates, dev_labels)
# e.g., {"TYPO-062": 0.45, "TYPO-028": 0.50, "TYPO-052": 0.40, ...}
```

### 6.3 Optional Deterministic Verification

For maximum soundness, pipe ML predictions through the OCaml engine for confirmation. This is optional because the candidate extractor already ensures boundary correctness — the ML model only decides yes/no.

---

## 7. Evaluation Protocol

### 7.1 Candidate-Level Metrics

Before span evaluation, verify candidate extraction quality:

| Metric | Target | Meaning |
|--------|--------|---------|
| Candidate recall | 1.000 | Every gold span has a candidate |
| Candidate count | ~ | Total candidates per rule |
| Positive rate | ~0.3–0.7 | Fraction of candidates that are violations |

### 7.2 Span-Level Metrics (Unchanged)

Same exact-match span evaluation as v1:
- TP = gold spans correctly predicted
- FP = predicted spans not in gold
- FN = gold spans not predicted
- Micro F1 = 2*TP / (2*TP + FP + FN)

### 7.3 Coq-Bound Metrics (New)

Separate precision and recall bounds, evaluated on the **frozen test split**:

| Metric | Definition | Coq import |
|--------|-----------|------------|
| Precision | TP / (TP + FP) | `measured_fp_rate = 1 - precision` |
| Recall | TP / (TP + FN) | `measured_fn_rate = 1 - recall` |

### 7.4 Split Discipline

- **Train**: Used for gradient updates only
- **Dev**: Used for early stopping, threshold tuning, hyperparameter search
- **Test**: Used **exactly once** after pipeline is frozen. Numbers go into Coq proof.

---

## 8. Coq Proof Design (v2)

### Current (v1, unsound)

```coq
Definition measured_delta : R := 0.028.  (* 1 - F1 *)
Definition f1_threshold : R := 0.94.
```

Problem: `1 - F1` conflates precision and recall errors into a single number that is neither a false-positive rate nor a false-negative rate.

### New (v2, sound)

```coq
(* Empirical bounds from frozen test split *)
Definition measured_fp_rate : R := ...    (* 1 - precision *)
Definition measured_fn_rate : R := ...    (* 1 - recall *)

(* Thresholds from project spec *)
Definition precision_threshold : R := 0.94.
Definition recall_threshold : R := 0.90.  (* can be lower than precision *)

(* Soundness: false-positive rate is bounded *)
Theorem span_extractor_sound :
  forall fp_rate : R,
    (fp_rate <= measured_fp_rate)%R ->
    (1 - fp_rate >= precision_threshold)%R.

(* Completeness: false-negative rate is bounded *)
Theorem span_extractor_complete :
  forall fn_rate : R,
    (fn_rate <= measured_fn_rate)%R ->
    (1 - fn_rate >= recall_threshold)%R.
```

This makes the formal guarantee meaningful: soundness bounds false positives, completeness bounds false negatives, each with its own threshold.

---

## 9. Diagnostic Experiment (Pre-Implementation)

Before building the full v2 pipeline, run one experiment to confirm the parser-state hypothesis on the existing v1 model:

1. Compute `in_math` and `in_verbatim` for each training window using the full document context
2. Append as 2 extra binary features to BERT's hidden states (e.g., concatenate to CLS, or add as special tokens)
3. Retrain multi-head model with these oracle features
4. Compare F1 to baseline (0.8503)

**Expected outcomes**:
- **F1 jumps to ~0.90+**: Parser state is the primary bottleneck. Validates v2 approach.
- **F1 stays ~0.85**: Tokenization is the primary bottleneck. Still validates v2 (byte model needed), but parser features alone are insufficient.
- **Either outcome**: Proceed with v2. The experiment just tells us which component matters most.

---

## 10. File Map

| File | Status | Purpose |
|------|--------|---------|
| `ml/ARCHITECTURE.md` | **This file** | Architecture documentation |
| `ml/results/expert_briefing.md` | Updated | Full problem statement + expert feedback |
| `ml/data/label_spans.py` | Existing | Replay functions (reused for candidate extraction) |
| `ml/data/candidate_extractor.py` | **To create** | Candidate extraction per rule |
| `ml/data/parser_state.py` | **To create** | Per-character math/verbatim annotations |
| `ml/data/build_candidate_dataset.py` | **To create** | Build candidate classification JSONL |
| `ml/models/byte_classifier.py` | **To create** | Byte-level CNN+BiLSTM classifier |
| `ml/models/bert_crf.py` | Existing | Legacy v1 model (kept for diagnostic) |
| `ml/evaluate.py` | **To modify** | Add candidate-level eval + separate precision/recall |
| `ml/notebooks/candidate_training.ipynb` | **To create** | Colab training notebook for v2 |
| `ml/config.yaml` | **To modify** | Add candidate classifier config |
| `proofs/ML/SpanExtractorSound.v` | **To modify** | Separate precision/recall bounds |

---

## 11. Migration Notes

### What's Preserved from v1
- Replay functions in `label_spans.py` (reused as candidate extractors)
- `find_math_segments()` / `strip_math_segments()` (reused for parser state)
- Span-level evaluation logic in `evaluate.py`
- Corpus and labeling pipeline

### What's Retired from v1
- SciBERT encoder and WordPiece tokenizer
- BIO tag scheme (replaced by binary classification)
- 300-char windowing with 150-char stride
- Multi-head fused classifier
- Focal loss / per-head class weights
- Subword-to-character projection logic

### What's New in v2
- Byte-level model (no tokenizer)
- Candidate extraction + binary classification framing
- Parser-state features (in_math, in_verbatim, in_comment, env_depth)
- Per-rule threshold tuning on dev split
- Frozen test split for Coq bound import
- Separate precision/recall bounds in Coq proof
