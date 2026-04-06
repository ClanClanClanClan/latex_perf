# ML Span Extractor + Validation Metrics — Results

## Validation Baselines (April 2026)

### L2 Parser Corpus Pass Rate

| Metric | Value |
|--------|-------|
| Total corpus files | 306 |
| Parse success | 306 / 306 (100.0%) |
| Target (spec W43-45) | ≥ 90% |
| Status | **EXCEEDS** |

Measured across all golden corpus directories (lint/style, locale, phase3,
i18n_qa, pilot_v1, l2_approx, l2_batch3, l2_batch4, l3_text_approx,
l5_expl3_tikz, stragglers2, perf).

### False Positive Rate (FPR)

| Metric | Value |
|--------|-------|
| Clean corpus | corpora/perf/ (4 files) |
| Target (spec §1.2) | ≤ 0.1% |
| Status | **Pending full measurement** |

FPR measurement script: `scripts/measure_fpr.sh`. Requires a larger clean
corpus for statistically meaningful FPR — the 4 perf files are insufficient.
External corpora (corpora.lock) needed for proper FPR baseline.

### Sentence Splitter Throughput (W68-70)

| Metric | Value |
|--------|-------|
| Target (spec W68-70) | ≥ 50 MiB/s |
| Measured throughput | **141.5 MiB/s** |
| Test document | 1.46 MB × 100 iterations |
| Status | **PASS** (2.8× target) |

Measured via `test_throughput.ml` on M2-Pro. Sentence splitting uses single-pass
buffer scan with ". "+uppercase heuristic. O(n), no allocations in inner loop.

### Lock-Free Queue Throughput (W63)

| Metric | Value |
|--------|-------|
| Target (spec W63) | ≥ 8M events/sec |
| Single-thread | **22.1M events/sec** |
| Multi-domain (2P+1C) | **4.7M events/sec** |
| Status | **PASS** (single-thread exceeds 8M; multi-domain limited by CAS contention) |

Measured via `test_throughput.ml` on M2-Pro. MPMC ring buffer using OCaml 5.x
Atomic compare-and-swap. Power-of-two capacity with sequence numbers for ABA
protection.

### xxHash Scalar Throughput (W9)

| Metric | Value |
|--------|-------|
| Scalar baseline | ~2-4 GB/s (OCaml xxh64.ml) |
| SIMD target (spec W9) | ≥ 20 GB/s |
| SIMD C code | 447 lines (simd_tokenizer.c), AVX2+NEON |
| SIMD FFI path | xxh64_simd via L0_USE_SIMD_XXH=1 |
| Status | **Scalar measured; SIMD requires AVX2/NEON hardware** |

Benchmark: `make hash-bench` → `latex-parse/bench/hash_throughput.ml`.
The scalar OCaml path is the proven-correct reference. SIMD acceleration
is opt-in and requires native compilation on x86_64 (AVX2) or aarch64 (NEON).

### Catcode Scanner Throughput (W20)

| Metric | Value |
|--------|-------|
| Scalar baseline | Measured in catcode.ml match statement |
| SIMD target (spec W20) | ≥ 6× scalar |
| SIMD C code | 1,624 lines across 6 files in core/l0_lexer/simd/ |
| Status | **Scalar proven correct (Catcode.v); SIMD C code exists, ratio pending measurement** |

Benchmark: `scripts/bench_catcode.sh`. The SIMD C implementation uses vpshufb
(AVX2) / vtbl (NEON) for parallel 16-entry LUT lookup. Catcode correctness
(all 16 codes) verified against Catcode.v bijection proof.

### Validator DAG Integrity

| Metric | Value |
|--------|-------|
| Total unique rules | 606 |
| DAG cycles | 0 |
| Conflicts | 0 |
| Status | **PASS** |

DAG validated at startup via `Validator_dag.build_dag` in `get_rules()`.

---

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
