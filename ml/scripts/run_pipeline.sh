#!/usr/bin/env bash
# End-to-end ML span extractor pipeline.
# Usage: bash ml/scripts/run_pipeline.sh [--model logreg|gbt|bert-crf] [--device cpu|cuda]
set -euo pipefail

MODEL="${1:---model}"
MODEL_ARG="${2:-logreg}"
DEVICE="${3:-cpu}"
SEED=42

echo "=== ML Span Extractor Pipeline ==="
echo "Model: $MODEL_ARG"
echo "Device: $DEVICE"
echo "Seed: $SEED"
echo ""

# Parse args
if [[ "$MODEL" == "--model" ]]; then
    MODEL_NAME="$MODEL_ARG"
else
    MODEL_NAME="$MODEL"
fi

# Step 1: Label spans
echo ">>> Step 1: Labeling spans..."
python3 -m ml.data.label_spans \
    --corpus-dir corpora/lint/pilot_v1 \
    --vpd-patterns specs/rules/vpd_patterns.json \
    --golden-yaml specs/rules/pilot_v1_golden.yaml \
    --output ml/data/labeled_spans.jsonl

# Step 2: Feature extraction (for baseline models)
if [[ "$MODEL_NAME" == "logreg" || "$MODEL_NAME" == "gbt" ]]; then
    echo ">>> Step 2: Extracting features..."
    python3 -m ml.data.feature_extract \
        --input ml/data/labeled_spans.jsonl \
        --output ml/data/features.jsonl

    # Step 3: Split data (features version)
    echo ">>> Step 3: Splitting data..."
    python3 -m ml.data.split_data \
        --input ml/data/features.jsonl \
        --train ml/data/features_train.jsonl \
        --dev ml/data/features_dev.jsonl \
        --seed "$SEED"

    # Step 4: Train
    echo ">>> Step 4: Training $MODEL_NAME..."
    python3 -m ml.train \
        --model "$MODEL_NAME" \
        --train ml/data/features_train.jsonl \
        --dev ml/data/features_dev.jsonl \
        --output "ml/eval_${MODEL_NAME}.json" \
        --seed "$SEED"
else
    # BERT-CRF uses raw text, not features
    echo ">>> Step 2: Splitting data..."
    python3 -m ml.data.split_data \
        --input ml/data/labeled_spans.jsonl \
        --train ml/data/train.jsonl \
        --dev ml/data/dev.jsonl \
        --seed "$SEED"

    echo ">>> Step 3: Training $MODEL_NAME..."
    python3 -m ml.train \
        --model "$MODEL_NAME" \
        --train ml/data/train.jsonl \
        --dev ml/data/dev.jsonl \
        --output "ml/eval_bert_crf.json" \
        --seed "$SEED" \
        --device "$DEVICE"
fi

# Step 5: Export for Coq
EVAL_FILE="ml/eval_${MODEL_NAME//-/_}.json"
echo ">>> Step 5: Exporting eval bound..."
python3 -m ml.export_eval \
    --input "$EVAL_FILE" \
    --output proofs/ML/eval_bound.json

# Step 6: F1 gate
echo ">>> Step 6: F1 gate check..."
bash ml/scripts/f1_gate.sh "$EVAL_FILE"

echo ""
echo "=== Pipeline complete ==="
