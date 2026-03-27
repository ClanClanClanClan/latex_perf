#!/usr/bin/env bash
# Pack pre-labeled training data for Colab upload.
#
# Creates a compact archive (39 MB) with pre-labeled train/dev splits
# and all ML code — skips arXiv download (~50 min) and labeling (~70 min)
# when running the Colab notebook.
#
# Prerequisites: run the labeling + split pipeline first:
#   cd Scripts/ml && python -m ml.data.label_spans && python -m ml.data.split_data
#
# Usage: cd Scripts && bash ml/scripts/pack_training_data.sh
set -euo pipefail

OUT="ml/data/colab_training_data.tar.gz"

echo "=== Packing ML training data for Colab ==="

# Verify we're in the right directory
if [[ ! -f "ml/config.yaml" ]]; then
    echo "ERROR: Run from the Scripts/ project root."
    exit 1
fi

# Verify pre-labeled data exists
if [[ ! -f "ml/data/train.jsonl" ]] || [[ ! -f "ml/data/dev.jsonl" ]]; then
    echo "ERROR: ml/data/train.jsonl and dev.jsonl must exist."
    echo "Run the labeling + split pipeline first:"
    echo "  python -m ml.data.label_spans"
    echo "  python -m ml.data.split_data"
    exit 1
fi

# Pack pre-labeled data + code (no corpus files — saves ~400 MB)
tar czf "$OUT" \
    ml/data/train.jsonl \
    ml/data/dev.jsonl \
    ml/config.yaml \
    ml/data/label_spans.py \
    ml/data/split_data.py \
    ml/data/feature_extract.py \
    ml/data/parser_state.py \
    ml/data/__init__.py \
    ml/models/bert_crf.py \
    ml/models/__init__.py \
    ml/evaluate.py \
    ml/export_eval.py \
    ml/__init__.py \
    specs/rules/vpd_patterns.json \
    specs/rules/pilot_v1_golden.yaml

size=$(du -h "$OUT" | cut -f1)
echo "Created $OUT ($size)"
echo ""
echo "Upload to Colab and run: ml/notebooks/span_extractor_training.ipynb"
echo "Or copy to Google Drive for automatic loading on subsequent runs."
