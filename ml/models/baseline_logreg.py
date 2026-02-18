#!/usr/bin/env python3
"""Logistic regression baseline for span extraction.

Uses character-level features (char class, token kind, in-math, line features)
with logistic regression for per-token binary classification (error span or not).

Usage:
    python -m ml.models.baseline_logreg --train data/features_train.jsonl --dev data/features_dev.jsonl
"""

import json
import logging
import argparse
import pickle
from pathlib import Path
from typing import List, Dict, Tuple, Any

import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

logger = logging.getLogger(__name__)


def load_features_and_tags(jsonl_path: str) -> Tuple[np.ndarray, List[str], List[List[str]]]:
    """Load features and BIO tags from feature JSONL.

    Returns: (X, flat_tags, per_doc_tags)
    """
    all_rows = []
    flat_tags = []
    per_doc_tags = []

    with open(jsonl_path, 'r', encoding='utf-8') as f:
        for line in f:
            doc = json.loads(line.strip())
            features = doc["features"]
            bio_tags = doc["bio_tags"]
            per_doc_tags.append(bio_tags)

            for feat, tag in zip(features, bio_tags):
                row = [
                    feat["char_ord"],
                    1.0 if feat["in_math"] else 0.0,
                    _char_class_to_int(feat["char_class"]),
                    _token_kind_to_int(feat["token_kind"]),
                    float(feat["line_length"]),
                    float(feat["pos_in_line"]),
                    float(feat["leading_whitespace"]),
                ]
                all_rows.append(row)
                flat_tags.append(tag)

    X = np.array(all_rows, dtype=np.float32)
    return X, flat_tags, per_doc_tags


_CHAR_CLASS_MAP = {
    "letter": 0, "digit": 1, "whitespace": 2, "newline": 3,
    "punctuation": 4, "symbol": 5, "other": 6,
}

_TOKEN_KIND_MAP = {
    "Word": 0, "Space": 1, "Newline": 2, "Command": 3,
    "BracketOpen": 4, "BracketClose": 5, "Quote": 6,
    "Symbol": 7, "MathDelim": 8, "Other": 9,
}


def _char_class_to_int(cc: str) -> float:
    return float(_CHAR_CLASS_MAP.get(cc, 6))


def _token_kind_to_int(tk: str) -> float:
    return float(_TOKEN_KIND_MAP.get(tk, 9))


def tags_to_binary(tags: List[str]) -> np.ndarray:
    """Convert BIO tags to binary: 0=O, 1=B-*/I-*."""
    return np.array([0 if t == 'O' else 1 for t in tags], dtype=np.int32)


def binary_to_bio(y_pred: np.ndarray, original_tags: List[str]) -> List[str]:
    """Convert binary predictions back to BIO format.

    For positions predicted as 1 (positive), assigns B-SPAN for the first
    positive position in a contiguous sequence, and I-SPAN for continuations.
    """
    tags = []
    in_span = False
    for pred in y_pred:
        if pred == 1:
            if not in_span:
                tags.append("B-SPAN")
                in_span = True
            else:
                tags.append("I-SPAN")
        else:
            tags.append("O")
            in_span = False
    return tags


def reconstruct_per_doc_tags(
    flat_predictions: np.ndarray,
    per_doc_lengths: List[int],
) -> List[List[str]]:
    """Split flat predictions back into per-document tag lists."""
    result = []
    offset = 0
    for length in per_doc_lengths:
        doc_preds = flat_predictions[offset:offset + length]
        doc_tags = binary_to_bio(doc_preds, [])
        result.append(doc_tags)
        offset += length
    return result


class LogregSpanExtractor:
    """Logistic regression baseline span extractor."""

    def __init__(self, C: float = 1.0, max_iter: int = 1000, seed: int = 42):
        self.model = LogisticRegression(
            C=C,
            max_iter=max_iter,
            solver='lbfgs',
            random_state=seed,
            class_weight='balanced',  # Handle class imbalance (mostly O tags)
        )
        self.scaler = StandardScaler()
        self.seed = seed

    def fit(self, X: np.ndarray, y_binary: np.ndarray) -> 'LogregSpanExtractor':
        """Train the model."""
        X_scaled = self.scaler.fit_transform(X)
        self.model.fit(X_scaled, y_binary)
        return self

    def predict(self, X: np.ndarray) -> np.ndarray:
        """Predict binary labels."""
        X_scaled = self.scaler.transform(X)
        return self.model.predict(X_scaled)

    def predict_proba(self, X: np.ndarray) -> np.ndarray:
        """Predict probabilities."""
        X_scaled = self.scaler.transform(X)
        return self.model.predict_proba(X_scaled)

    def save(self, path: str):
        """Save model to pickle."""
        with open(path, 'wb') as f:
            pickle.dump({'model': self.model, 'scaler': self.scaler}, f)

    def load(self, path: str):
        """Load model from pickle."""
        with open(path, 'rb') as f:
            data = pickle.load(f)
        self.model = data['model']
        self.scaler = data['scaler']


def train_and_evaluate(
    train_path: str,
    dev_path: str,
    C: float = 1.0,
    max_iter: int = 1000,
    seed: int = 42,
) -> Dict[str, Any]:
    """Train logistic regression and evaluate on dev set."""
    from ml.evaluate import evaluate

    logger.info("Loading training data...")
    X_train, train_tags, train_doc_tags = load_features_and_tags(train_path)
    y_train = tags_to_binary(train_tags)
    train_doc_lengths = [len(tags) for tags in train_doc_tags]

    logger.info("Loading dev data...")
    X_dev, dev_tags, dev_doc_tags = load_features_and_tags(dev_path)
    y_dev = tags_to_binary(dev_tags)
    dev_doc_lengths = [len(tags) for tags in dev_doc_tags]

    logger.info(f"Train: {X_train.shape[0]} samples, "
                f"{np.sum(y_train)} positive ({np.mean(y_train) * 100:.1f}%)")
    logger.info(f"Dev: {X_dev.shape[0]} samples, "
                f"{np.sum(y_dev)} positive ({np.mean(y_dev) * 100:.1f}%)")

    # Train
    logger.info(f"Training LogisticRegression (C={C}, max_iter={max_iter})...")
    model = LogregSpanExtractor(C=C, max_iter=max_iter, seed=seed)
    model.fit(X_train, y_train)

    # Predict
    y_pred = model.predict(X_dev)
    logger.info(f"Predictions: {np.sum(y_pred)} positive ({np.mean(y_pred) * 100:.1f}%)")

    # Reconstruct per-doc BIO tags
    pred_doc_tags = reconstruct_per_doc_tags(y_pred, dev_doc_lengths)

    # Evaluate
    results = evaluate(dev_doc_tags, pred_doc_tags, "logreg", seed)

    return results


def main():
    parser = argparse.ArgumentParser(description="Logistic regression baseline")
    parser.add_argument("--train", required=True, help="Train features JSONL")
    parser.add_argument("--dev", required=True, help="Dev features JSONL")
    parser.add_argument("--output", default="ml/eval_logreg.json",
                        help="Output evaluation results")
    parser.add_argument("--C", type=float, default=1.0)
    parser.add_argument("--max-iter", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== Logistic Regression Baseline ===")
    results = train_and_evaluate(
        args.train, args.dev, args.C, args.max_iter, args.seed
    )

    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, 'w') as f:
        json.dump(results, f, indent=2)

    logger.info(f"F1: {results['overall_f1']:.4f}")
    logger.info(f"Precision: {results['overall_precision']:.4f}")
    logger.info(f"Recall: {results['overall_recall']:.4f}")
    logger.info(f"Results written to {args.output}")


if __name__ == "__main__":
    main()
