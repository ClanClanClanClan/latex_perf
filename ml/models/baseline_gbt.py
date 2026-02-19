#!/usr/bin/env python3
"""Gradient-boosted trees baseline for span extraction.

Uses character-level features with GBT for per-token classification.
Expected F1: ~0.85-0.90 (above logistic regression baseline).

Usage:
    python -m ml.models.baseline_gbt --train data/features_train.jsonl --dev data/features_dev.jsonl
"""

import json
import logging
import argparse
import pickle
from pathlib import Path
from typing import List, Dict, Tuple, Any

import numpy as np
from sklearn.ensemble import GradientBoostingClassifier

logger = logging.getLogger(__name__)


# Reuse data loading from logreg baseline
from ml.models.baseline_logreg import (
    load_features_and_tags,
    tags_to_binary,
    reconstruct_per_doc_tags,
)


class GBTSpanExtractor:
    """Gradient-boosted trees span extractor."""

    def __init__(
        self,
        n_estimators: int = 200,
        max_depth: int = 6,
        learning_rate: float = 0.1,
        subsample: float = 0.8,
        seed: int = 42,
    ):
        self.model = GradientBoostingClassifier(
            n_estimators=n_estimators,
            max_depth=max_depth,
            learning_rate=learning_rate,
            subsample=subsample,
            random_state=seed,
        )
        self.seed = seed

    def fit(self, X: np.ndarray, y_binary: np.ndarray) -> 'GBTSpanExtractor':
        """Train the model."""
        self.model.fit(X, y_binary)
        return self

    def predict(self, X: np.ndarray) -> np.ndarray:
        """Predict binary labels."""
        return self.model.predict(X)

    def predict_proba(self, X: np.ndarray) -> np.ndarray:
        """Predict probabilities."""
        return self.model.predict_proba(X)

    def feature_importances(self) -> np.ndarray:
        """Get feature importance scores."""
        return self.model.feature_importances_

    def save(self, path: str):
        """Save model to pickle."""
        with open(path, 'wb') as f:
            pickle.dump({'model': self.model}, f)

    def load(self, path: str):
        """Load model from pickle."""
        with open(path, 'rb') as f:
            data = pickle.load(f)
        self.model = data['model']


FEATURE_NAMES = [
    "char_ord", "in_math", "char_class", "token_kind",
    "line_length", "pos_in_line", "leading_whitespace",
]


def train_and_evaluate(
    train_path: str,
    dev_path: str,
    n_estimators: int = 200,
    max_depth: int = 6,
    learning_rate: float = 0.1,
    subsample: float = 0.8,
    seed: int = 42,
) -> Dict[str, Any]:
    """Train GBT and evaluate on dev set."""
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
    logger.info(f"Training GBT (n_est={n_estimators}, depth={max_depth}, "
                f"lr={learning_rate})...")
    model = GBTSpanExtractor(
        n_estimators=n_estimators,
        max_depth=max_depth,
        learning_rate=learning_rate,
        subsample=subsample,
        seed=seed,
    )
    model.fit(X_train, y_train)

    # Feature importances
    importances = model.feature_importances()
    logger.info("Feature importances:")
    for name, imp in sorted(zip(FEATURE_NAMES, importances),
                             key=lambda x: -x[1]):
        logger.info(f"  {name}: {imp:.4f}")

    # Predict
    y_pred = model.predict(X_dev)
    logger.info(f"Predictions: {np.sum(y_pred)} positive ({np.mean(y_pred) * 100:.1f}%)")

    # Reconstruct per-doc BIO tags
    pred_doc_tags = reconstruct_per_doc_tags(y_pred, dev_doc_lengths)

    # Evaluate
    results = evaluate(dev_doc_tags, pred_doc_tags, "gbt", seed)

    # Add feature importances
    results["feature_importances"] = {
        name: round(float(imp), 4) for name, imp in zip(FEATURE_NAMES, importances)
    }

    return results


def main():
    parser = argparse.ArgumentParser(description="Gradient-boosted trees baseline")
    parser.add_argument("--train", required=True, help="Train features JSONL")
    parser.add_argument("--dev", required=True, help="Dev features JSONL")
    parser.add_argument("--output", default="ml/eval_gbt.json",
                        help="Output evaluation results")
    parser.add_argument("--n-estimators", type=int, default=200)
    parser.add_argument("--max-depth", type=int, default=6)
    parser.add_argument("--learning-rate", type=float, default=0.1)
    parser.add_argument("--subsample", type=float, default=0.8)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== Gradient-Boosted Trees Baseline ===")
    results = train_and_evaluate(
        args.train, args.dev,
        args.n_estimators, args.max_depth, args.learning_rate, args.subsample,
        args.seed,
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
