#!/usr/bin/env python3
"""Unified training entry point for ML span extractor.

Dispatches to the appropriate model based on --model flag.

Usage:
    python -m ml.train --model logreg --train data/features_train.jsonl --dev data/features_dev.jsonl
    python -m ml.train --model gbt --train data/features_train.jsonl --dev data/features_dev.jsonl
    python -m ml.train --model bert-crf --train data/train.jsonl --dev data/dev.jsonl --device cuda
"""

import json
import argparse
import logging
from pathlib import Path

import yaml

logger = logging.getLogger(__name__)


def main():
    parser = argparse.ArgumentParser(description="Unified ML span extractor training")
    parser.add_argument("--model", required=True,
                        choices=["logreg", "gbt", "bert-crf"],
                        help="Model to train")
    parser.add_argument("--train", required=True, help="Training data")
    parser.add_argument("--dev", required=True, help="Dev data")
    parser.add_argument("--output", default=None, help="Output eval JSON")
    parser.add_argument("--config", default="ml/config.yaml", help="Config file")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--device", default="cpu", help="Device for BERT")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    # Load config
    config = {}
    if Path(args.config).exists():
        with open(args.config) as f:
            config = yaml.safe_load(f) or {}

    output = args.output or f"ml/eval_{args.model.replace('-', '_')}.json"

    logger.info(f"=== Training: {args.model} ===")

    if args.model == "logreg":
        from ml.models.baseline_logreg import train_and_evaluate
        cfg = config.get("baseline_logreg", {})
        results = train_and_evaluate(
            args.train, args.dev,
            C=cfg.get("C", 1.0),
            max_iter=cfg.get("max_iter", 1000),
            seed=args.seed,
        )

    elif args.model == "gbt":
        from ml.models.baseline_gbt import train_and_evaluate
        cfg = config.get("baseline_gbt", {})
        results = train_and_evaluate(
            args.train, args.dev,
            n_estimators=cfg.get("n_estimators", 200),
            max_depth=cfg.get("max_depth", 6),
            learning_rate=cfg.get("learning_rate", 0.1),
            subsample=cfg.get("subsample", 0.8),
            seed=args.seed,
        )

    elif args.model == "bert-crf":
        from ml.models.bert_crf import train_bert_crf
        cfg = config.get("bert_crf", {})
        results = train_bert_crf(
            args.train, args.dev,
            model_name=cfg.get("model_name", "allenai/scibert_scivocab_uncased"),
            max_length=cfg.get("max_length", 512),
            batch_size=cfg.get("batch_size", 16),
            epochs=cfg.get("epochs", 5),
            learning_rate=cfg.get("learning_rate", 2e-5),
            crf_lr=cfg.get("crf_learning_rate", 1e-3),
            seed=args.seed,
            device=args.device,
        )

    else:
        raise ValueError(f"Unknown model: {args.model}")

    # Write results
    Path(output).parent.mkdir(parents=True, exist_ok=True)
    with open(output, 'w') as f:
        json.dump(results, f, indent=2)

    logger.info(f"F1: {results.get('overall_f1', 'N/A')}")
    logger.info(f"Delta: {results.get('delta', 'N/A')}")
    logger.info(f"Results: {output}")


if __name__ == "__main__":
    main()
