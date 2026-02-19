#!/usr/bin/env python3
"""Stratified train/dev split for BIO-tagged documents.

Splits labeled JSONL into train (80%) and dev (20%) sets, stratified by
rule distribution to ensure every rule ID appears in both splits.

Usage:
    python -m ml.data.split_data [--input data/labeled_spans.jsonl]
                                 [--train data/train.jsonl]
                                 [--dev data/dev.jsonl]
                                 [--seed 42]
"""

import json
import random
import argparse
import logging
from collections import Counter, defaultdict
from pathlib import Path
from typing import List, Dict, Tuple, Any

import yaml

logger = logging.getLogger(__name__)


def load_labeled_jsonl(path: str) -> List[Dict]:
    """Load labeled documents from JSONL."""
    docs = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                docs.append(json.loads(line))
    return docs


def get_primary_rule(doc: Dict) -> str:
    """Get the primary (most frequent) rule ID for a document.

    Used as the stratification key.
    """
    rule_ids = doc.get("rule_ids", [])
    if not rule_ids:
        return "O"  # No rules = "other" stratum
    # If multiple rules, use the first one (they're sorted)
    return rule_ids[0]


def stratified_split(
    docs: List[Dict],
    train_ratio: float = 0.80,
    seed: int = 42,
) -> Tuple[List[Dict], List[Dict]]:
    """Split documents into train/dev with stratification by primary rule.

    Ensures every rule ID that appears in the full set also appears in both
    train and dev (when there are at least 2 documents with that rule).
    """
    rng = random.Random(seed)

    # Group by primary rule
    rule_groups: Dict[str, List[Dict]] = defaultdict(list)
    for doc in docs:
        rule = get_primary_rule(doc)
        rule_groups[rule].append(doc)

    train = []
    dev = []

    for rule, group in sorted(rule_groups.items()):
        rng.shuffle(group)
        if len(group) == 1:
            # Can't split a single doc — put in train, but also copy to dev
            # for coverage (the model will see this rule in both splits)
            train.append(group[0])
            dev.append(group[0])
            logger.debug(f"  {rule}: 1 doc → duplicated to both train and dev")
        else:
            n_train = max(1, int(len(group) * train_ratio))
            # Ensure at least 1 in dev
            n_train = min(n_train, len(group) - 1)
            train.extend(group[:n_train])
            dev.extend(group[n_train:])
            logger.debug(f"  {rule}: {len(group)} docs → {n_train} train, "
                        f"{len(group) - n_train} dev")

    # Shuffle within splits
    rng.shuffle(train)
    rng.shuffle(dev)

    return train, dev


def write_jsonl(docs: List[Dict], path: str) -> None:
    """Write documents to JSONL."""
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        for doc in docs:
            json.dump(doc, f, ensure_ascii=False)
            f.write('\n')


def compute_split_stats(
    train: List[Dict],
    dev: List[Dict],
) -> Dict[str, Any]:
    """Compute statistics about the split."""
    train_rules = Counter()
    dev_rules = Counter()

    for doc in train:
        for rule in doc.get("rule_ids", []):
            train_rules[rule] += 1
    for doc in dev:
        for rule in doc.get("rule_ids", []):
            dev_rules[rule] += 1

    all_rules = set(train_rules.keys()) | set(dev_rules.keys())
    train_only = set(train_rules.keys()) - set(dev_rules.keys())
    dev_only = set(dev_rules.keys()) - set(train_rules.keys())

    train_spans = sum(len(doc.get("spans", [])) for doc in train)
    dev_spans = sum(len(doc.get("spans", [])) for doc in dev)

    return {
        "train_docs": len(train),
        "dev_docs": len(dev),
        "train_spans": train_spans,
        "dev_spans": dev_spans,
        "total_rules": len(all_rules),
        "train_only_rules": sorted(train_only),
        "dev_only_rules": sorted(dev_only),
        "rule_coverage_ok": len(train_only) == 0 and len(dev_only) == 0,
    }


def main():
    parser = argparse.ArgumentParser(description="Stratified train/dev split")
    parser.add_argument("--input", default="ml/data/labeled_spans.jsonl",
                        help="Input labeled JSONL")
    parser.add_argument("--train", default="ml/data/train.jsonl",
                        help="Output train JSONL")
    parser.add_argument("--dev", default="ml/data/dev.jsonl",
                        help="Output dev JSONL")
    parser.add_argument("--train-ratio", type=float, default=0.80,
                        help="Train split ratio (default: 0.80)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed (default: 42)")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== Stratified Train/Dev Split ===")
    logger.info(f"Input: {args.input}")
    logger.info(f"Seed: {args.seed}")
    logger.info(f"Ratio: {args.train_ratio:.0%} train / {1 - args.train_ratio:.0%} dev")

    # Load
    docs = load_labeled_jsonl(args.input)
    logger.info(f"Loaded {len(docs)} documents")

    # Split
    train, dev = stratified_split(docs, args.train_ratio, args.seed)

    # Stats
    stats = compute_split_stats(train, dev)
    logger.info(f"Train: {stats['train_docs']} docs, {stats['train_spans']} spans")
    logger.info(f"Dev: {stats['dev_docs']} docs, {stats['dev_spans']} spans")
    logger.info(f"Rules: {stats['total_rules']} total, coverage OK: {stats['rule_coverage_ok']}")

    if stats['train_only_rules']:
        logger.warning(f"Rules only in train: {stats['train_only_rules']}")
    if stats['dev_only_rules']:
        logger.warning(f"Rules only in dev: {stats['dev_only_rules']}")

    # Write
    write_jsonl(train, args.train)
    write_jsonl(dev, args.dev)
    logger.info(f"Wrote train to {args.train}")
    logger.info(f"Wrote dev to {args.dev}")
    logger.info("Done.")


if __name__ == "__main__":
    main()
