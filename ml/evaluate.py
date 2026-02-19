#!/usr/bin/env python3
"""Evaluation harness for ML span extractor.

Computes span-level precision/recall/F1 using seqeval, with per-rule-ID
breakdown and overall micro/macro F1. Also computes the delta bound for
the Coq proof.

Usage:
    python -m ml.evaluate --predictions pred.jsonl --gold dev.jsonl --output eval_results.json
"""

import json
import argparse
import logging
from datetime import datetime, timezone
from collections import defaultdict
from pathlib import Path
from typing import List, Dict, Tuple, Any, Optional

logger = logging.getLogger(__name__)


# ── BIO tag validation ───────────────────────────────────────────────────────

def validate_bio_sequence(tags: List[str]) -> bool:
    """Validate a BIO tag sequence for consistency."""
    for i, tag in enumerate(tags):
        if tag == 'O':
            continue
        if tag.startswith('B-'):
            continue
        if tag.startswith('I-'):
            rule = tag[2:]
            # I- tag must follow B- or I- for same rule
            if i == 0:
                return False
            prev = tags[i - 1]
            if prev != f'B-{rule}' and prev != f'I-{rule}':
                return False
        else:
            return False
    return True


# ── Span extraction from BIO tags ────────────────────────────────────────────

def bio_to_spans(tags: List[str]) -> List[Tuple[str, int, int]]:
    """Convert BIO tags to a list of (rule_id, start, end) spans.

    Uses strict BIO scheme: B- starts a new span, I- continues it.
    """
    spans = []
    current_rule = None
    current_start = None

    for i, tag in enumerate(tags):
        if tag.startswith('B-'):
            # Close previous span if open
            if current_rule is not None:
                spans.append((current_rule, current_start, i))
            current_rule = tag[2:]
            current_start = i
        elif tag.startswith('I-'):
            rule = tag[2:]
            if current_rule == rule:
                continue  # Extend current span
            else:
                # Mismatched I- tag, close previous and start new
                if current_rule is not None:
                    spans.append((current_rule, current_start, i))
                current_rule = rule
                current_start = i
        else:
            # O tag — close current span
            if current_rule is not None:
                spans.append((current_rule, current_start, i))
                current_rule = None
                current_start = None

    # Close final span
    if current_rule is not None:
        spans.append((current_rule, current_start, len(tags)))

    return spans


# ── Span-level F1 computation ────────────────────────────────────────────────

def compute_span_metrics(
    gold_tags_list: List[List[str]],
    pred_tags_list: List[List[str]],
) -> Dict[str, Any]:
    """Compute span-level precision/recall/F1.

    Uses exact span matching: a predicted span is correct only if it matches
    a gold span exactly (same rule, start, end).
    """
    # Extract spans from all documents
    gold_spans_per_doc = [bio_to_spans(tags) for tags in gold_tags_list]
    pred_spans_per_doc = [bio_to_spans(tags) for tags in pred_tags_list]

    # Overall counts
    total_tp = 0
    total_fp = 0
    total_fn = 0

    # Per-rule counts
    rule_tp = defaultdict(int)
    rule_fp = defaultdict(int)
    rule_fn = defaultdict(int)

    for gold_spans, pred_spans in zip(gold_spans_per_doc, pred_spans_per_doc):
        gold_set = set(gold_spans)
        pred_set = set(pred_spans)

        tp = gold_set & pred_set
        fp = pred_set - gold_set
        fn = gold_set - pred_set

        total_tp += len(tp)
        total_fp += len(fp)
        total_fn += len(fn)

        for rule, start, end in tp:
            rule_tp[rule] += 1
        for rule, start, end in fp:
            rule_fp[rule] += 1
        for rule, start, end in fn:
            rule_fn[rule] += 1

    # Overall micro F1
    precision = total_tp / (total_tp + total_fp) if (total_tp + total_fp) > 0 else 0.0
    recall = total_tp / (total_tp + total_fn) if (total_tp + total_fn) > 0 else 0.0
    f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0

    # Per-rule metrics
    all_rules = sorted(set(rule_tp.keys()) | set(rule_fp.keys()) | set(rule_fn.keys()))
    per_rule = {}
    for rule in all_rules:
        tp = rule_tp[rule]
        fp = rule_fp[rule]
        fn = rule_fn[rule]
        p = tp / (tp + fp) if (tp + fp) > 0 else 0.0
        r = tp / (tp + fn) if (tp + fn) > 0 else 0.0
        f = 2 * p * r / (p + r) if (p + r) > 0 else 0.0
        per_rule[rule] = {
            "precision": round(p, 4),
            "recall": round(r, 4),
            "f1": round(f, 4),
            "tp": tp, "fp": fp, "fn": fn,
        }

    # Macro F1 (average per-rule F1)
    rule_f1s = [v["f1"] for v in per_rule.values()]
    macro_f1 = sum(rule_f1s) / len(rule_f1s) if rule_f1s else 0.0

    return {
        "overall_precision": round(precision, 4),
        "overall_recall": round(recall, 4),
        "overall_f1": round(f1, 4),
        "macro_f1": round(macro_f1, 4),
        "total_tp": total_tp,
        "total_fp": total_fp,
        "total_fn": total_fn,
        "per_rule": per_rule,
    }


# ── Token-level F1 (alternative metric) ─────────────────────────────────────

def compute_token_metrics(
    gold_tags_list: List[List[str]],
    pred_tags_list: List[List[str]],
) -> Dict[str, float]:
    """Compute token-level precision/recall/F1 (binary: O vs non-O)."""
    total_tp = 0
    total_fp = 0
    total_fn = 0

    for gold_tags, pred_tags in zip(gold_tags_list, pred_tags_list):
        for g, p in zip(gold_tags, pred_tags):
            g_positive = g != 'O'
            p_positive = p != 'O'

            if g_positive and p_positive:
                total_tp += 1
            elif not g_positive and p_positive:
                total_fp += 1
            elif g_positive and not p_positive:
                total_fn += 1

    precision = total_tp / (total_tp + total_fp) if (total_tp + total_fp) > 0 else 0.0
    recall = total_tp / (total_tp + total_fn) if (total_tp + total_fn) > 0 else 0.0
    f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0

    return {
        "token_precision": round(precision, 4),
        "token_recall": round(recall, 4),
        "token_f1": round(f1, 4),
    }


# ── Seqeval integration (optional) ──────────────────────────────────────────

def compute_seqeval_metrics(
    gold_tags_list: List[List[str]],
    pred_tags_list: List[List[str]],
) -> Optional[Dict[str, Any]]:
    """Compute metrics using seqeval library (if available)."""
    try:
        from seqeval.metrics import classification_report, f1_score, precision_score, recall_score
        from seqeval.scheme import IOB2

        f1 = f1_score(gold_tags_list, pred_tags_list, mode='strict', scheme=IOB2)
        p = precision_score(gold_tags_list, pred_tags_list, mode='strict', scheme=IOB2)
        r = recall_score(gold_tags_list, pred_tags_list, mode='strict', scheme=IOB2)

        report = classification_report(gold_tags_list, pred_tags_list,
                                       mode='strict', scheme=IOB2,
                                       output_dict=True)

        return {
            "seqeval_f1": round(f1, 4),
            "seqeval_precision": round(p, 4),
            "seqeval_recall": round(r, 4),
            "seqeval_report": report,
        }
    except ImportError:
        logger.warning("seqeval not installed, skipping seqeval metrics")
        return None
    except Exception as e:
        logger.warning(f"seqeval error: {e}")
        return None


# ── Full evaluation ──────────────────────────────────────────────────────────

def evaluate(
    gold_tags_list: List[List[str]],
    pred_tags_list: List[List[str]],
    model_name: str = "unknown",
    seed: int = 42,
) -> Dict[str, Any]:
    """Run full evaluation and produce results dict.

    The delta field is (1 - overall_f1), used as the probability bound
    for the Coq proof.
    """
    span_metrics = compute_span_metrics(gold_tags_list, pred_tags_list)
    token_metrics = compute_token_metrics(gold_tags_list, pred_tags_list)
    seqeval_metrics = compute_seqeval_metrics(gold_tags_list, pred_tags_list)

    # Delta for Coq proof
    delta = round(1.0 - span_metrics["overall_f1"], 4)

    results = {
        "overall_f1": span_metrics["overall_f1"],
        "overall_precision": span_metrics["overall_precision"],
        "overall_recall": span_metrics["overall_recall"],
        "macro_f1": span_metrics["macro_f1"],
        "delta": delta,
        "per_rule": span_metrics["per_rule"],
        **token_metrics,
        "model": model_name,
        "seed": seed,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }

    if seqeval_metrics:
        results["seqeval"] = seqeval_metrics

    return results


# ── CLI ──────────────────────────────────────────────────────────────────────

def load_tags_from_jsonl(path: str) -> List[List[str]]:
    """Load BIO tags from JSONL (each line has 'bio_tags' field)."""
    all_tags = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            doc = json.loads(line.strip())
            all_tags.append(doc["bio_tags"])
    return all_tags


def main():
    parser = argparse.ArgumentParser(description="Evaluate span extractor predictions")
    parser.add_argument("--gold", required=True,
                        help="Gold standard JSONL with bio_tags")
    parser.add_argument("--predictions", required=True,
                        help="Predictions JSONL with bio_tags")
    parser.add_argument("--output", default="ml/eval_results.json",
                        help="Output evaluation results JSON")
    parser.add_argument("--model", default="unknown",
                        help="Model name for results metadata")
    parser.add_argument("--seed", type=int, default=42,
                        help="Seed for results metadata")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== ML Span Extractor Evaluation ===")

    gold_tags = load_tags_from_jsonl(args.gold)
    pred_tags = load_tags_from_jsonl(args.predictions)

    assert len(gold_tags) == len(pred_tags), \
        f"Mismatched doc counts: gold={len(gold_tags)}, pred={len(pred_tags)}"

    results = evaluate(gold_tags, pred_tags, args.model, args.seed)

    # Write results
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    logger.info(f"Overall F1: {results['overall_f1']:.4f}")
    logger.info(f"Overall Precision: {results['overall_precision']:.4f}")
    logger.info(f"Overall Recall: {results['overall_recall']:.4f}")
    logger.info(f"Delta (1-F1): {results['delta']:.4f}")
    logger.info(f"Macro F1: {results['macro_f1']:.4f}")
    logger.info(f"Token F1: {results['token_f1']:.4f}")
    logger.info(f"Results written to {args.output}")

    # Check threshold
    f1_threshold = 0.94
    if results['overall_f1'] >= f1_threshold:
        logger.info(f"✅ F1 {results['overall_f1']:.4f} >= {f1_threshold} threshold")
    else:
        logger.warning(f"⚠️ F1 {results['overall_f1']:.4f} < {f1_threshold} threshold")

    logger.info("Done.")


if __name__ == "__main__":
    main()
