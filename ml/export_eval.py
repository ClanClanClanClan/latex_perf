#!/usr/bin/env python3
"""Export evaluation JSON for Coq proof import.

Reads eval_results.json and generates the delta value used in
proofs/ML/SpanExtractorSound.v as an axiom.

Usage:
    python -m ml.export_eval --input ml/eval_results.json --output proofs/ML/eval_bound.json
"""

import json
import argparse
import logging
from pathlib import Path

logger = logging.getLogger(__name__)


def export_for_coq(eval_path: str, output_path: str) -> dict:
    """Export evaluation bound for Coq proof import.

    The Coq proof uses:
        Axiom eval_bound : (1 - delta >= threshold)%R.

    We export delta and verify the bound holds.
    """
    with open(eval_path, 'r') as f:
        results = json.load(f)

    delta = results.get("delta", 1.0)
    f1 = results.get("overall_f1", 0.0)
    threshold = 0.94

    bound = {
        "delta": delta,
        "f1": f1,
        "threshold": threshold,
        "bound_holds": (1.0 - delta) >= threshold,
        "model": results.get("model", "unknown"),
        "seed": results.get("seed", 42),
        "timestamp": results.get("timestamp", ""),
    }

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        json.dump(bound, f, indent=2)

    logger.info(f"Delta: {delta:.4f}")
    logger.info(f"F1: {f1:.4f}")
    logger.info(f"Bound holds (1-{delta:.4f} >= {threshold}): {bound['bound_holds']}")

    return bound


def main():
    parser = argparse.ArgumentParser(description="Export eval bound for Coq")
    parser.add_argument("--input", default="ml/eval_results.json")
    parser.add_argument("--output", default="proofs/ML/eval_bound.json")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    bound = export_for_coq(args.input, args.output)

    if not bound["bound_holds"]:
        logger.error("Bound does NOT hold — F1 below threshold!")
        exit(1)
    else:
        logger.info("Bound holds — safe for Coq import.")


if __name__ == "__main__":
    main()
