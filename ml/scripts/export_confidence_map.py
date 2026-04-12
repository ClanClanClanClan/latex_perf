#!/usr/bin/env python3
"""Export ML confidence map from eval_results.json.

Reads per-rule precision/recall/tp/fn from the v2 ByteClassifier evaluation
results and produces a JSON confidence map for the OCaml evidence_scoring
module.  Rules with zero true positives get suppress=true.

Usage:
    python3 ml/scripts/export_confidence_map.py \
        --input ml/checkpoints_v2/eval_results.json \
        --output data/ml_confidence_map.json
"""

import argparse
import json
import sys


def export_confidence_map(input_path: str, output_path: str) -> dict:
    with open(input_path) as f:
        eval_results = json.load(f)

    per_rule = eval_results.get("per_rule", {})
    confidence_map = {}

    for rule_id, metrics in per_rule.items():
        tp = metrics.get("tp", 0)
        fn = metrics.get("fn", 0)
        precision = metrics.get("precision", 0.0)

        # Rules with zero true positives in eval: suppress entirely
        suppress = tp == 0 and fn == 0
        weight = 0.0 if suppress else precision

        confidence_map[rule_id] = {
            "precision": precision,
            "weight": weight,
            "suppress": suppress,
        }

    with open(output_path, "w") as f:
        json.dump(confidence_map, f, indent=2)

    print(f"Exported {len(confidence_map)} rules to {output_path}")
    for rule_id, conf in sorted(confidence_map.items()):
        status = "SUPPRESS" if conf["suppress"] else f"weight={conf['weight']:.4f}"
        print(f"  {rule_id}: {status}")

    return confidence_map


def main():
    parser = argparse.ArgumentParser(description="Export ML confidence map")
    parser.add_argument(
        "--input",
        default="ml/checkpoints_v2/eval_results.json",
        help="Path to eval_results.json",
    )
    parser.add_argument(
        "--output",
        default="data/ml_confidence_map.json",
        help="Output path for confidence map JSON",
    )
    args = parser.parse_args()
    export_confidence_map(args.input, args.output)


if __name__ == "__main__":
    main()
