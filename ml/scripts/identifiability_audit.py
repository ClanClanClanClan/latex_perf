#!/usr/bin/env python3
"""Local identifiability audit for ambiguous rules.

For each gold span on an ambiguous rule, checks whether the correct label
is recoverable from the 300-char training window alone, or whether it depends
on parser state (in_math, in_verbatim) from outside the window.

This directly tests the expert's hypothesis #2: "Some labels depend on state
outside the 300-character window."

Usage:
    python -m ml.scripts.identifiability_audit [--window-size 300]
    python -m ml.scripts.identifiability_audit --input ml/data/dev.jsonl
"""

import json
import logging
import argparse
from collections import defaultdict
from typing import Dict, List, Set, Tuple

from ml.data.parser_state import compute_parser_state, ParserState
from ml.data.label_spans import Span

logger = logging.getLogger(__name__)

# Rules that depend on math/verbatim context for disambiguation
AMBIGUOUS_RULES = {
    'TYPO-001', 'TYPO-005', 'TYPO-012', 'TYPO-028',
    'TYPO-048', 'TYPO-052', 'TYPO-056', 'TYPO-062',
}

# Which parser-state features each ambiguous rule depends on
RULE_STATE_DEPS: Dict[str, List[str]] = {
    'TYPO-001': ['in_math', 'in_verbatim'],   # " in math/verbatim is OK
    'TYPO-005': ['in_math'],                    # ... in math is OK
    'TYPO-012': [],                             # digit+apostrophe — context-only
    'TYPO-028': ['in_math'],                    # $$ nesting depends on math state
    'TYPO-048': ['in_math'],                    # en-dash in math is OK
    'TYPO-052': ['in_math'],                    # < > in math is OK
    'TYPO-056': ['in_math'],                    # accent macros in math
    'TYPO-062': ['in_verbatim'],                # \\ in verbatim is OK
}


def _best_window(span_start: int, span_end: int,
                 doc_len: int, window_size: int) -> Tuple[int, int]:
    """Find the best window of `window_size` chars that contains the span."""
    if doc_len <= window_size:
        return 0, doc_len

    # Center the span in the window
    span_mid = (span_start + span_end) // 2
    ws = max(0, span_mid - window_size // 2)
    we = ws + window_size
    if we > doc_len:
        we = doc_len
        ws = max(0, we - window_size)
    return ws, we


def check_span_identifiability(
    text: str,
    span_start: int,
    span_end: int,
    rule_id: str,
    doc_state: ParserState,
    window_size: int = 300,
) -> Dict:
    """Check if a single span's label is identifiable from its window alone.

    Compares parser state computed from the full document vs from the window only.

    Returns:
        {
            'identifiable': bool,
            'reason': str,  # 'match' or description of mismatch
            'doc_state': Dict,  # parser state from full doc at span position
            'win_state': Dict,  # parser state from window at span position
        }
    """
    deps = RULE_STATE_DEPS.get(rule_id, ['in_math', 'in_verbatim'])
    if not deps:
        # Rule doesn't depend on parser state → always identifiable
        return {
            'identifiable': True,
            'reason': 'no_parser_state_dependency',
            'doc_state': {},
            'win_state': {},
        }

    # Get parser state from full document
    doc_features = {}
    for feat in deps:
        vals = getattr(doc_state, feat)
        doc_features[feat] = vals[span_start] if span_start < len(vals) else False

    # Compute parser state from window only
    ws, we = _best_window(span_start, span_end, len(text), window_size)
    window_text = text[ws:we]
    win_state = compute_parser_state(window_text)

    # Map span position into window coordinates
    win_pos = span_start - ws
    win_features = {}
    for feat in deps:
        vals = getattr(win_state, feat)
        win_features[feat] = vals[win_pos] if win_pos < len(vals) else False

    # Compare
    mismatches = []
    for feat in deps:
        if doc_features[feat] != win_features[feat]:
            mismatches.append(
                f"{feat}: doc={doc_features[feat]}, window={win_features[feat]}")

    if mismatches:
        return {
            'identifiable': False,
            'reason': '; '.join(mismatches),
            'doc_state': doc_features,
            'win_state': win_features,
        }
    else:
        return {
            'identifiable': True,
            'reason': 'match',
            'doc_state': doc_features,
            'win_state': win_features,
        }


def audit_identifiability(
    labeled_docs: List[Dict],
    window_size: int = 300,
    rules: Set[str] = None,
) -> Dict:
    """Audit local identifiability for all ambiguous-rule gold spans.

    For each gold span on an ambiguous rule:
    1. Compute parser state from the full document
    2. Compute parser state from the 300-char window containing the span
    3. If in_math/in_verbatim differs → NOT identifiable from window alone

    Args:
        labeled_docs: list of dicts with 'text' and 'spans'
        window_size: size of the training window (default 300 chars)
        rules: set of rule IDs to audit (default: AMBIGUOUS_RULES)

    Returns:
        dict with per-rule identifiability stats + overall summary
    """
    if rules is None:
        rules = AMBIGUOUS_RULES

    per_rule: Dict[str, Dict] = defaultdict(lambda: {
        'total': 0, 'identifiable': 0, 'not_identifiable': 0,
        'mismatches': [],
    })

    for doc_idx, doc in enumerate(labeled_docs):
        text = doc['text']
        spans = doc.get('spans', [])

        # Skip docs with no relevant spans
        relevant = [s for s in spans
                    if (s['rule_id'] if isinstance(s, dict) else s.rule_id)
                    in rules]
        if not relevant:
            continue

        # Compute parser state once per document
        doc_state = compute_parser_state(text)

        for span in relevant:
            rule_id = span['rule_id'] if isinstance(span, dict) else span.rule_id
            start = span['start'] if isinstance(span, dict) else span.start
            end = span['end'] if isinstance(span, dict) else span.end

            result = check_span_identifiability(
                text, start, end, rule_id, doc_state, window_size)

            stats = per_rule[rule_id]
            stats['total'] += 1
            if result['identifiable']:
                stats['identifiable'] += 1
            else:
                stats['not_identifiable'] += 1
                stats['mismatches'].append({
                    'doc_idx': doc_idx,
                    'span': (start, end),
                    'reason': result['reason'],
                })

    # Compute percentages
    summary = {}
    total_all = 0
    identifiable_all = 0

    for rule_id in sorted(per_rule.keys()):
        stats = per_rule[rule_id]
        total = stats['total']
        ident = stats['identifiable']
        total_all += total
        identifiable_all += ident
        summary[rule_id] = {
            'total': total,
            'identifiable': ident,
            'not_identifiable': stats['not_identifiable'],
            'pct_identifiable': round(100.0 * ident / max(total, 1), 1),
            'sample_mismatches': stats['mismatches'][:5],  # first 5 examples
        }

    return {
        'per_rule': summary,
        'overall': {
            'total': total_all,
            'identifiable': identifiable_all,
            'not_identifiable': total_all - identifiable_all,
            'pct_identifiable': round(
                100.0 * identifiable_all / max(total_all, 1), 1),
        },
        'window_size': window_size,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Audit local identifiability of ambiguous rules")
    parser.add_argument("--input", default="ml/data/dev.jsonl",
                        help="Input labeled JSONL")
    parser.add_argument("--window-size", type=int, default=300,
                        help="Training window size in chars (default: 300)")
    parser.add_argument("--output", default=None,
                        help="Output JSON file (default: print to stdout)")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info(f"Loading {args.input}...")
    docs = []
    with open(args.input, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                docs.append(json.loads(line))
    logger.info(f"Loaded {len(docs)} documents")

    logger.info(f"Auditing identifiability (window_size={args.window_size})...")
    results = audit_identifiability(docs, args.window_size)

    # Print results
    print(f"\n{'='*70}")
    print(f"LOCAL IDENTIFIABILITY AUDIT (window_size={args.window_size})")
    print(f"{'='*70}")
    print(f"\n{'Rule':<12} {'Total':>7} {'Ident':>7} {'Not':>7} {'%Ident':>8}")
    print(f"{'-'*12} {'-'*7} {'-'*7} {'-'*7} {'-'*8}")

    for rule_id, stats in sorted(results['per_rule'].items()):
        print(f"{rule_id:<12} {stats['total']:>7} {stats['identifiable']:>7} "
              f"{stats['not_identifiable']:>7} {stats['pct_identifiable']:>7.1f}%")

    overall = results['overall']
    print(f"{'-'*12} {'-'*7} {'-'*7} {'-'*7} {'-'*8}")
    print(f"{'OVERALL':<12} {overall['total']:>7} {overall['identifiable']:>7} "
          f"{overall['not_identifiable']:>7} {overall['pct_identifiable']:>7.1f}%")

    # Show sample mismatches
    for rule_id, stats in sorted(results['per_rule'].items()):
        if stats['sample_mismatches']:
            print(f"\n  {rule_id} sample mismatches:")
            for m in stats['sample_mismatches']:
                print(f"    doc={m['doc_idx']}, span={m['span']}: {m['reason']}")

    if args.output:
        # Remove non-serializable sample mismatches for JSON output
        clean = {
            'per_rule': {
                r: {k: v for k, v in s.items() if k != 'sample_mismatches'}
                for r, s in results['per_rule'].items()
            },
            'overall': results['overall'],
            'window_size': results['window_size'],
        }
        with open(args.output, 'w') as f:
            json.dump(clean, f, indent=2)
        logger.info(f"Wrote results to {args.output}")


if __name__ == "__main__":
    main()
