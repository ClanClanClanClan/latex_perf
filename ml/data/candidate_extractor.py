#!/usr/bin/env python3
"""Candidate extraction for the v2 span-extractor pipeline.

Extracts candidate positions for each rule from LaTeX documents by reusing
the deterministic ``replay_pattern()`` function from ``ml.data.label_spans``.
Each candidate represents a *potential* violation site; labeling against gold
spans determines which candidates are true positives.

The 16 v2 rules are partitioned into:
  - 8 deterministic rules (handled purely by replay, F1 = 1.0)
  - 8 ambiguous rules (require ML disambiguation)

Usage:
    python -m ml.data.candidate_extractor
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, replace
from typing import Dict, List, Optional, Set, Tuple, Union

from ml.data.label_spans import Span, replay_pattern

logger = logging.getLogger(__name__)

# ── Rule partitions ──────────────────────────────────────────────────────────

DETERMINISTIC_RULES: Set[str] = {
    "TYPO-002",
    "TYPO-003",
    "TYPO-004",
    "TYPO-013",
    "TYPO-030",
    "TYPO-043",
    "TYPO-047",
    "TYPO-061",
}

AMBIGUOUS_RULES: Set[str] = {
    "TYPO-001",
    "TYPO-005",
    "TYPO-012",
    "TYPO-028",
    "TYPO-048",
    "TYPO-052",
    "TYPO-056",
    "TYPO-062",
}

ALL_V2_RULES: Set[str] = DETERMINISTIC_RULES | AMBIGUOUS_RULES


# ── Candidate dataclass ──────────────────────────────────────────────────────

@dataclass(frozen=True)
class Candidate:
    """A candidate violation site in a document."""

    rule_id: str
    start: int
    end: int
    is_positive: bool = False

    def __post_init__(self) -> None:
        if self.start < 0 or self.end < self.start:
            raise ValueError(f"Invalid candidate span: [{self.start}, {self.end})")


# ── Extraction ───────────────────────────────────────────────────────────────

def extract_candidates(
    text: str,
    rule_id: str,
    vpd_patterns: Dict,
) -> List[Candidate]:
    """Extract all candidate positions for a single rule.

    Calls ``replay_pattern`` to find every occurrence of the rule's pattern in
    *text*, then wraps each hit as a :class:`Candidate` with
    ``is_positive=False`` (labeling is done separately).

    Args:
        text: Full document text (bytes-like or str).
        rule_id: TYPO rule identifier, e.g. ``"TYPO-001"``.
        vpd_patterns: Mapping from rule_id to pattern definition dicts.
            Must contain ``vpd_patterns[rule_id]["pattern"]``.

    Returns:
        List of candidates sorted by start position.
    """
    pattern_def = vpd_patterns[rule_id]["pattern"]
    spans = replay_pattern(text, rule_id, pattern_def)
    candidates = [
        Candidate(rule_id=rule_id, start=s, end=e)
        for s, e in spans
    ]
    candidates.sort(key=lambda c: c.start)
    logger.debug(
        "rule=%s  candidates=%d  text_len=%d", rule_id, len(candidates), len(text)
    )
    return candidates


def extract_all_candidates(
    text: str,
    vpd_patterns: Dict,
    rules: Optional[Set[str]] = None,
) -> List[Candidate]:
    """Extract candidates for multiple rules from a single document.

    Args:
        text: Full document text.
        vpd_patterns: Mapping from rule_id to pattern definition dicts.
        rules: Set of rule IDs to process.  Defaults to :data:`ALL_V2_RULES`.

    Returns:
        List of candidates sorted by ``(start, rule_id)``.
    """
    if rules is None:
        rules = ALL_V2_RULES

    all_candidates: List[Candidate] = []
    for rule_id in sorted(rules):
        if rule_id not in vpd_patterns:
            logger.warning("rule=%s not found in vpd_patterns, skipping", rule_id)
            continue
        all_candidates.extend(extract_candidates(text, rule_id, vpd_patterns))

    all_candidates.sort(key=lambda c: (c.start, c.rule_id))
    logger.info("total candidates=%d  rules_processed=%d", len(all_candidates), len(rules))
    return all_candidates


# ── Labeling ─────────────────────────────────────────────────────────────────

def label_candidates(
    candidates: List[Candidate],
    gold_spans: List[Union[Span, Dict]],
) -> List[Candidate]:
    """Label candidates against gold spans.

    For each candidate, if there is a matching ``(rule_id, start, end)`` in
    *gold_spans*, the returned copy has ``is_positive=True``.

    Args:
        candidates: Unlabeled candidate list.
        gold_spans: Ground-truth spans as :class:`~ml.data.label_spans.Span`
            instances or dicts with keys ``rule_id``, ``start``, ``end``.

    Returns:
        New list of :class:`Candidate` objects with ``is_positive`` set.
    """
    gold_set: Set[Tuple[str, int, int]] = set()
    for gs in gold_spans:
        if isinstance(gs, Span):
            gold_set.add((gs.rule_id, gs.start, gs.end))
        else:
            gold_set.add((gs["rule_id"], gs["start"], gs["end"]))

    labeled: List[Candidate] = []
    for c in candidates:
        positive = (c.rule_id, c.start, c.end) in gold_set
        labeled.append(replace(c, is_positive=positive))

    n_pos = sum(1 for c in labeled if c.is_positive)
    logger.info(
        "labeled %d candidates: %d positive, %d negative",
        len(labeled), n_pos, len(labeled) - n_pos,
    )
    return labeled


# ── Utility ──────────────────────────────────────────────────────────────────

def classify_rules() -> Tuple[Set[str], Set[str]]:
    """Return the (deterministic, ambiguous) rule partition.

    Returns:
        Tuple of ``(DETERMINISTIC_RULES, AMBIGUOUS_RULES)``.
    """
    return DETERMINISTIC_RULES, AMBIGUOUS_RULES


# ── CLI demo ─────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    logging.basicConfig(
        level=logging.DEBUG,
        format="%(asctime)s %(levelname)-8s %(name)s: %(message)s",
    )

    det, amb = classify_rules()
    print(f"Deterministic rules ({len(det)}): {sorted(det)}")
    print(f"Ambiguous rules     ({len(amb)}): {sorted(amb)}")
    print(f"All v2 rules        ({len(ALL_V2_RULES)}): {sorted(ALL_V2_RULES)}")

    # Minimal demo with a synthetic pattern dict
    sample_text = "Hello  world.  Two  spaces  here."
    sample_patterns = {
        "TYPO-001": {
            "pattern": {"family": "count_substring", "needle": "  "},
        },
    }

    candidates = extract_candidates(sample_text, "TYPO-001", sample_patterns)
    print(f"\nSample candidates for TYPO-001 in {sample_text!r}:")
    for c in candidates:
        print(f"  {c}")

    # Demo labeling
    gold = [Span(start=5, end=7, rule_id="TYPO-001")]
    labeled = label_candidates(candidates, gold)
    print("\nAfter labeling against gold spans:")
    for c in labeled:
        print(f"  {c}")
