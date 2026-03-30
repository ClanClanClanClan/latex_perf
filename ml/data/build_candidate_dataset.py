#!/usr/bin/env python3
"""Build the candidate classification dataset for the v2 pipeline.

For each candidate anchor in a labeled document, extracts a 128-byte context
window centered on the anchor, plus parser-state features (in_math, in_verbatim,
in_comment, env_depth).  Outputs JSONL records compatible with the Colab training
notebook.

Usage:
    python -m ml.data.build_candidate_dataset \
        --input  ml/data/labeled_spans.jsonl \
        --vpd    ml/data/vpd_patterns.yaml \
        --output ml/data/candidate_dataset.jsonl \
        [--rules TYPO-001,TYPO-005,...] \
        [--context-size 128] \
        [--verbose]
"""

import argparse
import json
import logging
from collections import Counter
from pathlib import Path
from typing import Dict, List, Optional, Set

import yaml

from ml.data.candidate_extractor import (
    ALL_V2_RULES,
    AMBIGUOUS_RULES,
    DETERMINISTIC_RULES,
    Candidate,
    extract_all_candidates,
    label_candidates,
)
from ml.data.label_spans import Span
from ml.data.parser_state import ParserState, compute_parser_state
from ml.data.split_data import load_labeled_jsonl, write_jsonl

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Context-window construction
# ---------------------------------------------------------------------------

def build_context(
    text: str,
    start: int,
    end: int,
    context_size: int = 128,
) -> Dict:
    """Extract a byte-level context window centered on a character-offset anchor.

    Args:
        text: Full document text (str).
        start: Anchor start in *character* offsets.
        end: Anchor end in *character* offsets.
        context_size: Desired byte-length of the returned context (default 128).

    Returns:
        dict with keys:
          - ``bytes``:  List[int] of length exactly ``context_size`` (zero-padded).
          - ``anchor_start``: int index into ``bytes`` where the anchor begins.
          - ``anchor_end``:   int index into ``bytes`` where the anchor ends.

        Invariant: ``bytes[anchor_start:anchor_end]`` equals the UTF-8 encoding
        of ``text[start:end]``.
    """
    # Encode the full text to UTF-8 and build a char→byte offset map.
    text_bytes = text.encode("utf-8")

    # Build character-to-byte offset table.  char_to_byte[i] gives the byte
    # offset where character i starts; char_to_byte[len(text)] == len(text_bytes).
    char_to_byte: List[int] = []
    byte_idx = 0
    for ch in text:
        char_to_byte.append(byte_idx)
        byte_idx += len(ch.encode("utf-8"))
    char_to_byte.append(byte_idx)  # sentinel for end-of-text

    anchor_byte_start = char_to_byte[start]
    anchor_byte_end = char_to_byte[end]
    anchor_byte_len = anchor_byte_end - anchor_byte_start

    # Edge case: anchor longer than context_size → truncate context to anchor.
    if anchor_byte_len >= context_size:
        raw = list(text_bytes[anchor_byte_start : anchor_byte_start + context_size])
        return {
            "bytes": raw,
            "anchor_start": 0,
            "anchor_end": min(anchor_byte_len, context_size),
        }

    # Center the anchor in the context window.
    padding_total = context_size - anchor_byte_len
    pad_before = padding_total // 2
    pad_after = padding_total - pad_before

    window_byte_start = anchor_byte_start - pad_before
    window_byte_end = anchor_byte_end + pad_after

    # Clamp to document boundaries.
    if window_byte_start < 0:
        window_byte_end -= window_byte_start  # shift right
        window_byte_start = 0
    if window_byte_end > len(text_bytes):
        window_byte_start -= window_byte_end - len(text_bytes)  # shift left
        window_byte_end = len(text_bytes)
        if window_byte_start < 0:
            window_byte_start = 0

    raw = list(text_bytes[window_byte_start:window_byte_end])

    # Compute anchor position within the extracted window.
    a_start = anchor_byte_start - window_byte_start
    a_end = anchor_byte_end - window_byte_start

    # Zero-pad to exact context_size if the document is shorter.
    if len(raw) < context_size:
        deficit = context_size - len(raw)
        # Prefer padding at the end so anchor offsets stay valid.
        raw.extend([0] * deficit)

    return {
        "bytes": raw,
        "anchor_start": a_start,
        "anchor_end": a_end,
    }


# ---------------------------------------------------------------------------
# Single-record builder
# ---------------------------------------------------------------------------

def build_candidate_record(
    text: str,
    candidate: Candidate,
    parser_state: ParserState,
    file_path: str = "",
) -> Dict:
    """Build a single dataset record combining context window + features.

    Args:
        text: Full document text.
        candidate: A ``Candidate`` from the extractor (has rule_id, start, end, label).
        parser_state: Pre-computed per-character parser state for the document.
        file_path: Optional source file path for traceability.

    Returns:
        dict suitable for JSONL serialization:
          - rule_id (str)
          - label (int, 0 or 1)
          - bytes (List[int], length == context_size)
          - anchor_start, anchor_end (int)
          - in_math, in_verbatim, in_comment (bool)
          - env_depth (int)
          - file (str)
          - doc_offset (int)
    """
    ctx = build_context(text, candidate.start, candidate.end)

    # Sample parser features at anchor START position.
    pos = candidate.start
    # Guard against out-of-range (should not happen in practice).
    if pos >= len(parser_state):
        pos = max(0, len(parser_state) - 1)

    return {
        "rule_id": candidate.rule_id,
        "label": int(candidate.is_positive),
        "bytes": ctx["bytes"],
        "anchor_start": ctx["anchor_start"],
        "anchor_end": ctx["anchor_end"],
        "in_math": bool(parser_state.in_math[pos]) if len(parser_state) > 0 else False,
        "in_verbatim": bool(parser_state.in_verbatim[pos]) if len(parser_state) > 0 else False,
        "in_comment": bool(parser_state.in_comment[pos]) if len(parser_state) > 0 else False,
        "env_depth": int(parser_state.env_depth[pos]) if len(parser_state) > 0 else 0,
        "file": file_path,
        "doc_offset": candidate.start,
    }


# ---------------------------------------------------------------------------
# Batch dataset builder
# ---------------------------------------------------------------------------

def build_candidate_dataset(
    labeled_docs: List[Dict],
    vpd_patterns: Dict,
    rules: Optional[Set[str]] = None,
    context_size: int = 128,
) -> List[Dict]:
    """Build the full candidate-classification dataset from labeled documents.

    For each document:
      1. Extract all candidate anchors via deterministic replay.
      2. Label each candidate against the gold spans.
      3. Compute per-character parser state.
      4. Build a context-window record for every candidate.

    Args:
        labeled_docs: List of document dicts (as loaded by ``load_labeled_jsonl``).
            Each dict must have ``text``, ``spans``, and ``file`` keys.
        vpd_patterns: VPD pattern configuration dict (loaded from YAML).
        rules: If given, restrict to this set of rule IDs.  Default: all v2 rules.
        context_size: Byte-length of each context window (default 128).

    Returns:
        List of dataset-record dicts ready for JSONL serialization.
    """
    if rules is None:
        rules = ALL_V2_RULES

    records: List[Dict] = []

    for doc_idx, doc in enumerate(labeled_docs):
        text = doc["text"]
        file_path = doc.get("file", "")

        # Reconstruct gold spans.
        gold_spans = [
            Span(start=s["start"], end=s["end"], rule_id=s["rule_id"])
            for s in doc.get("spans", [])
        ]

        # Extract candidates and assign labels against gold spans.
        candidates = extract_all_candidates(text, vpd_patterns, rules=rules)
        candidates = label_candidates(candidates, gold_spans)

        # Compute parser state once per document.
        pstate = compute_parser_state(text)

        for cand in candidates:
            rec = build_candidate_record(
                text, cand, pstate, file_path=file_path,
            )
            # Override context_size if non-default (rebuild context).
            if context_size != 128:
                ctx = build_context(text, cand.start, cand.end, context_size)
                rec["bytes"] = ctx["bytes"]
                rec["anchor_start"] = ctx["anchor_start"]
                rec["anchor_end"] = ctx["anchor_end"]
            records.append(rec)

        if (doc_idx + 1) % 100 == 0:
            logger.info(
                "Processed %d / %d docs (%d candidates so far)",
                doc_idx + 1,
                len(labeled_docs),
                len(records),
            )

    logger.info(
        "Dataset complete: %d documents -> %d candidate records",
        len(labeled_docs),
        len(records),
    )
    return records


# ---------------------------------------------------------------------------
# Full pipeline: load -> build -> write + stats
# ---------------------------------------------------------------------------

def build_and_write(
    input_jsonl: str,
    vpd_patterns_path: str,
    output_path: str,
    rules: Optional[Set[str]] = None,
    context_size: int = 128,
) -> Dict:
    """End-to-end pipeline: load docs, build dataset, write JSONL, return stats.

    Args:
        input_jsonl: Path to labeled-documents JSONL (from ``label_spans``).
        vpd_patterns_path: Path to VPD pattern YAML config.
        output_path: Destination JSONL path.
        rules: Optional rule-ID filter.
        context_size: Byte-length of context windows.

    Returns:
        dict with summary statistics:
          - total: int
          - positives: int
          - negatives: int
          - per_rule: dict mapping rule_id -> {total, pos, neg}
    """
    logger.info("Loading labeled documents from %s", input_jsonl)
    docs = load_labeled_jsonl(input_jsonl)
    logger.info("Loaded %d documents", len(docs))

    logger.info("Loading VPD patterns from %s", vpd_patterns_path)
    with open(vpd_patterns_path, "r", encoding="utf-8") as f:
        vpd_patterns = yaml.safe_load(f)

    logger.info("Building candidate dataset (context_size=%d) ...", context_size)
    records = build_candidate_dataset(
        docs, vpd_patterns, rules=rules, context_size=context_size,
    )

    logger.info("Writing %d records to %s", len(records), output_path)
    write_jsonl(records, output_path)

    # Compute statistics.
    total = len(records)
    positives = sum(1 for r in records if r["label"] == 1)
    negatives = total - positives

    per_rule: Dict[str, Dict[str, int]] = {}
    for r in records:
        rid = r["rule_id"]
        if rid not in per_rule:
            per_rule[rid] = {"total": 0, "pos": 0, "neg": 0}
        per_rule[rid]["total"] += 1
        if r["label"] == 1:
            per_rule[rid]["pos"] += 1
        else:
            per_rule[rid]["neg"] += 1

    stats = {
        "total": total,
        "positives": positives,
        "negatives": negatives,
        "per_rule": per_rule,
    }

    logger.info("Stats: %d total, %d pos, %d neg", total, positives, negatives)
    for rid in sorted(per_rule):
        s = per_rule[rid]
        logger.info(
            "  %s: %d total (%d pos, %d neg)",
            rid, s["total"], s["pos"], s["neg"],
        )

    return stats


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build candidate-classification dataset (v2 pipeline).",
    )
    parser.add_argument(
        "--input", default="ml/data/labeled_spans.jsonl",
        help="Input labeled-documents JSONL (default: ml/data/labeled_spans.jsonl)",
    )
    parser.add_argument(
        "--vpd", default="ml/data/vpd_patterns.yaml",
        help="VPD pattern config YAML (default: ml/data/vpd_patterns.yaml)",
    )
    parser.add_argument(
        "--output", default="ml/data/candidate_dataset.jsonl",
        help="Output JSONL path (default: ml/data/candidate_dataset.jsonl)",
    )
    parser.add_argument(
        "--rules", default=None,
        help="Comma-separated rule IDs to include (default: all v2 rules)",
    )
    parser.add_argument(
        "--context-size", type=int, default=128,
        help="Byte-length of context windows (default: 128)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true",
        help="Enable debug logging",
    )
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    rule_set: Optional[Set[str]] = None
    if args.rules:
        rule_set = set(args.rules.split(","))
        logger.info("Filtering to rules: %s", rule_set)

    stats = build_and_write(
        input_jsonl=args.input,
        vpd_patterns_path=args.vpd,
        output_path=args.output,
        rules=rule_set,
        context_size=args.context_size,
    )

    logger.info("Done. Summary: %s", json.dumps(
        {k: v for k, v in stats.items() if k != "per_rule"},
        indent=2,
    ))


if __name__ == "__main__":
    main()
