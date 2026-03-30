#!/usr/bin/env python3
"""Unit tests for the candidate dataset builder."""

import json
import os
import tempfile
import unittest

from ml.data.build_candidate_dataset import (
    build_candidate_dataset,
    build_candidate_record,
    build_context,
)
from ml.data.candidate_extractor import AMBIGUOUS_RULES, Candidate
from ml.data.label_spans import Span
from ml.data.parser_state import compute_parser_state


class TestBuildContextSize(unittest.TestCase):
    """build_context must always return exactly context_size bytes."""

    def test_context_window_exact_size(self):
        """Output bytes list is ALWAYS exactly 128 long, regardless of input."""
        cases = [
            ("x", 0, 1),                       # 1-byte doc
            ("hello world", 0, 5),              # short doc
            ("a" * 1000, 400, 410),             # long doc, middle anchor
            ("a" * 1000, 0, 1),                 # anchor at start
            ("a" * 1000, 999, 1000),            # anchor at end
            ("a" * 50, 10, 40),                 # doc shorter than 128
        ]
        for text, start, end in cases:
            with self.subTest(text_len=len(text), start=start, end=end):
                ctx = build_context(text, start, end, context_size=128)
                self.assertEqual(
                    len(ctx["bytes"]), 128,
                    f"Expected 128 bytes for text_len={len(text)}, "
                    f"start={start}, end={end}, got {len(ctx['bytes'])}",
                )


class TestBuildContextCentering(unittest.TestCase):
    """Anchor centering within the context window."""

    def test_context_centering_middle(self):
        """Anchor in the middle of a long text is approximately centered."""
        text = "a" * 2000
        ctx = build_context(text, 1000, 1010, context_size=128)
        anchor_mid = (ctx["anchor_start"] + ctx["anchor_end"]) / 2
        window_mid = 128 / 2
        # The anchor midpoint should be within a few bytes of center.
        self.assertAlmostEqual(anchor_mid, window_mid, delta=10)

    def test_context_at_document_start(self):
        """Anchor at position 0 → left-padded with zeros when doc < 128."""
        text = "short"
        ctx = build_context(text, 0, 1, context_size=128)
        self.assertEqual(len(ctx["bytes"]), 128)
        # anchor_start must be 0 (starts at beginning)
        self.assertEqual(ctx["anchor_start"], 0)
        # Trailing bytes should be zero-padded
        text_bytes = text.encode("utf-8")
        for i in range(len(text_bytes), 128):
            self.assertEqual(ctx["bytes"][i], 0, f"byte {i} should be zero pad")

    def test_context_at_document_end(self):
        """Anchor at end of text → right-padded with zeros when doc < 128."""
        text = "abcdef"
        ctx = build_context(text, 5, 6, context_size=128)
        self.assertEqual(len(ctx["bytes"]), 128)
        # The anchor byte should appear somewhere in the window
        self.assertEqual(
            bytes(ctx["bytes"][ctx["anchor_start"]:ctx["anchor_end"]]),
            b"f",
        )


class TestBuildContextAnchorBytes(unittest.TestCase):
    """Verify bytes[anchor_start:anchor_end] matches text[start:end]."""

    def test_anchor_bytes_match_text(self):
        """Extracted anchor bytes decode to the original anchor text."""
        text = "The quick brown fox jumps over the lazy dog."
        start, end = 10, 15  # "brown"
        ctx = build_context(text, start, end, context_size=128)
        anchor_bytes = bytes(ctx["bytes"][ctx["anchor_start"]:ctx["anchor_end"]])
        self.assertEqual(anchor_bytes.decode("utf-8"), "brown")

    def test_unicode_anchor_bytes(self):
        """Multi-byte UTF-8 chars (accented, CJK) → byte offsets correct."""
        # e-acute is 2 bytes; CJK chars are 3 bytes each
        text = "abc\u00e9def\u4e16\u754c"  # "abcédef世界"
        # Anchor the accented char: text[3:4] = "é"
        ctx = build_context(text, 3, 4, context_size=128)
        anchor_bytes = bytes(ctx["bytes"][ctx["anchor_start"]:ctx["anchor_end"]])
        self.assertEqual(anchor_bytes.decode("utf-8"), "\u00e9")

        # Anchor the CJK chars: text[7:9] = "世界"
        ctx2 = build_context(text, 7, 9, context_size=128)
        anchor_bytes2 = bytes(ctx2["bytes"][ctx2["anchor_start"]:ctx2["anchor_end"]])
        self.assertEqual(anchor_bytes2.decode("utf-8"), "\u4e16\u754c")


class TestBuildContextEdgeCases(unittest.TestCase):

    def test_anchor_longer_than_context(self):
        """Anchor > 128 bytes → context truncated to anchor portion."""
        text = "x" * 200
        ctx = build_context(text, 0, 200, context_size=128)
        self.assertEqual(len(ctx["bytes"]), 128)
        # anchor_start should be 0 and anchor_end capped at 128
        self.assertEqual(ctx["anchor_start"], 0)
        self.assertEqual(ctx["anchor_end"], min(200, 128))


class TestParserFeaturesInRecord(unittest.TestCase):
    """build_candidate_record should propagate parser state features."""

    def test_parser_features_at_anchor(self):
        """in_math=True when anchor is inside $...$."""
        text = "text $x + y$ more"
        pstate = compute_parser_state(text)
        # "x" is at index 6, inside $...$
        cand = Candidate(rule_id="TYPO-001", start=6, end=7, is_positive=False)
        rec = build_candidate_record(text, cand, pstate)
        self.assertTrue(rec["in_math"])

    def test_parser_features_verbatim(self):
        r"""in_verbatim=True when anchor is inside \verb|...|."""
        text = r"text \verb|code here| more"
        pstate = compute_parser_state(text)
        # "code" starts after \verb|, find its position
        idx = text.index("code")
        cand = Candidate(rule_id="TYPO-062", start=idx, end=idx + 4, is_positive=False)
        rec = build_candidate_record(text, cand, pstate)
        self.assertTrue(rec["in_verbatim"])

    def test_env_depth_propagated(self):
        r"""env_depth=2 when inside nested \begin{itemize}\begin{enumerate}."""
        text = (
            "\\begin{itemize}\n"
            "\\begin{enumerate}\n"
            "deep content\n"
            "\\end{enumerate}\n"
            "\\end{itemize}"
        )
        pstate = compute_parser_state(text)
        idx = text.index("deep content")
        cand = Candidate(rule_id="TYPO-001", start=idx, end=idx + 4, is_positive=False)
        rec = build_candidate_record(text, cand, pstate)
        self.assertEqual(rec["env_depth"], 2)


class TestCandidateLabeling(unittest.TestCase):
    """build_candidate_record label field matches is_positive."""

    def test_positive_label(self):
        """Candidate with is_positive=True → record['label']=1."""
        text = "hello world"
        pstate = compute_parser_state(text)
        cand = Candidate(rule_id="TYPO-001", start=0, end=5, is_positive=True)
        rec = build_candidate_record(text, cand, pstate)
        self.assertEqual(rec["label"], 1)

    def test_negative_label(self):
        """Candidate with is_positive=False → record['label']=0."""
        text = "hello world"
        pstate = compute_parser_state(text)
        cand = Candidate(rule_id="TYPO-001", start=0, end=5, is_positive=False)
        rec = build_candidate_record(text, cand, pstate)
        self.assertEqual(rec["label"], 0)


class TestFullPipeline(unittest.TestCase):
    """Integration tests for build_candidate_dataset."""

    def _make_vpd_patterns(self):
        """Minimal VPD patterns dict for testing with double-space rule."""
        return {
            "TYPO-001": {
                "pattern": {"family": "count_substring", "needle": "  "},
            },
        }

    def test_full_pipeline_small_doc(self):
        """Build dataset from a small labeled doc → correct number of records."""
        text = "hello  world  here"
        # Two double-space occurrences at positions 5 and 12
        labeled_docs = [{
            "text": text,
            "spans": [
                {"rule_id": "TYPO-001", "start": 5, "end": 7},
            ],
            "file": "test.tex",
        }]
        vpd = self._make_vpd_patterns()
        records = build_candidate_dataset(
            labeled_docs, vpd, rules={"TYPO-001"}, context_size=128,
        )
        # Should have 2 candidates (two double-spaces), one labeled positive
        self.assertEqual(len(records), 2)
        labels = {r["doc_offset"]: r["label"] for r in records}
        self.assertEqual(labels[5], 1)
        self.assertEqual(labels[12], 0)

    def test_empty_document(self):
        """Document with no spans → all candidates get label=0."""
        text = "hello  world  here"
        labeled_docs = [{
            "text": text,
            "spans": [],
            "file": "empty.tex",
        }]
        vpd = self._make_vpd_patterns()
        records = build_candidate_dataset(
            labeled_docs, vpd, rules={"TYPO-001"}, context_size=128,
        )
        for rec in records:
            self.assertEqual(rec["label"], 0)

    def test_multiple_rules_in_doc(self):
        """Document with violations of multiple rules → records for each."""
        text = "hello--world and a---dash"
        vpd = {
            "TYPO-002": {
                "pattern": {"family": "count_substring", "needle": "--"},
            },
            "TYPO-003": {
                "pattern": {"family": "count_substring", "needle": "---"},
            },
        }
        labeled_docs = [{
            "text": text,
            "spans": [
                {"rule_id": "TYPO-002", "start": 5, "end": 7},
                {"rule_id": "TYPO-003", "start": 18, "end": 21},
            ],
            "file": "multi.tex",
        }]
        records = build_candidate_dataset(
            labeled_docs, vpd,
            rules={"TYPO-002", "TYPO-003"},
            context_size=128,
        )
        rule_ids = {r["rule_id"] for r in records}
        self.assertIn("TYPO-002", rule_ids)
        self.assertIn("TYPO-003", rule_ids)


class TestJSONLRoundtrip(unittest.TestCase):
    """Verify records survive JSONL serialization."""

    def test_jsonl_roundtrip(self):
        """Write records to JSONL, reload, verify all fields match."""
        text = "hello  world"
        pstate = compute_parser_state(text)
        cand = Candidate(rule_id="TYPO-001", start=5, end=7, is_positive=True)
        original = build_candidate_record(text, cand, pstate, file_path="test.tex")

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".jsonl", delete=False, encoding="utf-8",
        ) as f:
            f.write(json.dumps(original) + "\n")
            tmp_path = f.name

        try:
            with open(tmp_path, "r", encoding="utf-8") as f:
                reloaded = json.loads(f.readline())

            # Every key in the original should match after roundtrip.
            for key in original:
                self.assertEqual(
                    original[key], reloaded[key],
                    f"Mismatch on key {key!r}: {original[key]!r} != {reloaded[key]!r}",
                )
        finally:
            os.unlink(tmp_path)


if __name__ == "__main__":
    unittest.main()
