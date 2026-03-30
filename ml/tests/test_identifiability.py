#!/usr/bin/env python3
"""Unit tests for the identifiability audit."""

import unittest

from ml.data.parser_state import compute_parser_state
from ml.scripts.identifiability_audit import (
    AMBIGUOUS_RULES,
    RULE_STATE_DEPS,
    _best_window,
    audit_identifiability,
    check_span_identifiability,
)


class TestFullyIdentifiable(unittest.TestCase):

    def test_fully_identifiable_no_math_dep(self):
        """TYPO-012 has no math dependency → always identifiable."""
        # TYPO-012 (digit+apostrophe) has RULE_STATE_DEPS = []
        self.assertEqual(RULE_STATE_DEPS["TYPO-012"], [])
        text = "The value 3's magnitude is large " + "x" * 500
        doc_state = compute_parser_state(text)
        result = check_span_identifiability(
            text, span_start=10, span_end=12,
            rule_id="TYPO-012", doc_state=doc_state, window_size=300,
        )
        self.assertTrue(result["identifiable"])
        self.assertEqual(result["reason"], "no_parser_state_dependency")


class TestMathMismatch(unittest.TestCase):

    def test_math_mismatch_across_window_boundary(self):
        """$ opens math 400 chars before span. 300-char window won't see it.
        Span should NOT be identifiable."""
        # Build: "$" + 400 chars of filler + anchor + closing "$"
        filler = "a" * 400
        anchor = "  "  # double space (TYPO-001 pattern)
        text = "$" + filler + anchor + "$"
        # anchor starts at position 401, ends at 403
        anchor_start = 1 + len(filler)
        anchor_end = anchor_start + len(anchor)

        doc_state = compute_parser_state(text)
        # Full doc: anchor is inside math
        self.assertTrue(doc_state.in_math[anchor_start])

        result = check_span_identifiability(
            text, anchor_start, anchor_end,
            rule_id="TYPO-001", doc_state=doc_state, window_size=300,
        )
        self.assertFalse(result["identifiable"])

    def test_math_within_window(self):
        """$ opens 100 chars before span (within 300-char window).
        Span IS identifiable."""
        filler = "a" * 100
        anchor = "  "
        text = "$" + filler + anchor + "$"
        anchor_start = 1 + len(filler)
        anchor_end = anchor_start + len(anchor)

        doc_state = compute_parser_state(text)
        self.assertTrue(doc_state.in_math[anchor_start])

        result = check_span_identifiability(
            text, anchor_start, anchor_end,
            rule_id="TYPO-001", doc_state=doc_state, window_size=300,
        )
        self.assertTrue(result["identifiable"])


class TestVerbatimBoundary(unittest.TestCase):

    def test_verbatim_across_boundary(self):
        r"""\begin{verbatim} 400 chars before \\ span. Window doesn't see it.
        NOT identifiable."""
        prefix = "\\begin{verbatim}\n"
        filler = "a" * 400
        anchor = "\\\\"  # literal backslash-backslash
        suffix = "\n\\end{verbatim}"
        text = prefix + filler + anchor + suffix
        anchor_start = len(prefix) + len(filler)
        anchor_end = anchor_start + len(anchor)

        doc_state = compute_parser_state(text)
        # Full doc: anchor is inside verbatim
        self.assertTrue(doc_state.in_verbatim[anchor_start])

        # TYPO-062 depends on in_verbatim
        result = check_span_identifiability(
            text, anchor_start, anchor_end,
            rule_id="TYPO-062", doc_state=doc_state, window_size=300,
        )
        self.assertFalse(result["identifiable"])


class TestShortDocument(unittest.TestCase):

    def test_short_document(self):
        """Document < 300 chars → window is entire doc → always identifiable."""
        text = "$x + y$"  # 7 chars, all within window
        doc_state = compute_parser_state(text)
        # anchor inside math at index 1
        result = check_span_identifiability(
            text, 1, 2,
            rule_id="TYPO-001", doc_state=doc_state, window_size=300,
        )
        self.assertTrue(result["identifiable"])
        self.assertEqual(result["reason"], "match")


class TestAuditIdentifiability(unittest.TestCase):

    def test_empty_docs_no_crash(self):
        """Empty document list → no errors, zero totals."""
        results = audit_identifiability([], window_size=300)
        self.assertEqual(results["overall"]["total"], 0)
        self.assertEqual(results["overall"]["identifiable"], 0)
        self.assertEqual(results["overall"]["not_identifiable"], 0)

    def test_per_rule_stats_structure(self):
        """Output has correct keys: total, identifiable, not_identifiable, pct_identifiable."""
        docs = [{
            "text": "hello  world",
            "spans": [
                {"rule_id": "TYPO-001", "start": 5, "end": 7},
            ],
        }]
        results = audit_identifiability(docs, window_size=300)
        for rule_id, stats in results["per_rule"].items():
            self.assertIn("total", stats)
            self.assertIn("identifiable", stats)
            self.assertIn("not_identifiable", stats)
            self.assertIn("pct_identifiable", stats)

    def test_overall_stats_sum(self):
        """Overall total = sum of per-rule totals."""
        # Build docs with spans for multiple ambiguous rules
        docs = [{
            "text": "hello  world <angle>",
            "spans": [
                {"rule_id": "TYPO-001", "start": 5, "end": 7},
                {"rule_id": "TYPO-052", "start": 13, "end": 14},
            ],
        }]
        results = audit_identifiability(docs, window_size=300)
        per_rule_total = sum(
            s["total"] for s in results["per_rule"].values()
        )
        self.assertEqual(results["overall"]["total"], per_rule_total)

        per_rule_ident = sum(
            s["identifiable"] for s in results["per_rule"].values()
        )
        self.assertEqual(results["overall"]["identifiable"], per_rule_ident)


class TestBestWindow(unittest.TestCase):

    def test_best_window_centering(self):
        """_best_window(150, 160, 1000, 300) centers span in window."""
        ws, we = _best_window(150, 160, 1000, 300)
        self.assertEqual(we - ws, 300)
        # Span midpoint = 155; window should center around it
        span_mid = 155
        window_mid = (ws + we) / 2
        self.assertAlmostEqual(window_mid, span_mid, delta=5)
        # Span must be inside the window
        self.assertLessEqual(ws, 150)
        self.assertGreaterEqual(we, 160)

    def test_best_window_near_start(self):
        """Span near position 0 → window starts at 0."""
        ws, we = _best_window(5, 10, 1000, 300)
        self.assertEqual(ws, 0)
        self.assertEqual(we, 300)

    def test_best_window_near_end(self):
        """Span near end → window ends at doc_len."""
        ws, we = _best_window(990, 995, 1000, 300)
        self.assertEqual(we, 1000)
        self.assertEqual(ws, 700)

    def test_best_window_short_doc(self):
        """Document shorter than window → returns (0, doc_len)."""
        ws, we = _best_window(10, 20, 100, 300)
        self.assertEqual(ws, 0)
        self.assertEqual(we, 100)


if __name__ == "__main__":
    unittest.main()
