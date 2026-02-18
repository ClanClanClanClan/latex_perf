#!/usr/bin/env python3
"""Unit tests for evaluation harness."""

import unittest
from ml.evaluate import (
    bio_to_spans,
    compute_span_metrics,
    compute_token_metrics,
    validate_bio_sequence,
    evaluate,
)


class TestBIOToSpans(unittest.TestCase):
    def test_single_span(self):
        tags = ["O", "B-X", "I-X", "O"]
        spans = bio_to_spans(tags)
        self.assertEqual(len(spans), 1)
        self.assertEqual(spans[0], ("X", 1, 3))

    def test_multiple_spans(self):
        tags = ["B-A", "I-A", "O", "B-B", "O"]
        spans = bio_to_spans(tags)
        self.assertEqual(len(spans), 2)
        self.assertEqual(spans[0], ("A", 0, 2))
        self.assertEqual(spans[1], ("B", 3, 4))

    def test_adjacent_spans(self):
        tags = ["B-A", "B-B", "O"]
        spans = bio_to_spans(tags)
        self.assertEqual(len(spans), 2)
        self.assertEqual(spans[0], ("A", 0, 1))
        self.assertEqual(spans[1], ("B", 1, 2))

    def test_all_outside(self):
        tags = ["O", "O", "O"]
        spans = bio_to_spans(tags)
        self.assertEqual(len(spans), 0)

    def test_span_at_end(self):
        tags = ["O", "B-X", "I-X"]
        spans = bio_to_spans(tags)
        self.assertEqual(len(spans), 1)
        self.assertEqual(spans[0], ("X", 1, 3))


class TestSpanMetrics(unittest.TestCase):
    def test_perfect_match(self):
        gold = [["O", "B-X", "I-X", "O"]]
        pred = [["O", "B-X", "I-X", "O"]]
        metrics = compute_span_metrics(gold, pred)
        self.assertAlmostEqual(metrics["overall_f1"], 1.0)
        self.assertAlmostEqual(metrics["overall_precision"], 1.0)
        self.assertAlmostEqual(metrics["overall_recall"], 1.0)

    def test_no_predictions(self):
        gold = [["O", "B-X", "I-X", "O"]]
        pred = [["O", "O", "O", "O"]]
        metrics = compute_span_metrics(gold, pred)
        self.assertAlmostEqual(metrics["overall_f1"], 0.0)
        self.assertAlmostEqual(metrics["overall_recall"], 0.0)

    def test_false_positives(self):
        gold = [["O", "O", "O", "O"]]
        pred = [["O", "B-X", "O", "O"]]
        metrics = compute_span_metrics(gold, pred)
        self.assertAlmostEqual(metrics["overall_precision"], 0.0)
        self.assertEqual(metrics["total_fp"], 1)

    def test_partial_match(self):
        gold = [["B-X", "I-X", "I-X", "O"]]
        pred = [["B-X", "I-X", "O", "O"]]
        metrics = compute_span_metrics(gold, pred)
        # Different span boundaries → no exact match
        self.assertAlmostEqual(metrics["overall_f1"], 0.0)


class TestTokenMetrics(unittest.TestCase):
    def test_perfect(self):
        gold = [["O", "B-X", "O"]]
        pred = [["O", "B-X", "O"]]
        metrics = compute_token_metrics(gold, pred)
        self.assertAlmostEqual(metrics["token_f1"], 1.0)

    def test_all_negative(self):
        gold = [["O", "O", "O"]]
        pred = [["O", "O", "O"]]
        metrics = compute_token_metrics(gold, pred)
        # No positives, so F1 is 0 (undefined)
        self.assertAlmostEqual(metrics["token_f1"], 0.0)


class TestBIOValidation(unittest.TestCase):
    def test_valid(self):
        self.assertTrue(validate_bio_sequence(["O", "B-X", "I-X", "O"]))
        self.assertTrue(validate_bio_sequence(["O", "O", "O"]))
        self.assertTrue(validate_bio_sequence(["B-X", "I-X"]))

    def test_invalid_orphan_i(self):
        self.assertFalse(validate_bio_sequence(["I-X", "O"]))

    def test_invalid_mismatched_i(self):
        self.assertFalse(validate_bio_sequence(["B-X", "I-Y"]))


class TestEvaluate(unittest.TestCase):
    def test_full_evaluation(self):
        gold = [["O", "B-X", "I-X", "O"]]
        pred = [["O", "B-X", "I-X", "O"]]
        results = evaluate(gold, pred, "test_model", 42)
        self.assertAlmostEqual(results["overall_f1"], 1.0)
        self.assertAlmostEqual(results["delta"], 0.0)
        self.assertEqual(results["model"], "test_model")
        self.assertEqual(results["seed"], 42)
        self.assertIn("timestamp", results)


if __name__ == "__main__":
    unittest.main()
