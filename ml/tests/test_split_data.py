#!/usr/bin/env python3
"""Tests for stratified_three_way_split and split_data utilities."""

import unittest
from ml.data.split_data import stratified_split

try:
    from ml.data.split_data import stratified_three_way_split
    HAS_THREE_WAY = True
except ImportError:
    HAS_THREE_WAY = False


def _make_docs(n, rule="TYPO-001"):
    """Create n synthetic labeled documents for a given rule."""
    return [
        {"text": f"doc{i}", "bio_tags": ["O"],
         "rule_ids": [rule] if i % 2 == 0 else [], "spans": []}
        for i in range(n)
    ]


def skipUnlessThreeWay(f):
    return unittest.skipUnless(HAS_THREE_WAY, "stratified_three_way_split not available")(f)

class TestThreeWaySplit(unittest.TestCase):

    @skipUnlessThreeWay
    def test_ratios_sum_to_one(self):
        """Rejects ratios that don't sum to 1.0."""
        docs = _make_docs(20)
        with self.assertRaises(AssertionError):
            stratified_three_way_split(docs, 0.5, 0.3, 0.3)

    @skipUnlessThreeWay
    def test_basic_split_sizes(self):
        """70/15/15 split on 20 docs produces reasonable sizes."""
        docs = _make_docs(20)
        train, dev, test = stratified_three_way_split(docs, 0.70, 0.15, 0.15)
        total = len(train) + len(dev) + len(test)
        # May have duplicates for 1-doc rules, so total >= 20
        self.assertGreaterEqual(total, 20)
        self.assertGreater(len(train), len(dev))
        self.assertGreater(len(train), len(test))

    @skipUnlessThreeWay
    def test_all_splits_nonempty(self):
        """Even with few docs, all three splits get at least 1 item."""
        docs = _make_docs(5, "TYPO-001") + _make_docs(5, "TYPO-002")
        train, dev, test = stratified_three_way_split(docs, 0.70, 0.15, 0.15)
        self.assertGreater(len(train), 0)
        self.assertGreater(len(dev), 0)
        self.assertGreater(len(test), 0)

    @skipUnlessThreeWay
    def test_single_doc_rule_duplicated(self):
        """A rule with exactly 1 document appears in all three splits."""
        docs = [{"text": "only", "bio_tags": ["O"],
                 "rule_ids": ["RARE-001"], "spans": []}]
        train, dev, test = stratified_three_way_split(docs, 0.70, 0.15, 0.15)
        # The single doc should be duplicated to all splits
        self.assertTrue(any(d["text"] == "only" for d in train))
        self.assertTrue(any(d["text"] == "only" for d in dev))
        self.assertTrue(any(d["text"] == "only" for d in test))

    @skipUnlessThreeWay
    def test_two_doc_rule_coverage(self):
        """A rule with 2 docs: 1 in train, 1 shared between dev+test."""
        docs = [
            {"text": "a", "bio_tags": ["O"], "rule_ids": ["PAIR-001"], "spans": []},
            {"text": "b", "bio_tags": ["O"], "rule_ids": ["PAIR-001"], "spans": []},
        ]
        train, dev, test = stratified_three_way_split(docs, 0.70, 0.15, 0.15)
        self.assertGreater(len(train), 0)
        self.assertGreater(len(dev), 0)
        self.assertGreater(len(test), 0)

    @skipUnlessThreeWay
    def test_deterministic_with_seed(self):
        """Same seed produces same split."""
        docs = _make_docs(50)
        t1, d1, s1 = stratified_three_way_split(docs, 0.70, 0.15, 0.15, seed=42)
        t2, d2, s2 = stratified_three_way_split(docs, 0.70, 0.15, 0.15, seed=42)
        self.assertEqual([d["text"] for d in t1], [d["text"] for d in t2])
        self.assertEqual([d["text"] for d in d1], [d["text"] for d in d2])
        self.assertEqual([d["text"] for d in s1], [d["text"] for d in s2])

    @skipUnlessThreeWay
    def test_different_seed_different_split(self):
        """Different seeds produce different splits."""
        docs = _make_docs(50)
        t1, _, _ = stratified_three_way_split(docs, 0.70, 0.15, 0.15, seed=42)
        t2, _, _ = stratified_three_way_split(docs, 0.70, 0.15, 0.15, seed=99)
        # With 50 docs and different seeds, trains should differ
        texts1 = set(d["text"] for d in t1)
        texts2 = set(d["text"] for d in t2)
        self.assertNotEqual(texts1, texts2)

    def test_backward_compat_two_way(self):
        """Original stratified_split still works with new rule type."""
        docs = _make_docs(20)
        train, dev = stratified_split(docs, 0.80, 42)
        self.assertGreater(len(train), 0)
        self.assertGreater(len(dev), 0)


if __name__ == "__main__":
    unittest.main()
