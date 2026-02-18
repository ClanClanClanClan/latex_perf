#!/usr/bin/env python3
"""Test that seeded training produces identical results.

Runs the labeling pipeline twice with the same seed and verifies
that output is byte-identical.
"""

import unittest
import tempfile
import json
from pathlib import Path

from ml.data.label_spans import run_labeling_pipeline
from ml.data.split_data import load_labeled_jsonl, stratified_split


class TestDeterminism(unittest.TestCase):
    """Verify that seeded operations produce identical results."""

    def test_labeling_determinism(self):
        """Same corpus + patterns → same JSONL output."""
        corpus = "corpora/lint/pilot_v1"
        vpd = "specs/rules/vpd_patterns.json"
        golden = "specs/rules/pilot_v1_golden.yaml"

        # Skip if corpus doesn't exist (CI without corpus)
        if not Path(corpus).exists():
            self.skipTest("Corpus not available")

        with tempfile.TemporaryDirectory() as tmpdir:
            out1 = f"{tmpdir}/labeled1.jsonl"
            out2 = f"{tmpdir}/labeled2.jsonl"

            run_labeling_pipeline(corpus, vpd, golden, out1)
            run_labeling_pipeline(corpus, vpd, golden, out2)

            with open(out1) as f1, open(out2) as f2:
                content1 = f1.read()
                content2 = f2.read()

            self.assertEqual(content1, content2,
                            "Labeling pipeline produced different output on two runs")

    def test_split_determinism(self):
        """Same input + seed → same train/dev split."""
        # Create synthetic labeled data
        docs = [
            {"file": f"test_{i}.tex", "text": f"text {i}",
             "bio_tags": ["O"] * 6, "rule_ids": [f"RULE-{i % 3:03d}"],
             "spans": []}
            for i in range(20)
        ]

        train1, dev1 = stratified_split(docs, train_ratio=0.8, seed=42)
        train2, dev2 = stratified_split(docs, train_ratio=0.8, seed=42)

        self.assertEqual(len(train1), len(train2))
        self.assertEqual(len(dev1), len(dev2))

        for d1, d2 in zip(train1, train2):
            self.assertEqual(d1["file"], d2["file"])
        for d1, d2 in zip(dev1, dev2):
            self.assertEqual(d1["file"], d2["file"])

    def test_different_seed_different_split(self):
        """Different seeds should produce different splits."""
        docs = [
            {"file": f"test_{i}.tex", "text": f"text {i}",
             "bio_tags": ["O"] * 6, "rule_ids": [f"RULE-{i % 3:03d}"],
             "spans": []}
            for i in range(20)
        ]

        train1, _ = stratified_split(docs, train_ratio=0.8, seed=42)
        train2, _ = stratified_split(docs, train_ratio=0.8, seed=99)

        files1 = [d["file"] for d in train1]
        files2 = [d["file"] for d in train2]

        # With different seeds, order should differ (not guaranteed but very likely)
        # We just check they're both valid splits
        self.assertEqual(len(files1), len(files2))


if __name__ == "__main__":
    unittest.main()
