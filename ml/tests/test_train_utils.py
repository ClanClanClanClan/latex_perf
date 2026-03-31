#!/usr/bin/env python3
"""Tests for CPU-testable utilities in train_byte_classifier."""

import unittest

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

if HAS_TORCH:
    from ml.models.train_byte_classifier import CandidateDataset, evaluate_candidates
    from ml.models.byte_classifier import build_byte_classifier, RULE_TO_IDX


def skipUnlessTorch(test_func):
    return unittest.skipUnless(HAS_TORCH, "torch not available")(test_func)


SAMPLE_RECORDS = [
    {"rule_id": "TYPO-001", "label": 1, "bytes": [65] * 128,
     "anchor_start": 60, "anchor_end": 62,
     "in_math": False, "in_verbatim": False, "in_comment": False, "env_depth": 0},
    {"rule_id": "TYPO-001", "label": 0, "bytes": [66] * 128,
     "anchor_start": 60, "anchor_end": 62,
     "in_math": True, "in_verbatim": False, "in_comment": False, "env_depth": 1},
    {"rule_id": "TYPO-052", "label": 1, "bytes": [60] * 128,
     "anchor_start": 63, "anchor_end": 64,
     "in_math": False, "in_verbatim": False, "in_comment": False, "env_depth": 0},
    {"rule_id": "TYPO-052", "label": 0, "bytes": [60] * 128,
     "anchor_start": 63, "anchor_end": 64,
     "in_math": True, "in_verbatim": False, "in_comment": False, "env_depth": 2},
]


class TestCandidateDataset(unittest.TestCase):

    @skipUnlessTorch
    def test_dataset_length(self):
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)
        self.assertEqual(len(ds), 4)

    @skipUnlessTorch
    def test_dataset_item_shapes(self):
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)
        item = ds[0]
        self.assertEqual(item['byte_input'].shape, (128,))
        self.assertEqual(item['anchor_start'].shape, ())
        self.assertEqual(item['anchor_end'].shape, ())
        self.assertEqual(item['rule_id'].shape, ())
        self.assertEqual(item['parser_features'].shape, (4,))
        self.assertEqual(item['label'].shape, ())

    @skipUnlessTorch
    def test_env_depth_normalized(self):
        """env_depth is divided by 10.0 for normalization."""
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)
        # Record index 3 has env_depth=2 -> 2/10 = 0.2
        item = ds[3]
        self.assertAlmostEqual(item['parser_features'][3].item(), 0.2, places=5)

    @skipUnlessTorch
    def test_in_math_feature(self):
        """in_math=True maps to 1.0, False maps to 0.0."""
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)
        item_no_math = ds[0]
        item_math = ds[1]
        self.assertAlmostEqual(item_no_math['parser_features'][0].item(), 0.0)
        self.assertAlmostEqual(item_math['parser_features'][0].item(), 1.0)

    @skipUnlessTorch
    def test_unknown_rule_skipped(self):
        """Records with rule_id not in RULE_TO_IDX are skipped."""
        bad_records = [
            {"rule_id": "FAKE-999", "label": 1, "bytes": [0] * 128,
             "anchor_start": 0, "anchor_end": 1,
             "in_math": False, "in_verbatim": False, "in_comment": False, "env_depth": 0},
        ]
        ds = CandidateDataset(bad_records, RULE_TO_IDX)
        self.assertEqual(len(ds), 0)

    @skipUnlessTorch
    def test_label_mapping(self):
        """label=1 in record -> label=1.0 in tensor, label=0 -> 0.0."""
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)
        self.assertAlmostEqual(ds[0]['label'].item(), 1.0)
        self.assertAlmostEqual(ds[1]['label'].item(), 0.0)


class TestEvaluateCandidates(unittest.TestCase):

    @skipUnlessTorch
    def test_perfect_model(self):
        """A model that returns exactly the labels gets F1=1.0."""
        ByteClassifier = build_byte_classifier()
        model = ByteClassifier()
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)

        # Mock: replace forward to return exact labels
        original_forward = model.forward
        def mock_forward(byte_input, anchor_start, anchor_end, rule_id, parser_features):
            # Return the ground truth labels from the dataset
            batch_size = byte_input.shape[0]
            return torch.tensor([SAMPLE_RECORDS[i % len(SAMPLE_RECORDS)]['label']
                                for i in range(batch_size)], dtype=torch.float32)
        model.forward = mock_forward

        results = evaluate_candidates(model, ds, threshold=0.5)
        self.assertEqual(results['overall_f1'], 1.0)
        self.assertEqual(results['total_fp'], 0)
        self.assertEqual(results['total_fn'], 0)

    @skipUnlessTorch
    def test_all_wrong_model(self):
        """A model that returns inverted labels gets F1=0.0."""
        ByteClassifier = build_byte_classifier()
        model = ByteClassifier()
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)

        def mock_forward(byte_input, anchor_start, anchor_end, rule_id, parser_features):
            batch_size = byte_input.shape[0]
            # Return inverted labels
            return torch.tensor([1.0 - SAMPLE_RECORDS[i % len(SAMPLE_RECORDS)]['label']
                                for i in range(batch_size)], dtype=torch.float32)
        model.forward = mock_forward

        results = evaluate_candidates(model, ds, threshold=0.5)
        self.assertEqual(results['overall_f1'], 0.0)

    @skipUnlessTorch
    def test_per_rule_breakdown(self):
        """Results include per-rule precision/recall for each rule."""
        ByteClassifier = build_byte_classifier()
        model = ByteClassifier()
        ds = CandidateDataset(SAMPLE_RECORDS, RULE_TO_IDX)

        def mock_forward(byte_input, anchor_start, anchor_end, rule_id, parser_features):
            return torch.tensor([0.9] * byte_input.shape[0], dtype=torch.float32)
        model.forward = mock_forward

        results = evaluate_candidates(model, ds, threshold=0.5)
        self.assertIn('per_rule', results)
        self.assertIn('TYPO-001', results['per_rule'])
        self.assertIn('TYPO-052', results['per_rule'])
        for rule_id, metrics in results['per_rule'].items():
            self.assertIn('precision', metrics)
            self.assertIn('recall', metrics)
            self.assertIn('f1', metrics)


if __name__ == "__main__":
    unittest.main()
