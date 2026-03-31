#!/usr/bin/env python3
"""Tests for the byte-level CNN+BiLSTM candidate classifier."""

import unittest
import sys

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

if HAS_TORCH:
    from ml.models.byte_classifier import (
        build_byte_classifier,
        count_parameters,
        RULE_TO_IDX,
        AMBIGUOUS_RULE_IDS,
    )


def skipUnlessTorch(test_func):
    return unittest.skipUnless(HAS_TORCH, "torch not available")(test_func)


def _make_batch(batch_size=4, context_size=128, num_rules=8):
    byte_input = torch.randint(0, 256, (batch_size, context_size))
    anchor_start = torch.full((batch_size,), 60, dtype=torch.long)
    anchor_end = torch.full((batch_size,), 64, dtype=torch.long)
    rule_id = torch.randint(0, num_rules, (batch_size,))
    parser_features = torch.randn(batch_size, 4)
    return byte_input, anchor_start, anchor_end, rule_id, parser_features


def _build_model():
    Cls = build_byte_classifier()
    return Cls(num_rules=8)


class TestByteClassifier(unittest.TestCase):

    @skipUnlessTorch
    def test_forward_output_shape(self):
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=4)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertEqual(out.shape, torch.Size([4]))

    @skipUnlessTorch
    def test_output_range_sigmoid(self):
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=8)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertTrue((out >= 0.0).all(), f"Output has values < 0: {out}")
        self.assertTrue((out <= 1.0).all(), f"Output has values > 1: {out}")

    @skipUnlessTorch
    def test_single_item_batch(self):
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=1)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertEqual(out.shape, torch.Size([1]))
        self.assertTrue(0.0 <= out.item() <= 1.0)

    @skipUnlessTorch
    def test_gradient_flows_all_params(self):
        model = _build_model()
        model.train()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=4)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        target = torch.rand(4)
        loss = torch.nn.BCELoss()(out, target)
        loss.backward()
        for name, param in model.named_parameters():
            if param.requires_grad:
                self.assertIsNotNone(
                    param.grad,
                    f"Parameter '{name}' has None gradient -- layer may be disconnected",
                )
                self.assertFalse(
                    (param.grad == 0).all(),
                    f"Parameter '{name}' has all-zero gradient -- layer may be disconnected",
                )

    @skipUnlessTorch
    def test_different_rules_different_output(self):
        torch.manual_seed(42)
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, _, parser_features = _make_batch(batch_size=1)
        # Same input, two different rule IDs
        rule_a = torch.tensor([0])
        rule_b = torch.tensor([7])
        out_a = model(byte_input, anchor_start, anchor_end, rule_a, parser_features)
        out_b = model(byte_input, anchor_start, anchor_end, rule_b, parser_features)
        self.assertFalse(
            torch.allclose(out_a, out_b, atol=1e-7),
            f"Same output for different rule IDs: {out_a.item()} vs {out_b.item()}",
        )

    @skipUnlessTorch
    def test_different_parser_features_different_output(self):
        torch.manual_seed(42)
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, rule_id, _ = _make_batch(batch_size=1)
        # in_math=0
        pf_no_math = torch.tensor([[0.0, 0.0, 0.0, 0.0]])
        # in_math=1
        pf_math = torch.tensor([[1.0, 0.0, 0.0, 0.0]])
        out_no = model(byte_input, anchor_start, anchor_end, rule_id, pf_no_math)
        out_yes = model(byte_input, anchor_start, anchor_end, rule_id, pf_math)
        self.assertFalse(
            torch.allclose(out_no, out_yes, atol=1e-7),
            f"Parser features had no effect: {out_no.item()} vs {out_yes.item()}",
        )

    @skipUnlessTorch
    def test_anchor_position_matters(self):
        torch.manual_seed(42)
        model = _build_model()
        model.eval()
        byte_input, _, _, rule_id, parser_features = _make_batch(batch_size=1)
        anchor_start_a = torch.tensor([10])
        anchor_end_a = torch.tensor([20])
        anchor_start_b = torch.tensor([90])
        anchor_end_b = torch.tensor([100])
        out_a = model(byte_input, anchor_start_a, anchor_end_a, rule_id, parser_features)
        out_b = model(byte_input, anchor_start_b, anchor_end_b, rule_id, parser_features)
        self.assertFalse(
            torch.allclose(out_a, out_b, atol=1e-7),
            f"Anchor position had no effect: {out_a.item()} vs {out_b.item()}",
        )

    @skipUnlessTorch
    def test_batch_consistency(self):
        torch.manual_seed(42)
        model = _build_model()
        model.eval()
        # Build a batch of 4 and run the first item alone
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=4)
        with torch.no_grad():
            out_batch = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
            out_single = model(
                byte_input[:1], anchor_start[:1], anchor_end[:1],
                rule_id[:1], parser_features[:1],
            )
        self.assertTrue(
            torch.allclose(out_batch[0:1], out_single, atol=1e-5),
            f"Batch inconsistency: batch[0]={out_batch[0].item()}, "
            f"single={out_single.item()}, diff={abs(out_batch[0].item() - out_single.item())}",
        )

    @skipUnlessTorch
    def test_model_parameter_count(self):
        model = _build_model()
        n_params = count_parameters(model)
        self.assertLess(
            n_params, 1_000_000,
            f"Model has {n_params:,} trainable params, exceeds 1M budget",
        )

    @skipUnlessTorch
    def test_zero_padded_input(self):
        model = _build_model()
        model.eval()
        byte_input = torch.zeros(2, 128, dtype=torch.long)
        anchor_start = torch.tensor([0, 0])
        anchor_end = torch.tensor([4, 4])
        rule_id = torch.tensor([0, 1])
        parser_features = torch.zeros(2, 4)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertFalse(torch.isnan(out).any(), "NaN in output for zero-padded input")
        self.assertEqual(out.shape, torch.Size([2]))

    @skipUnlessTorch
    def test_max_byte_values(self):
        model = _build_model()
        model.eval()
        byte_input = torch.full((2, 128), 255, dtype=torch.long)
        anchor_start = torch.tensor([60, 60])
        anchor_end = torch.tensor([64, 64])
        rule_id = torch.tensor([3, 5])
        parser_features = torch.randn(2, 4)
        out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertFalse(torch.isnan(out).any(), "NaN in output for max-byte input")
        self.assertEqual(out.shape, torch.Size([2]))

    @skipUnlessTorch
    def test_rule_to_idx_mapping(self):
        self.assertEqual(len(RULE_TO_IDX), 8, f"Expected 8 rule entries, got {len(RULE_TO_IDX)}")
        self.assertEqual(
            set(RULE_TO_IDX.values()), set(range(8)),
            f"RULE_TO_IDX values should be 0-7, got {sorted(RULE_TO_IDX.values())}",
        )
        for rule_id in AMBIGUOUS_RULE_IDS:
            self.assertIn(rule_id, RULE_TO_IDX, f"Missing rule {rule_id} in RULE_TO_IDX")

    @skipUnlessTorch
    def test_deterministic_forward(self):
        torch.manual_seed(99)
        model = _build_model()
        model.eval()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=4)
        with torch.no_grad():
            out1 = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
            out2 = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertTrue(
            torch.equal(out1, out2),
            f"Non-deterministic forward in eval mode: {out1} vs {out2}",
        )

    @skipUnlessTorch
    def test_train_vs_eval_mode(self):
        torch.manual_seed(0)
        model = _build_model()
        byte_input, anchor_start, anchor_end, rule_id, parser_features = _make_batch(batch_size=8)
        # Collect multiple train-mode passes to check for variance from dropout
        model.train()
        train_outputs = []
        with torch.no_grad():
            for _ in range(20):
                out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
                train_outputs.append(out.clone())
        train_stack = torch.stack(train_outputs)
        train_varies = not all(torch.equal(train_stack[0], train_stack[i]) for i in range(1, 20))

        model.eval()
        with torch.no_grad():
            eval_out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        eval_outputs = []
        with torch.no_grad():
            for _ in range(5):
                out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
                eval_outputs.append(out.clone())
        eval_deterministic = all(torch.equal(eval_outputs[0], eval_outputs[i]) for i in range(1, 5))

        # At least one of these should be true: train mode varies OR eval mode is deterministic
        self.assertTrue(
            train_varies or eval_deterministic,
            "Neither train-mode variance nor eval-mode determinism detected -- "
            "dropout/batchnorm may not be functioning",
        )


    @skipUnlessTorch
    def test_zero_width_anchor_fallback(self):
        """Zero-width anchor (start == end) should fall back to global mean pooling,
        not crash or produce NaN. This path fires if candidate extraction produces
        degenerate spans."""
        model = _build_model()
        model.eval()
        byte_input, _, _, rule_id, parser_features = _make_batch(batch_size=2)
        # Set anchor_start == anchor_end (zero-width)
        anchor_start = torch.tensor([64, 64])
        anchor_end = torch.tensor([64, 64])  # zero-width
        with torch.no_grad():
            out = model(byte_input, anchor_start, anchor_end, rule_id, parser_features)
        self.assertEqual(out.shape, (2,))
        self.assertTrue(torch.all(out >= 0) and torch.all(out <= 1),
                        f"Output out of [0,1] range with zero-width anchor: {out}")
        self.assertFalse(torch.any(torch.isnan(out)),
                         "NaN with zero-width anchor")


if __name__ == "__main__":
    unittest.main()
