#!/usr/bin/env python3
"""Byte-level CNN+BiLSTM binary classifier for LaTeX rule violation detection.

Classifies candidate spans as violations or non-violations for the 8 ambiguous
TYPO rules that cannot be handled by deterministic replay functions.  Operates
on raw bytes (no WordPiece tokenisation) so character-level patterns like
``\\\\``, ``$$``, ``----``, ``<>`` are preserved exactly.

Architecture (per ARCHITECTURE.md S5):

    128 bytes ─► Embedding(256, 64)
              ─► Conv1d x3 (dilated, kernel 3/5/7)
              ─► BiLSTM(128, 128)
              ─► anchor-pooled 256-dim

    rule_id   ─► Embedding(8, 16)  ─► 16-dim

    parser_features ─────────────── 4 floats
                                      │
              concat ◄────────────────┘
              276-dim ─► MLP(276→128→1) ─► sigmoid ─► P(violation)

Target parameter budget: ~650K (must be < 1M).

Usage:
    from ml.models.byte_classifier import build_byte_classifier, RULE_TO_IDX
    ByteClassifier = build_byte_classifier()
    model = ByteClassifier(num_rules=8)
"""

import logging
from typing import Dict

import numpy as np

logger = logging.getLogger(__name__)

__all__ = [
    "build_byte_classifier",
    "count_parameters",
    "AMBIGUOUS_RULE_IDS",
    "RULE_TO_IDX",
    "IDX_TO_RULE",
]

# ── Rule ID mappings ────────────────────────────────────────────────────────

AMBIGUOUS_RULE_IDS = [
    "TYPO-001", "TYPO-005", "TYPO-012", "TYPO-028",
    "TYPO-048", "TYPO-052", "TYPO-056", "TYPO-062",
]
RULE_TO_IDX: Dict[str, int] = {r: i for i, r in enumerate(AMBIGUOUS_RULE_IDS)}
IDX_TO_RULE: Dict[int, str] = {i: r for r, i in RULE_TO_IDX.items()}

# ── Lazy torch imports ──────────────────────────────────────────────────────

torch = None
nn = None


def _import_torch():
    global torch, nn
    if torch is not None:
        return
    import torch as _torch
    import torch.nn as _nn
    torch = _torch
    nn = _nn


# ── Model factory ───────────────────────────────────────────────────────────

_ByteClassifierClass = None


def build_byte_classifier():
    """Build and return the ByteClassifier class (lazy torch import).

    Returns the class itself, not an instance.  Call it to instantiate::

        Cls = build_byte_classifier()
        model = Cls(num_rules=8)
    """
    global _ByteClassifierClass
    if _ByteClassifierClass is not None:
        return _ByteClassifierClass

    _import_torch()

    class ByteClassifier(nn.Module):
        """Byte-level CNN+BiLSTM binary classifier for candidate spans.

        Given a 128-byte context window, anchor boundaries, a rule ID, and
        parser-state features, predicts P(violation) in [0, 1].

        Parameters
        ----------
        num_rules : int
            Number of distinct rule IDs (default 8 for the ambiguous set).
        context_size : int
            Length of the byte input sequence (default 128).
        byte_embed_dim : int
            Dimensionality of byte embeddings (default 64).
        cnn_channels : int
            Number of output channels for each Conv1d layer (default 128).
        lstm_hidden : int
            Hidden size per direction for BiLSTM (default 128).
        rule_embed_dim : int
            Dimensionality of rule ID embeddings (default 16).
        parser_feat_dim : int
            Number of parser-state features (default 4).
        mlp_hidden : int
            Hidden units in the classification MLP (default 128).
        dropout : float
            Dropout probability in the MLP (default 0.3).
        """

        def __init__(
            self,
            num_rules: int = 8,
            context_size: int = 128,
            byte_embed_dim: int = 64,
            cnn_channels: int = 128,
            lstm_hidden: int = 128,
            rule_embed_dim: int = 16,
            parser_feat_dim: int = 4,
            mlp_hidden: int = 128,
            dropout: float = 0.3,
        ):
            super().__init__()
            self.context_size = context_size
            self.lstm_hidden = lstm_hidden

            # ── Byte encoder ────────────────────────────────────────────
            # 256 possible byte values -> byte_embed_dim
            self.byte_embed = nn.Embedding(256, byte_embed_dim)

            # Dilated CNN stack: increasing receptive field
            self.conv1 = nn.Conv1d(
                byte_embed_dim, cnn_channels, kernel_size=3,
                dilation=1, padding=1,
            )
            self.bn1 = nn.BatchNorm1d(cnn_channels)

            self.conv2 = nn.Conv1d(
                cnn_channels, cnn_channels, kernel_size=5,
                dilation=2, padding=4,
            )
            self.bn2 = nn.BatchNorm1d(cnn_channels)

            self.conv3 = nn.Conv1d(
                cnn_channels, cnn_channels, kernel_size=7,
                dilation=4, padding=12,
            )
            self.bn3 = nn.BatchNorm1d(cnn_channels)

            self.relu = nn.ReLU(inplace=True)

            # BiLSTM over CNN output
            self.bilstm = nn.LSTM(
                input_size=cnn_channels,
                hidden_size=lstm_hidden,
                num_layers=1,
                batch_first=True,
                bidirectional=True,
            )
            # BiLSTM output dim = 2 * lstm_hidden

            # ── Rule encoder ────────────────────────────────────────────
            self.rule_embed = nn.Embedding(num_rules, rule_embed_dim)

            # ── Classifier MLP ──────────────────────────────────────────
            classifier_in = 2 * lstm_hidden + rule_embed_dim + parser_feat_dim
            self.fc1 = nn.Linear(classifier_in, mlp_hidden)
            self.drop = nn.Dropout(dropout)
            self.fc2 = nn.Linear(mlp_hidden, 1)

        def forward(self, byte_input, anchor_start, anchor_end,
                    rule_id, parser_features):
            """Forward pass.

            Args:
                byte_input: [batch, context_size] int tensor (values 0--255).
                anchor_start: [batch] int tensor -- inclusive start of anchor.
                anchor_end: [batch] int tensor -- exclusive end of anchor.
                rule_id: [batch] int tensor (0 to num_rules-1).
                parser_features: [batch, parser_feat_dim] float tensor.

            Returns:
                [batch] float tensor of P(violation) in [0, 1].
            """
            batch_size = byte_input.size(0)

            # ── Byte encoding ───────────────────────────────────────────
            # [batch, seq, embed_dim]
            x = self.byte_embed(byte_input)

            # Conv1d expects [batch, channels, seq_len]
            x = x.transpose(1, 2)

            x = self.relu(self.bn1(self.conv1(x)))
            x = self.relu(self.bn2(self.conv2(x)))
            x = self.relu(self.bn3(self.conv3(x)))

            # Back to [batch, seq_len, channels] for LSTM
            x = x.transpose(1, 2)

            # BiLSTM: [batch, seq_len, 2*lstm_hidden]
            x, _ = self.bilstm(x)

            # ── Anchor pooling ──────────────────────────────────────────
            # Mean-pool the BiLSTM output over [anchor_start, anchor_end)
            # for each item in the batch.
            pooled = torch.zeros(
                batch_size, 2 * self.lstm_hidden,
                device=byte_input.device, dtype=x.dtype,
            )
            for i in range(batch_size):
                s = anchor_start[i].item()
                e = anchor_end[i].item()
                if e <= s:
                    # Degenerate anchor -- fall back to full-sequence mean
                    pooled[i] = x[i].mean(dim=0)
                else:
                    pooled[i] = x[i, s:e].mean(dim=0)

            # ── Rule embedding ──────────────────────────────────────────
            rule_emb = self.rule_embed(rule_id)  # [batch, rule_embed_dim]

            # ── Concatenate & classify ──────────────────────────────────
            combined = torch.cat([pooled, rule_emb, parser_features], dim=1)
            out = self.relu(self.fc1(combined))
            out = self.drop(out)
            out = torch.sigmoid(self.fc2(out)).squeeze(-1)  # [batch]
            return out

    _ByteClassifierClass = ByteClassifier
    return _ByteClassifierClass


# ── Utilities ───────────────────────────────────────────────────────────────

def count_parameters(model) -> int:
    """Return total number of trainable parameters in a model.

    Args:
        model: a ``torch.nn.Module`` instance.

    Returns:
        Integer count of parameters with ``requires_grad=True``.
    """
    return sum(p.numel() for p in model.parameters() if p.requires_grad)
