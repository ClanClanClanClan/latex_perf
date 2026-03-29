#!/usr/bin/env python3
"""BERT + CRF span extractor for LaTeX error detection.

Uses a BERT encoder (allenai/scibert for domain coverage) with a CRF layer
on top for structured BIO prediction. Designed for fine-tuning on Google
Colab Pro (A100/V100 GPU).

Architecture:
    Input text → BERT subword tokenizer → BERT encoder → CRF layer → BIO tags

Key design:
    - Subword-to-character alignment via offset_mapping (proper round-trip)
    - Class-weighted loss to handle extreme O-tag imbalance (~99%+ O)
    - Compact max_length (128) since corpus docs are small (30-200 chars)
    - 20 epochs with early stopping to converge on sparse data

Usage:
    python -m ml.models.bert_crf --train data/train.jsonl --dev data/dev.jsonl --device cuda
"""

import json
import logging
import argparse
import random
from pathlib import Path
from typing import List, Dict, Tuple, Any, Optional

import numpy as np

logger = logging.getLogger(__name__)

# Lazy imports for torch (may not be available in CI)
torch = None
nn = None
CRF = None


def _import_torch():
    global torch, nn, CRF
    if torch is not None:
        return
    import torch as _torch
    import torch.nn as _nn
    torch = _torch
    nn = _nn
    try:
        from torchcrf import CRF as _CRF
        CRF = _CRF
        logger.info("torchcrf loaded — CRF layer available")
    except ImportError:
        logger.warning("torchcrf not installed — CRF layer unavailable, using greedy decoding")
        CRF = None


# ── Tag scheme ───────────────────────────────────────────────────────────────

class TagScheme:
    """BIO tag ↔ index mapping."""

    def __init__(self, rule_ids: List[str]):
        self.tags = ["O"]
        for rule in sorted(set(rule_ids)):
            self.tags.append(f"B-{rule}")
            self.tags.append(f"I-{rule}")
        self.tag_to_idx = {t: i for i, t in enumerate(self.tags)}
        self.idx_to_tag = {i: t for t, i in self.tag_to_idx.items()}
        self.num_tags = len(self.tags)

    def encode(self, tag: str) -> int:
        return self.tag_to_idx.get(tag, 0)

    def decode(self, idx: int) -> str:
        return self.idx_to_tag.get(idx, "O")


# ── Dataset ──────────────────────────────────────────────────────────────────

class SpanDataset:
    """Dataset of (text, BIO tags) pairs for BERT+CRF.

    Stores pre-tokenized data with proper subword→char alignment.
    Optionally includes per-token parser-state features (in_math, in_verbatim).
    """

    def __init__(self, texts, bio_tags, tag_scheme, tokenizer, max_length=128,
                 parser_states=None):
        """
        Args:
            texts: list of raw text strings
            bio_tags: list of char-level BIO tag lists
            tag_scheme: TagScheme instance
            tokenizer: BERT tokenizer
            max_length: max subword tokens
            parser_states: optional list of ParserState objects (one per text).
                If provided, each item gets a 'parser_features' field with
                [in_math, in_verbatim] floats per subword token.
        """
        self.items = []
        self.has_parser_features = parser_states is not None
        for idx, (text, tags) in enumerate(zip(texts, bio_tags)):
            enc = tokenizer(
                text,
                max_length=max_length,
                truncation=True,
                padding='max_length',
                return_offsets_mapping=True,
            )
            offsets = enc['offset_mapping']

            # Align char-level BIO tags → subword tokens
            aligned = []
            parser_feats = []  # [max_length, 2] if parser_states given
            ps = parser_states[idx] if parser_states is not None else None

            for start, end in offsets:
                if start == end:
                    # Special token or padding → ignore label (-100)
                    aligned.append(-100)
                    parser_feats.append([0.0, 0.0])
                else:
                    char_idx = int(start)
                    if char_idx < len(tags):
                        aligned.append(tag_scheme.encode(tags[char_idx]))
                    else:
                        aligned.append(0)  # O
                    # Parser features: sample at first char of subword
                    if ps is not None and char_idx < len(ps):
                        parser_feats.append([
                            1.0 if ps.in_math[char_idx] else 0.0,
                            1.0 if ps.in_verbatim[char_idx] else 0.0,
                        ])
                    else:
                        parser_feats.append([0.0, 0.0])

            item = {
                'input_ids': enc['input_ids'],
                'attention_mask': enc['attention_mask'],
                'labels': aligned,
                'offsets': offsets,
                'text_len': len(text),
                'char_tags': tags,
            }
            if self.has_parser_features:
                item['parser_features'] = parser_feats
            self.items.append(item)

    def __len__(self):
        return len(self.items)

    def __getitem__(self, idx):
        item = self.items[idx]
        result = {
            'input_ids': torch.tensor(item['input_ids'], dtype=torch.long),
            'attention_mask': torch.tensor(item['attention_mask'], dtype=torch.long),
            'labels': torch.tensor(item['labels'], dtype=torch.long),
        }
        if self.has_parser_features:
            result['parser_features'] = torch.tensor(
                item['parser_features'], dtype=torch.float32)
        return result


# ── Model ────────────────────────────────────────────────────────────────────

_ModelClass = None


def _build_model_class():
    global _ModelClass
    if _ModelClass is not None:
        return _ModelClass

    _import_torch()

    class BertCRFSpanExtractor(nn.Module):
        """BERT + optional CRF for BIO sequence labeling."""

        def __init__(self, model_name, num_tags, use_crf=True, dropout=0.1,
                     class_weights=None, focal_gamma=0.0):
            super().__init__()
            from transformers import AutoModel
            self.bert = AutoModel.from_pretrained(model_name)
            self.dropout = nn.Dropout(dropout)
            self.classifier = nn.Linear(self.bert.config.hidden_size, num_tags)
            self.use_crf = use_crf and CRF is not None
            if self.use_crf:
                self.crf = CRF(num_tags, batch_first=True)
            self.num_tags = num_tags
            self.focal_gamma = focal_gamma
            # Class weights for cross-entropy / focal loss
            if class_weights is not None:
                self.register_buffer('class_weights', class_weights)
            else:
                self.class_weights = None

        def _focal_loss(self, logits, targets):
            """Alpha-balanced focal loss: -alpha_t * (1-p_t)^gamma * log(p_t)."""
            import torch.nn.functional as F
            # Standard CE per-element (no reduction)
            ce = F.cross_entropy(
                logits, targets, weight=self.class_weights,
                ignore_index=-100, reduction='none')
            if self.focal_gamma > 0:
                pt = torch.exp(-ce)  # p_t = probability of correct class
                focal_weight = (1.0 - pt) ** self.focal_gamma
                ce = focal_weight * ce
            return ce.mean()

        def forward(self, input_ids, attention_mask, labels=None,
                    parser_features=None):
            outputs = self.bert(input_ids=input_ids, attention_mask=attention_mask)
            emissions = self.dropout(outputs.last_hidden_state)
            emissions = self.classifier(emissions)
            # parser_features is accepted but ignored for single-head model
            # (only used by BertMultiHeadSpanExtractor)

            if labels is not None:
                if self.use_crf:
                    # CRF needs valid labels (no -100), mask out special/pad tokens
                    crf_mask = (labels != -100) & attention_mask.bool()
                    # CRF requires first timestep mask=True; position 0 is [CLS]
                    # which has label=-100, so force it on and give it the O tag
                    crf_mask[:, 0] = True
                    # Replace -100 with 0 for CRF (masked positions are ignored)
                    safe_labels = labels.clone()
                    safe_labels[safe_labels == -100] = 0
                    loss = -self.crf(emissions, safe_labels, mask=crf_mask)
                    return loss
                else:
                    return self._focal_loss(
                        emissions.view(-1, self.num_tags), labels.view(-1))
            else:
                if self.use_crf:
                    tags = self.crf.decode(emissions, mask=attention_mask.bool())
                    return tags
                else:
                    return emissions.argmax(dim=-1).tolist()

    _ModelClass = BertCRFSpanExtractor
    return _ModelClass


# ── Multi-head model ─────────────────────────────────────────────────────────

_MultiHeadModelClass = None


def _build_multihead_model_class():
    """Build per-rule-head model class (lazy torch import)."""
    global _MultiHeadModelClass
    if _MultiHeadModelClass is not None:
        return _MultiHeadModelClass

    _import_torch()

    class BertMultiHeadSpanExtractor(nn.Module):
        """BERT + independent per-rule 3-class heads for BIO labeling.

        Instead of one N-class classifier sharing all rules, uses K separate
        3-class heads (O/B/I), one per rule.  Each head learns independently
        — rare rules don't compete with common ones for the shared output.

        All K heads are fused into a single nn.Linear(H, K*3) to avoid
        launching K separate CUDA kernels per batch.  Label conversion and
        inference merge are fully vectorized (no Python loops over heads).
        """

        def __init__(self, model_name, rule_ids, tag_scheme, dropout=0.1,
                     focal_gamma=0.0, per_head_weights=None,
                     use_parser_features=False):
            super().__init__()
            from transformers import AutoModel
            self.bert = AutoModel.from_pretrained(model_name)
            self.dropout = nn.Dropout(dropout)

            self.rule_ids = list(rule_ids)
            self.num_rules = len(self.rule_ids)
            self.num_tags = tag_scheme.num_tags
            self.focal_gamma = focal_gamma
            self.use_crf = False  # compatibility with training loop
            self.use_parser_features = use_parser_features

            # Fused K×3-class head: one matmul instead of K separate ones
            hidden_size = self.bert.config.hidden_size
            # If parser features enabled, concat 2 extra dims (in_math, in_verbatim)
            classifier_input = hidden_size + (2 if use_parser_features else 0)
            self.classifier = nn.Linear(classifier_input, self.num_rules * 3)

            # Unified-tag → per-head-label mapping: [num_rules, num_tags]
            mapping = torch.zeros(self.num_rules, tag_scheme.num_tags,
                                  dtype=torch.long)
            for h, rule in enumerate(self.rule_ids):
                b_idx = tag_scheme.tag_to_idx.get(f'B-{rule}', -1)
                i_idx = tag_scheme.tag_to_idx.get(f'I-{rule}', -1)
                if b_idx >= 0:
                    mapping[h, b_idx] = 1
                if i_idx >= 0:
                    mapping[h, i_idx] = 2
            self.register_buffer('tag_mapping', mapping)

            # Per-head class weights [num_rules, 3]
            if per_head_weights is not None:
                self.register_buffer('per_head_weights',
                                     torch.stack(per_head_weights))
            else:
                self.per_head_weights = None

            # Unified B/I indices per rule (for inference merge)
            b_indices = []
            i_indices = []
            for rule in self.rule_ids:
                b_indices.append(tag_scheme.tag_to_idx.get(f'B-{rule}', 0))
                i_indices.append(tag_scheme.tag_to_idx.get(f'I-{rule}', 0))
            self.register_buffer('_b_indices',
                                 torch.tensor(b_indices, dtype=torch.long))
            self.register_buffer('_i_indices',
                                 torch.tensor(i_indices, dtype=torch.long))

        def forward(self, input_ids, attention_mask, labels=None,
                    parser_features=None):
            outputs = self.bert(input_ids=input_ids,
                                attention_mask=attention_mask)
            hidden = self.dropout(outputs.last_hidden_state)
            # Concatenate parser features if provided and model expects them
            if self.use_parser_features and parser_features is not None:
                hidden = torch.cat([hidden, parser_features], dim=-1)
            if labels is not None:
                return self._training_forward(hidden, labels)
            else:
                return self._inference_forward(hidden, input_ids)

        def _training_forward(self, hidden, labels):
            """Fully vectorized: fused matmul + loss (zero Python loops)."""
            import torch.nn.functional as F
            B, T, _H = hidden.shape
            K = self.num_rules

            # Single fused matmul: [B, T, H] → [B, T, K*3] → [B, T, K, 3]
            all_logits = self.classifier(hidden).view(B, T, K, 3)

            # Vectorized label conversion: unified [B,T] → per-head [K, B, T]
            mask = labels == -100  # [B, T]
            safe = labels.clone()
            safe[mask] = 0
            all_head_labels = self.tag_mapping[:, safe]  # [K, B, T]
            mask_k = mask.unsqueeze(0).expand(K, -1, -1)  # [K, B, T]
            all_head_labels[mask_k] = -100

            # Reshape: logits [K, BT, 3], labels [K, BT]
            flat_logits = all_logits.permute(2, 0, 1, 3).reshape(K, -1, 3)
            flat_labels = all_head_labels.reshape(K, -1)

            # Fully vectorized focal CE (no loop over K heads)
            ignore = (flat_labels == -100)           # [K, BT]
            safe_fl = flat_labels.clone()
            safe_fl[ignore] = 0

            # Log-softmax → gather target log-probs
            log_probs = F.log_softmax(flat_logits, dim=-1)  # [K, BT, 3]
            target_lp = log_probs.gather(
                2, safe_fl.unsqueeze(-1)).squeeze(-1)       # [K, BT]

            # Per-head class weights via gather
            if self.per_head_weights is not None:
                # per_head_weights: [K, 3], safe_fl: [K, BT] → [K, BT]
                class_w = self.per_head_weights.gather(1, safe_fl)
            else:
                class_w = 1.0

            # Weighted CE + focal (all vectorized)
            ce = -class_w * target_lp               # [K, BT]
            if self.focal_gamma > 0:
                pt = torch.exp(target_lp)            # p_target
                ce = ((1.0 - pt) ** self.focal_gamma) * ce
            ce[ignore] = 0.0

            # Mean per head, then mean across heads
            counts = (~ignore).sum(dim=1).clamp(min=1).float()  # [K]
            return (ce.sum(dim=1) / counts).mean()

        def _inference_forward(self, hidden, input_ids):
            """Fully vectorized: batched forward + merge by confidence."""
            B, T = input_ids.shape
            K = self.num_rules
            NEG_INF = -1e9

            # Single fused matmul → [B, T, K, 3]
            all_logits = self.classifier(hidden).view(B, T, K, 3)

            # Per-head predictions and confidence (no loop)
            all_probs = torch.softmax(all_logits, dim=-1)   # [B, T, K, 3]
            all_preds = all_logits.argmax(dim=-1)            # [B, T, K]
            non_o_conf = all_probs[:, :, :, 1:].max(dim=-1).values  # [B, T, K]

            # Mask non-entity predictions, find best head per token
            is_entity = all_preds > 0
            masked_conf = torch.where(is_entity, non_o_conf,
                                      torch.full_like(non_o_conf, NEG_INF))
            best_head = masked_conf.argmax(dim=-1)           # [B, T]
            best_conf = masked_conf.max(dim=-1).values       # [B, T]
            has_entity = best_conf > NEG_INF

            # Gather prediction from winning head
            best_pred = all_preds.gather(
                2, best_head.unsqueeze(-1)).squeeze(-1)      # [B, T]

            # Map local {1=B, 2=I} → unified tag indices
            b_unified = self._b_indices[best_head]           # [B, T]
            i_unified = self._i_indices[best_head]           # [B, T]
            unified = torch.where(
                best_pred == 1, b_unified,
                torch.where(best_pred == 2, i_unified,
                            torch.zeros_like(best_pred)))
            result = torch.where(has_entity, unified,
                                 torch.zeros_like(unified))
            return result.tolist()

    _MultiHeadModelClass = BertMultiHeadSpanExtractor
    return _MultiHeadModelClass


# ── Subword → character projection ──────────────────────────────────────────

def subword_preds_to_char_tags(
    subword_tags: List[int],
    offsets: List[Tuple[int, int]],
    text_len: int,
    tag_scheme: TagScheme,
) -> List[str]:
    """Project subword-level tag indices back to character-level BIO strings.

    For B-tags, only the first character gets B; remaining characters in
    the subword get I (continuing the span).  This prevents a single
    B-tagged subword from creating multiple spurious 1-char spans.
    """
    char_tags = ['O'] * text_len
    for tok_idx, (start, end) in enumerate(offsets):
        if start == end:
            continue  # special token or padding
        if tok_idx >= len(subword_tags):
            continue
        tag_str = tag_scheme.decode(subword_tags[tok_idx])
        for c in range(int(start), min(int(end), text_len)):
            if c == int(start):
                char_tags[c] = tag_str
            elif tag_str.startswith('B-'):
                # Interior chars of a B-tagged subword continue the span
                char_tags[c] = 'I-' + tag_str[2:]
            else:
                char_tags[c] = tag_str
    return char_tags


# ── Training ─────────────────────────────────────────────────────────────────

def set_seed(seed):
    random.seed(seed)
    np.random.seed(seed)
    _import_torch()
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def train_bert_crf(
    train_jsonl: str,
    dev_jsonl: str,
    model_name: str = "allenai/scibert_scivocab_uncased",
    max_length: int = 128,
    batch_size: int = 8,
    epochs: int = 50,
    learning_rate: float = 3e-5,
    warmup_ratio: float = 0.1,
    weight_decay: float = 0.01,
    crf_lr: float = 1e-3,
    patience: int = 7,
    min_epochs: int = 15,
    seed: int = 42,
    device: str = "cpu",
    output_dir: str = "ml/checkpoints",
    use_crf: bool = True,
    use_amp: bool = False,
    gradient_accumulation_steps: int = 1,
    num_workers: int = 0,
    save_callback=None,
    resume_from: Optional[str] = None,
    focal_gamma: float = 0.0,
    class_weight_cap: float = 50.0,
    multi_head: bool = False,
    use_parser_features: bool = False,
) -> Dict[str, Any]:
    """Full BERT+CRF training pipeline. Returns evaluation results dict."""
    _import_torch()
    from torch.utils.data import DataLoader
    from transformers import AutoTokenizer, get_linear_schedule_with_warmup
    from ml.evaluate import evaluate

    set_seed(seed)

    # Load data
    train_docs = _load_jsonl(train_jsonl)
    dev_docs = _load_jsonl(dev_jsonl)
    logger.info(f"Train: {len(train_docs)} docs, Dev: {len(dev_docs)} docs")

    # Count positive examples
    train_pos = sum(1 for d in train_docs for t in d['bio_tags'] if t != 'O')
    train_total = sum(len(d['bio_tags']) for d in train_docs)
    logger.info(f"Train class balance: {train_pos}/{train_total} positive "
                f"({train_pos/max(train_total,1)*100:.2f}%)")

    # Build tag scheme
    all_rules = set()
    for doc in train_docs + dev_docs:
        for tag in doc["bio_tags"]:
            if tag != "O":
                all_rules.add(tag.split("-", 1)[1])
    tag_scheme = TagScheme(sorted(all_rules))
    logger.info(f"Tag scheme: {tag_scheme.num_tags} tags for {len(all_rules)} rules")

    # Tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    # Compute parser states if enabled
    train_parser_states = None
    dev_parser_states = None
    if use_parser_features:
        from ml.data.parser_state import compute_parser_state
        logger.info("Computing parser-state features (in_math, in_verbatim)...")
        train_parser_states = [compute_parser_state(d["text"]) for d in train_docs]
        dev_parser_states = [compute_parser_state(d["text"]) for d in dev_docs]
        logger.info(f"Parser states computed: {len(train_parser_states)} train, "
                     f"{len(dev_parser_states)} dev")

    # Datasets
    train_dataset = SpanDataset(
        [d["text"] for d in train_docs],
        [d["bio_tags"] for d in train_docs],
        tag_scheme, tokenizer, max_length,
        parser_states=train_parser_states,
    )
    dev_dataset = SpanDataset(
        [d["text"] for d in dev_docs],
        [d["bio_tags"] for d in dev_docs],
        tag_scheme, tokenizer, max_length,
        parser_states=dev_parser_states,
    )

    pin = device.startswith('cuda')
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True,
                              num_workers=num_workers, pin_memory=pin)
    dev_loader = DataLoader(dev_dataset, batch_size=batch_size, shuffle=False,
                            num_workers=num_workers, pin_memory=pin)

    logger.info(f"Batches/epoch: {len(train_loader)}")

    # Compute class weights
    class_weights = None
    per_head_weights = None
    sorted_rules = sorted(all_rules)

    if multi_head or not use_crf:
        from collections import Counter
        tag_counts = Counter()
        for doc in train_docs:
            for tag in doc['bio_tags']:
                tag_counts[tag_scheme.encode(tag)] += 1
        total = sum(tag_counts.values())

    if multi_head:
        # Per-head weights: each head gets O/B/I weights for its rule
        per_head_weights = []
        for rule in sorted_rules:
            b_idx = tag_scheme.encode(f'B-{rule}')
            i_idx = tag_scheme.encode(f'I-{rule}')
            b_count = max(tag_counts.get(b_idx, 0), 1)
            i_count = max(tag_counts.get(i_idx, 0), 1)
            o_count = max(total - b_count - i_count, 1)
            head_total = o_count + b_count + i_count
            w = torch.tensor([head_total / (3 * c)
                              for c in [o_count, b_count, i_count]])
            per_head_weights.append(w.clamp(max=class_weight_cap).to(device))
        avg_b = sum(w[1].item() for w in per_head_weights) / len(per_head_weights)
        avg_i = sum(w[2].item() for w in per_head_weights) / len(per_head_weights)
        logger.info(f"Per-head weights: avg B={avg_b:.1f}, avg I={avg_i:.1f} "
                    f"(cap={class_weight_cap}, {len(sorted_rules)} heads)")
    elif not use_crf:
        n_classes = tag_scheme.num_tags
        weights = torch.ones(n_classes)
        for idx, count in tag_counts.items():
            if count > 0:
                weights[idx] = total / (n_classes * count)
        weights = weights.clamp(max=class_weight_cap)
        class_weights = weights.to(device)
        o_w = weights[0].item()
        max_w = weights.max().item()
        logger.info(f"Class weights: O={o_w:.3f}, max={max_w:.1f} "
                    f"(cap={class_weight_cap}, {n_classes} classes)")

    # Model
    if multi_head:
        ModelClass = _build_multihead_model_class()
        model = ModelClass(model_name, sorted_rules, tag_scheme,
                           focal_gamma=focal_gamma,
                           per_head_weights=per_head_weights,
                           use_parser_features=use_parser_features)
        model.to(device)
        n_head_params = sum(p.numel() for p in model.classifier.parameters())
        pf_str = " +parser_features" if use_parser_features else ""
        logger.info(f"Multi-head model on {device}: {len(sorted_rules)} heads x 3, "
                    f"focal_gamma={focal_gamma}, head_params={n_head_params:,}{pf_str}")
    else:
        ModelClass = _build_model_class()
        model = ModelClass(model_name, tag_scheme.num_tags, use_crf=use_crf,
                           class_weights=class_weights, focal_gamma=focal_gamma)
        model.to(device)
        logger.info(f"Model on {device}, CRF={model.use_crf}, "
                    f"focal_gamma={focal_gamma}")

    # Optimizer — separate CRF lr only if CRF is active
    if model.use_crf:
        bert_params = [p for n, p in model.named_parameters() if 'crf' not in n]
        crf_params = [p for n, p in model.named_parameters() if 'crf' in n]
        optimizer = torch.optim.AdamW([
            {'params': bert_params, 'lr': learning_rate, 'weight_decay': weight_decay},
            {'params': crf_params, 'lr': crf_lr, 'weight_decay': 0.0},
        ])
    else:
        optimizer = torch.optim.AdamW(
            model.parameters(), lr=learning_rate, weight_decay=weight_decay
        )

    # Gradient accumulation adjustments
    accum = max(1, gradient_accumulation_steps)
    steps_per_epoch = (len(train_loader) + accum - 1) // accum
    total_steps = steps_per_epoch * epochs
    warmup_steps = int(total_steps * warmup_ratio)
    scheduler = get_linear_schedule_with_warmup(optimizer, warmup_steps, total_steps)

    # Mixed precision
    amp_enabled = use_amp and device.startswith('cuda')
    scaler = torch.amp.GradScaler() if amp_enabled else None
    if amp_enabled:
        logger.info("Mixed precision (AMP) enabled")
    if accum > 1:
        logger.info(f"Gradient accumulation: {accum} steps (effective batch {batch_size * accum})")

    # Optional tqdm
    try:
        from tqdm.auto import tqdm as _tqdm
    except ImportError:
        _tqdm = None

    # Training loop
    best_f1 = -1.0
    best_results = None
    patience_counter = 0
    start_epoch = 0
    PATIENCE = patience
    MIN_EPOCHS = min_epochs

    # Resume from checkpoint if provided
    _resumed = False
    if resume_from and Path(resume_from).exists():
        ckpt = torch.load(resume_from, map_location=device, weights_only=False)
        ckpt_epoch = ckpt['epoch'] + 1
        ckpt_tags = ckpt.get('tag_scheme_tags')

        # Validate: architecture + tag scheme must match
        skip_reason = None
        ckpt_multi_head = ckpt.get('multi_head', False)
        ckpt_parser_features = ckpt.get('use_parser_features', False)
        if ckpt_multi_head != multi_head:
            skip_reason = (f"architecture mismatch: checkpoint is "
                           f"{'multi-head' if ckpt_multi_head else 'single-head'}, "
                           f"current is {'multi-head' if multi_head else 'single-head'}")
        elif ckpt_parser_features != use_parser_features:
            skip_reason = (f"parser features mismatch: checkpoint has "
                           f"parser_features={ckpt_parser_features}, "
                           f"current has parser_features={use_parser_features}")
        elif ckpt_tags is not None and ckpt_tags != tag_scheme.tags:
            skip_reason = (f"tag scheme mismatch: checkpoint has "
                           f"{len(ckpt_tags)} tags, current has "
                           f"{tag_scheme.num_tags} tags")
        elif ckpt_epoch >= epochs:
            skip_reason = (f"checkpoint is from completed run "
                           f"(epoch {ckpt_epoch}/{epochs})")

        if skip_reason:
            logger.warning(f"Skipping resume: {skip_reason}. "
                           f"Starting fresh.")
        else:
            model.load_state_dict(ckpt['model_state_dict'])
            optimizer.load_state_dict(ckpt['optimizer_state_dict'])
            scheduler.load_state_dict(ckpt['scheduler_state_dict'])
            if scaler is not None and 'scaler_state_dict' in ckpt:
                scaler.load_state_dict(ckpt['scaler_state_dict'])
            start_epoch = ckpt_epoch
            patience_counter = ckpt.get('patience_counter', 0)
            # Evaluate resumed model to populate best_results
            best_results = _evaluate_model(
                model, dev_dataset, dev_docs, tag_scheme, device,
                batch_size, use_amp=amp_enabled,
            )
            best_f1 = best_results["overall_f1"]
            ckpt_f1 = ckpt.get('best_f1', -1.0)
            logger.info(f"Resumed from epoch {start_epoch}, "
                        f"checkpoint F1={ckpt_f1:.4f}, "
                        f"evaluated F1={best_f1:.4f}")
            # Sanity check: if evaluated F1 is way below checkpoint's,
            # the model is likely corrupted or tag scheme drifted
            if best_f1 < 0.10 and ckpt_f1 > 0.30:
                logger.warning(
                    f"Resumed model F1 ({best_f1:.4f}) is far below "
                    f"checkpoint F1 ({ckpt_f1:.4f}) — likely corrupted "
                    f"or tag scheme drift. Starting fresh.")
                # Reset model to pretrained weights
                if multi_head:
                    ModelClass = _build_multihead_model_class()
                    model = ModelClass(model_name, sorted_rules, tag_scheme,
                                       focal_gamma=focal_gamma,
                                       per_head_weights=per_head_weights,
                                       use_parser_features=use_parser_features)
                else:
                    ModelClass = _build_model_class()
                    model = ModelClass(model_name, tag_scheme.num_tags,
                                       use_crf=use_crf,
                                       class_weights=class_weights,
                                       focal_gamma=focal_gamma)
                model.to(device)
                if not multi_head and model.use_crf:
                    bert_params = [p for n, p in model.named_parameters()
                                   if 'crf' not in n]
                    crf_params = [p for n, p in model.named_parameters()
                                  if 'crf' in n]
                    optimizer = torch.optim.AdamW([
                        {'params': bert_params, 'lr': learning_rate,
                         'weight_decay': weight_decay},
                        {'params': crf_params, 'lr': crf_lr,
                         'weight_decay': 0.0},
                    ])
                else:
                    optimizer = torch.optim.AdamW(
                        model.parameters(), lr=learning_rate,
                        weight_decay=weight_decay)
                scheduler = get_linear_schedule_with_warmup(
                    optimizer, warmup_steps, total_steps)
                if amp_enabled:
                    scaler = torch.amp.GradScaler()
                start_epoch = 0
                best_f1 = -1.0
                best_results = None
                patience_counter = 0
            else:
                _resumed = True

    logger.info(f"Training for up to {epochs} epochs (early stop: patience={PATIENCE}, min={MIN_EPOCHS})")

    for epoch in range(start_epoch, epochs):
        model.train()
        total_loss = 0.0
        n_batches = len(train_loader)
        optimizer.zero_grad()

        if _tqdm:
            pbar = _tqdm(train_loader, desc=f"Epoch {epoch+1}/{epochs}", leave=False)
        else:
            pbar = train_loader

        for batch_idx, batch in enumerate(pbar):
            input_ids = batch['input_ids'].to(device, non_blocking=pin)
            attention_mask = batch['attention_mask'].to(device, non_blocking=pin)
            labels = batch['labels'].to(device, non_blocking=pin)
            pf = batch.get('parser_features')
            if pf is not None:
                pf = pf.to(device, non_blocking=pin)

            if amp_enabled:
                with torch.amp.autocast(device_type='cuda'):
                    loss = model(input_ids, attention_mask, labels,
                                 parser_features=pf)
                scaled_loss = loss / accum
                scaler.scale(scaled_loss).backward()

                if (batch_idx + 1) % accum == 0 or (batch_idx + 1) == n_batches:
                    scaler.unscale_(optimizer)
                    torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                    scaler.step(optimizer)
                    scaler.update()
                    scheduler.step()
                    optimizer.zero_grad()
            else:
                loss = model(input_ids, attention_mask, labels,
                             parser_features=pf)
                scaled_loss = loss / accum
                scaled_loss.backward()

                if (batch_idx + 1) % accum == 0 or (batch_idx + 1) == n_batches:
                    torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                    optimizer.step()
                    scheduler.step()
                    optimizer.zero_grad()

            total_loss += loss.item()

            # Progress updates
            if _tqdm and hasattr(pbar, 'set_postfix'):
                pbar.set_postfix(loss=f"{total_loss / (batch_idx + 1):.4f}")
            elif not _tqdm and (batch_idx + 1) % 500 == 0:
                avg_so_far = total_loss / (batch_idx + 1)
                logger.info(f"  Epoch {epoch+1} batch {batch_idx+1}/{n_batches}: "
                           f"loss={avg_so_far:.4f}")

        if _tqdm and hasattr(pbar, 'close'):
            pbar.close()

        avg_loss = total_loss / max(n_batches, 1)

        # Evaluate on dev
        dev_results = _evaluate_model(
            model, dev_dataset, dev_docs, tag_scheme, device, batch_size,
            use_amp=amp_enabled,
        )
        f1 = dev_results["overall_f1"]
        n_pred = sum(v['tp'] + v['fp'] for v in dev_results.get('per_rule', {}).values())

        logger.info(f"Epoch {epoch+1}/{epochs}: loss={avg_loss:.4f}, "
                    f"dev_f1={f1:.4f}, pred_spans={n_pred}")

        if f1 > best_f1:
            best_f1 = f1
            best_results = dev_results
            patience_counter = 0
            Path(output_dir).mkdir(parents=True, exist_ok=True)
            torch.save(model.state_dict(), f"{output_dir}/best_model.pt")
            with open(f"{output_dir}/tag_scheme.json", 'w') as fp:
                json.dump({"tags": tag_scheme.tags}, fp)
            # Full checkpoint for resume after disconnection
            ckpt = {
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'scheduler_state_dict': scheduler.state_dict(),
                'best_f1': best_f1,
                'patience_counter': 0,
                'tag_scheme_tags': tag_scheme.tags,
                'multi_head': multi_head,
                'use_parser_features': use_parser_features,
            }
            if scaler is not None:
                ckpt['scaler_state_dict'] = scaler.state_dict()
            torch.save(ckpt, f"{output_dir}/training_checkpoint.pt")
            if save_callback:
                save_callback(output_dir, epoch, f1)
        else:
            patience_counter += 1
            if patience_counter >= PATIENCE and epoch >= MIN_EPOCHS:
                logger.info(f"Early stopping at epoch {epoch+1} (patience={PATIENCE})")
                break

    logger.info(f"Best dev F1: {best_f1:.4f}")

    if best_results:
        best_results["model"] = f"bert-crf ({model_name})"
        best_results["seed"] = seed
        best_results["epochs"] = epochs

    return best_results or {"overall_f1": 0.0, "delta": 1.0, "model": model_name}


def _load_jsonl(path: str) -> List[Dict]:
    docs = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                docs.append(json.loads(line))
    return docs


def _evaluate_model(
    model,
    dev_dataset: SpanDataset,
    dev_docs: List[Dict],
    tag_scheme: TagScheme,
    device: str,
    batch_size: int = 16,
    use_amp: bool = False,
) -> Dict[str, Any]:
    """Evaluate with proper subword→character alignment."""
    from ml.evaluate import evaluate
    from torch.utils.data import DataLoader

    model.eval()
    amp_eval = use_amp and device.startswith('cuda')

    # Run inference
    dev_loader = DataLoader(dev_dataset, batch_size=batch_size, shuffle=False)
    all_subword_preds = []  # list of lists of tag indices

    with torch.no_grad():
        for batch in dev_loader:
            input_ids = batch['input_ids'].to(device)
            attention_mask = batch['attention_mask'].to(device)
            pf = batch.get('parser_features')
            if pf is not None:
                pf = pf.to(device)

            if amp_eval:
                with torch.amp.autocast(device_type='cuda'):
                    tag_indices = model(input_ids, attention_mask,
                                        parser_features=pf)
            else:
                tag_indices = model(input_ids, attention_mask,
                                    parser_features=pf)

            for seq in tag_indices:
                if isinstance(seq, list):
                    all_subword_preds.append(seq)
                else:
                    all_subword_preds.append([t.item() for t in seq])

    # Project subword predictions back to character-level
    gold_tags_list = []
    pred_tags_list = []

    for i, doc in enumerate(dev_docs):
        if i >= len(all_subword_preds):
            break

        gold_chars = doc["bio_tags"]
        text_len = len(doc["text"])
        offsets = dev_dataset.items[i]['offsets']

        pred_chars = subword_preds_to_char_tags(
            all_subword_preds[i], offsets, text_len, tag_scheme
        )

        gold_tags_list.append(gold_chars)
        pred_tags_list.append(pred_chars)

    return evaluate(gold_tags_list, pred_tags_list, "bert-crf", 42)


# ── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="BERT+CRF span extractor")
    parser.add_argument("--train", required=True)
    parser.add_argument("--dev", required=True)
    parser.add_argument("--output", default="ml/eval_bert_crf.json")
    parser.add_argument("--model-name", default="allenai/scibert_scivocab_uncased")
    parser.add_argument("--max-length", type=int, default=128)
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--epochs", type=int, default=20)
    parser.add_argument("--lr", type=float, default=3e-5)
    parser.add_argument("--crf-lr", type=float, default=1e-3)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--device", default="cpu")
    parser.add_argument("--output-dir", default="ml/checkpoints")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    results = train_bert_crf(
        args.train, args.dev,
        model_name=args.model_name,
        max_length=args.max_length,
        batch_size=args.batch_size,
        epochs=args.epochs,
        learning_rate=args.lr,
        crf_lr=args.crf_lr,
        seed=args.seed,
        device=args.device,
        output_dir=args.output_dir,
    )

    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    with open(args.output, 'w') as f:
        json.dump(results, f, indent=2)
    logger.info(f"F1: {results.get('overall_f1', 0):.4f}, written to {args.output}")


if __name__ == "__main__":
    main()
