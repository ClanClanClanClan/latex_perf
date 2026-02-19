#!/usr/bin/env python3
"""BERT + CRF span extractor for LaTeX error detection.

Uses a BERT encoder (allenai/scibert for domain coverage) with a CRF layer
on top for structured BIO prediction. Designed for fine-tuning on Google
Colab Pro (A100/V100 GPU).

Architecture:
    Input text → BERT subword tokenizer → BERT encoder → CRF layer → BIO tags

Training:
    AdamW optimizer, linear warmup, batch size 16, 5 epochs, seed 42.

Usage:
    python -m ml.models.bert_crf --train data/train.jsonl --dev data/dev.jsonl
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
    import torch as _torch
    import torch.nn as _nn
    torch = _torch
    nn = _nn
    try:
        from torchcrf import CRF as _CRF
        CRF = _CRF
    except ImportError:
        logger.warning("torchcrf not installed — CRF layer unavailable, using greedy decoding")
        CRF = None


# ── Tag scheme ───────────────────────────────────────────────────────────────

class TagScheme:
    """BIO tag ↔ index mapping."""

    def __init__(self, rule_ids: List[str]):
        """Build tag scheme from rule IDs.

        Tags: O, B-{rule}, I-{rule} for each rule.
        """
        self.tags = ["O"]
        for rule in sorted(set(rule_ids)):
            self.tags.append(f"B-{rule}")
            self.tags.append(f"I-{rule}")
        self.tag_to_idx = {t: i for i, t in enumerate(self.tags)}
        self.idx_to_tag = {i: t for t, i in self.tag_to_idx.items()}
        self.num_tags = len(self.tags)

    def encode(self, tag: str) -> int:
        return self.tag_to_idx.get(tag, 0)  # Unknown → O

    def decode(self, idx: int) -> str:
        return self.idx_to_tag.get(idx, "O")

    def encode_sequence(self, tags: List[str]) -> List[int]:
        return [self.encode(t) for t in tags]

    def decode_sequence(self, indices: List[int]) -> List[str]:
        return [self.decode(i) for i in indices]


# ── Dataset ──────────────────────────────────────────────────────────────────

class SpanDataset:
    """Dataset of (text, BIO tags) pairs for BERT+CRF.

    Handles subword tokenization with alignment back to character-level tags.
    """

    def __init__(
        self,
        texts: List[str],
        bio_tags: List[List[str]],
        tag_scheme: TagScheme,
        tokenizer,
        max_length: int = 512,
    ):
        self.texts = texts
        self.bio_tags = bio_tags
        self.tag_scheme = tag_scheme
        self.tokenizer = tokenizer
        self.max_length = max_length

    def __len__(self):
        return len(self.texts)

    def __getitem__(self, idx):
        text = self.texts[idx]
        tags = self.bio_tags[idx]

        # Tokenize with offset mapping for alignment
        encoding = self.tokenizer(
            text,
            max_length=self.max_length,
            truncation=True,
            padding='max_length',
            return_tensors='pt',
            return_offsets_mapping=True,
        )

        # Align tags to subword tokens
        offsets = encoding['offset_mapping'][0]
        aligned_tags = []
        for start, end in offsets:
            if start == 0 and end == 0:
                # Special token ([CLS], [SEP], [PAD])
                aligned_tags.append(0)  # O tag
            else:
                # Use tag of the first character in the subword
                char_idx = start
                if char_idx < len(tags):
                    aligned_tags.append(self.tag_scheme.encode(tags[char_idx]))
                else:
                    aligned_tags.append(0)

        return {
            'input_ids': encoding['input_ids'].squeeze(0),
            'attention_mask': encoding['attention_mask'].squeeze(0),
            'labels': torch.tensor(aligned_tags, dtype=torch.long),
            'offset_mapping': offsets,
        }


# ── Model ────────────────────────────────────────────────────────────────────

class BertCRFSpanExtractor(nn.Module if nn else object):
    """BERT + optional CRF for BIO sequence labeling."""

    def __init__(
        self,
        model_name: str,
        num_tags: int,
        use_crf: bool = True,
        dropout: float = 0.1,
    ):
        if nn is None:
            _import_torch()
        super().__init__()

        from transformers import AutoModel

        self.bert = AutoModel.from_pretrained(model_name)
        self.dropout = nn.Dropout(dropout)
        self.classifier = nn.Linear(self.bert.config.hidden_size, num_tags)
        self.use_crf = use_crf and CRF is not None
        if self.use_crf:
            self.crf = CRF(num_tags, batch_first=True)
        self.num_tags = num_tags

    def forward(
        self,
        input_ids,
        attention_mask,
        labels=None,
    ):
        outputs = self.bert(input_ids=input_ids, attention_mask=attention_mask)
        sequence_output = self.dropout(outputs.last_hidden_state)
        emissions = self.classifier(sequence_output)

        if labels is not None:
            if self.use_crf:
                # CRF loss (negative log-likelihood)
                loss = -self.crf(emissions, labels, mask=attention_mask.bool())
                return loss
            else:
                # Cross-entropy loss
                loss_fn = nn.CrossEntropyLoss(ignore_index=-100)
                # Reshape for cross-entropy
                active = attention_mask.view(-1) == 1
                active_logits = emissions.view(-1, self.num_tags)[active]
                active_labels = labels.view(-1)[active]
                loss = loss_fn(active_logits, active_labels)
                return loss
        else:
            if self.use_crf:
                # CRF decode
                tags = self.crf.decode(emissions, mask=attention_mask.bool())
                return tags
            else:
                # Greedy decode
                tags = emissions.argmax(dim=-1)
                return tags.tolist()


# ── Training loop ────────────────────────────────────────────────────────────

def set_seed(seed: int):
    """Set all random seeds for reproducibility."""
    random.seed(seed)
    np.random.seed(seed)
    if torch is not None:
        torch.manual_seed(seed)
        if torch.cuda.is_available():
            torch.cuda.manual_seed_all(seed)


def train_bert_crf(
    train_jsonl: str,
    dev_jsonl: str,
    model_name: str = "allenai/scibert_scivocab_uncased",
    max_length: int = 512,
    batch_size: int = 16,
    epochs: int = 5,
    learning_rate: float = 2e-5,
    warmup_ratio: float = 0.1,
    weight_decay: float = 0.01,
    crf_lr: float = 1e-3,
    seed: int = 42,
    device: str = "cpu",
    output_dir: str = "ml/checkpoints",
) -> Dict[str, Any]:
    """Full BERT+CRF training pipeline.

    Returns evaluation results dict.
    """
    _import_torch()
    from torch.utils.data import DataLoader
    from transformers import AutoTokenizer, get_linear_schedule_with_warmup
    from ml.evaluate import evaluate

    set_seed(seed)

    # Load data
    logger.info(f"Loading data from {train_jsonl} and {dev_jsonl}...")
    train_docs = _load_jsonl(train_jsonl)
    dev_docs = _load_jsonl(dev_jsonl)

    # Build tag scheme from all rules
    all_rules = set()
    for doc in train_docs + dev_docs:
        for tag in doc["bio_tags"]:
            if tag != "O":
                rule = tag.split("-", 1)[1]
                all_rules.add(rule)
    tag_scheme = TagScheme(sorted(all_rules))
    logger.info(f"Tag scheme: {tag_scheme.num_tags} tags for {len(all_rules)} rules")

    # Tokenizer
    logger.info(f"Loading tokenizer: {model_name}")
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    # Datasets
    train_dataset = SpanDataset(
        [d["text"] for d in train_docs],
        [d["bio_tags"] for d in train_docs],
        tag_scheme, tokenizer, max_length,
    )
    dev_dataset = SpanDataset(
        [d["text"] for d in dev_docs],
        [d["bio_tags"] for d in dev_docs],
        tag_scheme, tokenizer, max_length,
    )

    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    dev_loader = DataLoader(dev_dataset, batch_size=batch_size, shuffle=False)

    # Model
    logger.info(f"Building BERT+CRF model on {device}")
    model = BertCRFSpanExtractor(model_name, tag_scheme.num_tags, use_crf=True)
    model.to(device)

    # Optimizer with separate LR for CRF
    bert_params = [p for n, p in model.named_parameters() if 'crf' not in n]
    crf_params = [p for n, p in model.named_parameters() if 'crf' in n]
    optimizer = torch.optim.AdamW([
        {'params': bert_params, 'lr': learning_rate, 'weight_decay': weight_decay},
        {'params': crf_params, 'lr': crf_lr, 'weight_decay': 0.0},
    ])

    # Scheduler
    total_steps = len(train_loader) * epochs
    warmup_steps = int(total_steps * warmup_ratio)
    scheduler = get_linear_schedule_with_warmup(
        optimizer, warmup_steps, total_steps
    )

    # Training
    best_f1 = 0.0
    best_results = None

    for epoch in range(epochs):
        model.train()
        total_loss = 0.0
        for batch in train_loader:
            input_ids = batch['input_ids'].to(device)
            attention_mask = batch['attention_mask'].to(device)
            labels = batch['labels'].to(device)

            loss = model(input_ids, attention_mask, labels)
            loss.backward()

            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            scheduler.step()
            optimizer.zero_grad()

            total_loss += loss.item()

        avg_loss = total_loss / len(train_loader)

        # Evaluate on dev
        dev_results = _evaluate_model(
            model, dev_loader, dev_docs, tag_scheme, device
        )
        f1 = dev_results["overall_f1"]

        logger.info(f"Epoch {epoch + 1}/{epochs}: loss={avg_loss:.4f}, "
                    f"dev_f1={f1:.4f}")

        if f1 > best_f1:
            best_f1 = f1
            best_results = dev_results
            # Save best model
            Path(output_dir).mkdir(parents=True, exist_ok=True)
            torch.save(model.state_dict(), f"{output_dir}/best_model.pt")
            with open(f"{output_dir}/tag_scheme.json", 'w') as fp:
                json.dump({"tags": tag_scheme.tags}, fp)

    logger.info(f"Best dev F1: {best_f1:.4f}")

    # Add metadata
    if best_results:
        best_results["model"] = f"bert-crf ({model_name})"
        best_results["seed"] = seed
        best_results["epochs"] = epochs
        best_results["best_epoch"] = -1  # Will be set properly with tracking

    return best_results or {}


def _load_jsonl(path: str) -> List[Dict]:
    docs = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                docs.append(json.loads(line))
    return docs


def _evaluate_model(
    model,
    dev_loader,
    dev_docs: List[Dict],
    tag_scheme: TagScheme,
    device: str,
) -> Dict[str, Any]:
    """Evaluate model on dev set."""
    from ml.evaluate import evaluate

    model.eval()
    all_pred_tags = []

    with torch.no_grad():
        for batch in dev_loader:
            input_ids = batch['input_ids'].to(device)
            attention_mask = batch['attention_mask'].to(device)

            tag_indices = model(input_ids, attention_mask)

            # Decode back to tag strings
            for seq_tags in tag_indices:
                if isinstance(seq_tags, list):
                    tags = [tag_scheme.decode(t) for t in seq_tags]
                else:
                    tags = [tag_scheme.decode(t.item()) for t in seq_tags]
                all_pred_tags.append(tags)

    # Align predictions back to character level
    gold_tags_list = [doc["bio_tags"] for doc in dev_docs]

    # Truncate/pad predictions to match gold lengths
    aligned_pred_tags = []
    for i, (gold, pred) in enumerate(zip(gold_tags_list, all_pred_tags)):
        # Simple alignment: take first len(gold) predictions, pad with O
        aligned = pred[:len(gold)] + ['O'] * max(0, len(gold) - len(pred))
        aligned_pred_tags.append(aligned)

    return evaluate(gold_tags_list, aligned_pred_tags, "bert-crf", 42)


# ── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="BERT+CRF span extractor")
    parser.add_argument("--train", required=True, help="Train JSONL")
    parser.add_argument("--dev", required=True, help="Dev JSONL")
    parser.add_argument("--output", default="ml/eval_bert_crf.json",
                        help="Output evaluation results")
    parser.add_argument("--model-name", default="allenai/scibert_scivocab_uncased")
    parser.add_argument("--max-length", type=int, default=512)
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--lr", type=float, default=2e-5)
    parser.add_argument("--crf-lr", type=float, default=1e-3)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--device", default="cpu",
                        help="Device: cpu, cuda, mps")
    parser.add_argument("--output-dir", default="ml/checkpoints",
                        help="Checkpoint directory")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== BERT+CRF Span Extractor ===")
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

    logger.info(f"F1: {results.get('overall_f1', 'N/A')}")
    logger.info(f"Results written to {args.output}")


if __name__ == "__main__":
    main()
