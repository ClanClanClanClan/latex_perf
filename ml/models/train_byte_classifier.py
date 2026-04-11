#!/usr/bin/env python3
"""Training loop for the byte-level candidate classifier (v2 pipeline).

Loads candidate JSONL (from build_candidate_dataset.py), trains the
ByteClassifier model, evaluates per-rule precision/recall, and exports
results for the Coq soundness proof.

Usage:
    python -m ml.models.train_byte_classifier \
        --train ml/data/candidates_train.jsonl \
        --dev ml/data/candidates_dev.jsonl \
        --output ml/checkpoints_v2

Designed for Google Colab Pro (A100 GPU).  Supports:
  - Mixed precision (AMP) for fast training
  - Checkpoint saving/resuming (Drive-friendly)
  - Per-rule evaluation with separate precision/recall
  - Early stopping with configurable patience
"""

import json
import logging
import random
import argparse
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional

import numpy as np

logger = logging.getLogger(__name__)

# Lazy torch imports
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


# ── Dataset ──────────────────────────────────────────────────────────────────

def _load_candidates(path: str) -> List[Dict]:
    """Load candidate JSONL records."""
    docs = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                docs.append(json.loads(line))
    return docs


class CandidateDataset:
    """PyTorch-compatible dataset for candidate classification.

    Each item is a dict with tensors ready for ByteClassifier.forward().
    """

    def __init__(self, records: List[Dict], rule_to_idx: Dict[str, int]):
        _import_torch()
        self.items = []
        skipped = 0
        for rec in records:
            rule_id = rec['rule_id']
            if rule_id not in rule_to_idx:
                skipped += 1
                continue
            self.items.append({
                'byte_input': rec['bytes'],
                'anchor_start': rec['anchor_start'],
                'anchor_end': rec['anchor_end'],
                'rule_idx': rule_to_idx[rule_id],
                'rule_id': rule_id,
                'label': rec['label'],
                'parser_features': [
                    float(rec.get('in_math', False)),
                    float(rec.get('in_verbatim', False)),
                    float(rec.get('in_comment', False)),
                    float(rec.get('env_depth', 0)) / 10.0,  # normalise depth
                ],
            })
        if skipped:
            logger.info(f"Skipped {skipped} records with unknown rule_id")

    def __len__(self):
        return len(self.items)

    def __getitem__(self, idx):
        item = self.items[idx]
        return {
            'byte_input': torch.tensor(item['byte_input'], dtype=torch.long),
            'anchor_start': torch.tensor(item['anchor_start'], dtype=torch.long),
            'anchor_end': torch.tensor(item['anchor_end'], dtype=torch.long),
            'rule_id': torch.tensor(item['rule_idx'], dtype=torch.long),
            'parser_features': torch.tensor(item['parser_features'],
                                            dtype=torch.float32),
            'label': torch.tensor(item['label'], dtype=torch.float32),
        }


# ── Evaluation ───────────────────────────────────────────────────────────────

def evaluate_candidates(
    model,
    dataset: CandidateDataset,
    device: str = 'cpu',
    batch_size: int = 256,
    threshold: float = 0.5,
    use_amp: bool = False,
) -> Dict[str, Any]:
    """Evaluate candidate classifier, returning per-rule precision/recall.

    Args:
        model: ByteClassifier instance
        dataset: CandidateDataset
        device: 'cpu' or 'cuda'
        batch_size: evaluation batch size
        threshold: classification threshold for P(violation)
        use_amp: use mixed precision

    Returns:
        Dict with overall and per-rule metrics:
        {
            'overall_precision', 'overall_recall', 'overall_f1',
            'overall_accuracy',
            'per_rule': {rule_id: {precision, recall, f1, tp, fp, fn, tn}},
            'threshold': float,
        }
    """
    from torch.utils.data import DataLoader
    from ml.models.byte_classifier import IDX_TO_RULE

    model.eval()
    all_preds = []
    all_labels = []
    all_rule_idxs = []

    loader = DataLoader(dataset, batch_size=batch_size, shuffle=False)

    with torch.no_grad():
        for batch in loader:
            byte_input = batch['byte_input'].to(device)
            anchor_start = batch['anchor_start'].to(device)
            anchor_end = batch['anchor_end'].to(device)
            rule_id = batch['rule_id'].to(device)
            parser_features = batch['parser_features'].to(device)

            if use_amp and device.startswith('cuda'):
                with torch.amp.autocast(device_type='cuda'):
                    probs = model(byte_input, anchor_start, anchor_end,
                                  rule_id, parser_features)
            else:
                probs = model(byte_input, anchor_start, anchor_end,
                              rule_id, parser_features)

            preds = (probs >= threshold).long()
            all_preds.extend(preds.cpu().tolist())
            all_labels.extend(batch['label'].long().tolist())
            all_rule_idxs.extend(batch['rule_id'].tolist())

    # Per-rule metrics
    per_rule = defaultdict(lambda: {'tp': 0, 'fp': 0, 'fn': 0, 'tn': 0})
    for pred, label, ridx in zip(all_preds, all_labels, all_rule_idxs):
        rule_id = IDX_TO_RULE.get(ridx, f'rule-{ridx}')
        if pred == 1 and label == 1:
            per_rule[rule_id]['tp'] += 1
        elif pred == 1 and label == 0:
            per_rule[rule_id]['fp'] += 1
        elif pred == 0 and label == 1:
            per_rule[rule_id]['fn'] += 1
        else:
            per_rule[rule_id]['tn'] += 1

    # Compute F1 per rule
    results_per_rule = {}
    total_tp = total_fp = total_fn = total_tn = 0
    for rule_id, counts in sorted(per_rule.items()):
        tp, fp, fn, tn = counts['tp'], counts['fp'], counts['fn'], counts['tn']
        total_tp += tp
        total_fp += fp
        total_fn += fn
        total_tn += tn
        prec = tp / max(tp + fp, 1)
        rec = tp / max(tp + fn, 1)
        f1 = 2 * prec * rec / max(prec + rec, 1e-9)
        results_per_rule[rule_id] = {
            'precision': round(prec, 4),
            'recall': round(rec, 4),
            'f1': round(f1, 4),
            'tp': tp, 'fp': fp, 'fn': fn, 'tn': tn,
        }

    # Overall metrics
    overall_prec = total_tp / max(total_tp + total_fp, 1)
    overall_rec = total_tp / max(total_tp + total_fn, 1)
    overall_f1 = 2 * overall_prec * overall_rec / max(
        overall_prec + overall_rec, 1e-9)
    overall_acc = (total_tp + total_tn) / max(
        total_tp + total_fp + total_fn + total_tn, 1)

    return {
        'overall_precision': round(overall_prec, 4),
        'overall_recall': round(overall_rec, 4),
        'overall_f1': round(overall_f1, 4),
        'overall_accuracy': round(overall_acc, 4),
        'per_rule': results_per_rule,
        'threshold': threshold,
        'total_tp': total_tp,
        'total_fp': total_fp,
        'total_fn': total_fn,
        'total_tn': total_tn,
    }


# ── Training ─────────────────────────────────────────────────────────────────

def set_seed(seed: int):
    random.seed(seed)
    np.random.seed(seed)
    _import_torch()
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def train_byte_classifier(
    train_jsonl: str,
    dev_jsonl: str,
    num_rules: int = 8,
    context_size: int = 128,
    batch_size: int = 256,
    epochs: int = 50,
    learning_rate: float = 1e-3,
    weight_decay: float = 1e-5,
    patience: int = 10,
    min_epochs: int = 5,
    threshold: float = 0.5,
    seed: int = 42,
    device: str = 'cpu',
    output_dir: str = 'ml/checkpoints_v2',
    use_amp: bool = False,
    save_callback=None,
    resume_from: Optional[str] = None,
) -> Dict[str, Any]:
    """Train the byte-level candidate classifier.

    Args:
        train_jsonl: path to training candidate JSONL
        dev_jsonl: path to dev candidate JSONL
        num_rules: number of ambiguous rules (default 8)
        context_size: byte context window size (default 128)
        batch_size: training batch size (default 256)
        epochs: maximum training epochs (default 50)
        learning_rate: Adam learning rate (default 1e-3)
        weight_decay: L2 regularization (default 1e-5)
        patience: early stopping patience (default 10)
        min_epochs: minimum epochs before early stopping (default 5)
        threshold: classification threshold (default 0.5)
        seed: random seed (default 42)
        device: 'cpu' or 'cuda'
        output_dir: checkpoint output directory
        use_amp: use mixed precision training
        save_callback: optional fn(output_dir, epoch, f1) called on improvement
        resume_from: path to checkpoint for resuming

    Returns:
        Dict with evaluation results from best epoch
    """
    _import_torch()
    from torch.utils.data import DataLoader
    from ml.models.byte_classifier import (
        build_byte_classifier, count_parameters, RULE_TO_IDX,
    )

    set_seed(seed)

    # Load data
    logger.info(f"Loading training data from {train_jsonl}...")
    train_records = _load_candidates(train_jsonl)
    dev_records = _load_candidates(dev_jsonl)
    logger.info(f"Train: {len(train_records)} candidates, "
                f"Dev: {len(dev_records)} candidates")

    # Count class balance
    train_pos = sum(1 for r in train_records if r['label'] == 1)
    train_neg = len(train_records) - train_pos
    logger.info(f"Train balance: {train_pos} pos ({100*train_pos/max(len(train_records),1):.1f}%), "
                f"{train_neg} neg")

    # Datasets
    train_dataset = CandidateDataset(train_records, RULE_TO_IDX)
    dev_dataset = CandidateDataset(dev_records, RULE_TO_IDX)
    logger.info(f"Datasets: {len(train_dataset)} train, {len(dev_dataset)} dev")

    pin = device.startswith('cuda')
    train_loader = DataLoader(
        train_dataset, batch_size=batch_size, shuffle=True,
        pin_memory=pin, num_workers=2 if pin else 0,
    )
    dev_loader = DataLoader(
        dev_dataset, batch_size=batch_size, shuffle=False,
        pin_memory=pin,
    )

    # Model
    ByteClassifier = build_byte_classifier()
    model = ByteClassifier(num_rules=num_rules, context_size=context_size)
    model.to(device)
    n_params = count_parameters(model)
    logger.info(f"ByteClassifier on {device}: {n_params:,} parameters")

    # Optimizer + scheduler
    optimizer = torch.optim.Adam(
        model.parameters(), lr=learning_rate, weight_decay=weight_decay)
    scheduler = torch.optim.lr_scheduler.ReduceLROnPlateau(
        optimizer, mode='max', patience=5, factor=0.5, min_lr=1e-6)

    # Loss: binary cross-entropy (candidates are ~balanced, no class weighting)
    criterion = nn.BCELoss()

    # Mixed precision
    amp_enabled = use_amp and device.startswith('cuda')
    scaler = torch.amp.GradScaler() if amp_enabled else None
    if amp_enabled:
        logger.info("Mixed precision (AMP) enabled")

    # Optional tqdm
    try:
        from tqdm.auto import tqdm as _tqdm
    except ImportError:
        _tqdm = None

    # Training state
    best_f1 = -1.0
    best_results = None
    patience_counter = 0
    start_epoch = 0

    # Resume from checkpoint
    if resume_from and Path(resume_from).exists():
        ckpt = torch.load(resume_from, map_location=device, weights_only=False)
        model.load_state_dict(ckpt['model_state_dict'])
        optimizer.load_state_dict(ckpt['optimizer_state_dict'])
        if 'scheduler_state_dict' in ckpt:
            scheduler.load_state_dict(ckpt['scheduler_state_dict'])
        start_epoch = ckpt.get('epoch', 0) + 1
        best_f1 = ckpt.get('best_f1', -1.0)
        patience_counter = ckpt.get('patience_counter', 0)
        if amp_enabled and 'scaler_state_dict' in ckpt:
            scaler.load_state_dict(ckpt['scaler_state_dict'])
        logger.info(f"Resumed from epoch {start_epoch}, best_f1={best_f1:.4f}")

    logger.info(f"Training for up to {epochs} epochs "
                f"(patience={patience}, min={min_epochs})")

    for epoch in range(start_epoch, epochs):
        model.train()
        total_loss = 0.0
        n_batches = len(train_loader)

        if _tqdm:
            pbar = _tqdm(train_loader, desc=f"Epoch {epoch+1}/{epochs}",
                         leave=False)
        else:
            pbar = train_loader

        for batch_idx, batch in enumerate(pbar):
            byte_input = batch['byte_input'].to(device, non_blocking=pin)
            anchor_start = batch['anchor_start'].to(device, non_blocking=pin)
            anchor_end = batch['anchor_end'].to(device, non_blocking=pin)
            rule_id = batch['rule_id'].to(device, non_blocking=pin)
            parser_features = batch['parser_features'].to(device,
                                                          non_blocking=pin)
            labels = batch['label'].to(device, non_blocking=pin)

            optimizer.zero_grad()

            if amp_enabled:
                with torch.amp.autocast(device_type='cuda'):
                    probs = model(byte_input, anchor_start, anchor_end,
                                  rule_id, parser_features)
                    loss = criterion(probs, labels)
                scaler.scale(loss).backward()
                scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                scaler.step(optimizer)
                scaler.update()
            else:
                probs = model(byte_input, anchor_start, anchor_end,
                              rule_id, parser_features)
                loss = criterion(probs, labels)
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                optimizer.step()

            total_loss += loss.item()

            if _tqdm and hasattr(pbar, 'set_postfix'):
                pbar.set_postfix(loss=f"{total_loss/(batch_idx+1):.4f}")

        if _tqdm and hasattr(pbar, 'close'):
            pbar.close()

        avg_loss = total_loss / max(n_batches, 1)

        # Evaluate on dev
        dev_results = evaluate_candidates(
            model, dev_dataset, device, batch_size, threshold, use_amp)
        f1 = dev_results['overall_f1']
        scheduler.step(f1)

        current_lr = optimizer.param_groups[0]['lr']
        logger.info(f"Epoch {epoch+1}/{epochs}: loss={avg_loss:.4f}, "
                    f"dev_f1={f1:.4f}, prec={dev_results['overall_precision']:.4f}, "
                    f"rec={dev_results['overall_recall']:.4f}, "
                    f"lr={current_lr:.2e}")

        if f1 > best_f1:
            best_f1 = f1
            best_results = dev_results
            patience_counter = 0

            # Save checkpoint
            Path(output_dir).mkdir(parents=True, exist_ok=True)
            torch.save(model.state_dict(), f"{output_dir}/best_model.pt")

            ckpt = {
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'scheduler_state_dict': scheduler.state_dict(),
                'best_f1': best_f1,
                'patience_counter': 0,
            }
            if scaler is not None:
                ckpt['scaler_state_dict'] = scaler.state_dict()
            torch.save(ckpt, f"{output_dir}/training_checkpoint.pt")

            # Save results
            with open(f"{output_dir}/eval_results.json", 'w') as fp:
                json.dump(dev_results, fp, indent=2)

            if save_callback:
                save_callback(output_dir, epoch, f1)
        else:
            patience_counter += 1
            # Periodic checkpoint every 5 epochs (survives disconnection)
            if epoch % 5 == 4:
                ckpt = {
                    'epoch': epoch,
                    'model_state_dict': model.state_dict(),
                    'optimizer_state_dict': optimizer.state_dict(),
                    'scheduler_state_dict': scheduler.state_dict(),
                    'best_f1': best_f1,
                    'patience_counter': patience_counter,
                }
                if scaler is not None:
                    ckpt['scaler_state_dict'] = scaler.state_dict()
                torch.save(ckpt, f"{output_dir}/training_checkpoint.pt")
                if save_callback:
                    save_callback(output_dir, epoch, best_f1)
                logger.info(f"Periodic checkpoint saved (epoch {epoch+1})")
            if patience_counter >= patience and epoch >= min_epochs:
                logger.info(f"Early stopping at epoch {epoch+1} "
                           f"(patience={patience})")
                break

    logger.info(f"Best dev F1: {best_f1:.4f}")

    if best_results:
        best_results['model'] = 'byte-classifier'
        best_results['seed'] = seed
        best_results['epochs'] = epochs
        # Compute separate bounds for Coq proof
        best_results['measured_fp_rate'] = round(
            1.0 - best_results['overall_precision'], 4)
        best_results['measured_fn_rate'] = round(
            1.0 - best_results['overall_recall'], 4)

    return best_results or {
        'overall_f1': 0.0, 'overall_precision': 0.0, 'overall_recall': 0.0,
        'model': 'byte-classifier',
    }


# ── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Train byte-level candidate classifier (v2)")
    parser.add_argument("--train", required=True,
                        help="Training candidate JSONL")
    parser.add_argument("--dev", required=True,
                        help="Dev candidate JSONL")
    parser.add_argument("--output", default="ml/checkpoints_v2",
                        help="Output directory for checkpoints")
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--patience", type=int, default=10)
    parser.add_argument("--threshold", type=float, default=0.5)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--device", default="cpu")
    parser.add_argument("--amp", action="store_true",
                        help="Enable mixed precision")
    parser.add_argument("--resume", default=None,
                        help="Resume from checkpoint")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    results = train_byte_classifier(
        train_jsonl=args.train,
        dev_jsonl=args.dev,
        batch_size=args.batch_size,
        epochs=args.epochs,
        learning_rate=args.lr,
        patience=args.patience,
        threshold=args.threshold,
        seed=args.seed,
        device=args.device,
        output_dir=args.output,
        use_amp=args.amp,
        resume_from=args.resume,
    )

    print(f"\n{'='*60}")
    print(f"Byte Classifier Results:")
    print(f"  F1:        {results.get('overall_f1', 0):.4f}")
    print(f"  Precision: {results.get('overall_precision', 0):.4f}")
    print(f"  Recall:    {results.get('overall_recall', 0):.4f}")
    print(f"  FP rate:   {results.get('measured_fp_rate', 1):.4f}")
    print(f"  FN rate:   {results.get('measured_fn_rate', 1):.4f}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
