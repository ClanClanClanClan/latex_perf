#!/usr/bin/env python3
"""Local training pipeline for ML span extractor (replaces Colab notebook).

Runs the full pipeline on Apple Silicon (M3 MPS) or CPU:
  1. Download arXiv math papers (1000 papers via OAI-PMH)
  2. Label corpus + arXiv papers with VPD pattern replay
  3. Stratified train/dev split
  4. Extract training windows (300-char, bisect-optimised)
  5. Train BERT+CRF (SciBERT + CRF layer)
  6. Export eval_bound.json for Coq proof

Usage:
    cd Scripts/
    python3 ml/scripts/train_local.py [--skip-arxiv] [--device auto]
"""

import json
import os
import sys
import time
import gzip
import shutil
import tarfile
import random
import logging
import argparse
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import List, Dict, Any, Optional

import yaml

# ── Resolve project root ──────────────────────────────────────────────────
# Script lives at ml/scripts/train_local.py → project root is 2 levels up
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent

# Add project root to path so we can import ml.* modules
sys.path.insert(0, str(PROJECT_ROOT))

logger = logging.getLogger("train_local")


# ── Step 1: ArXiv download ────────────────────────────────────────────────

def download_arxiv_papers(
    output_dir: Path,
    n_papers: int = 1000,
    category: str = "math",
) -> int:
    """Download LaTeX sources from arXiv using direct ID enumeration.

    Generates candidate paper IDs (YYMM.NNNNN format for recent papers)
    and downloads source tarballs from the /e-print/ endpoint.
    Much faster than OAI-PMH (no 20s rate limit).

    Returns number of .tex files successfully downloaded.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    # Check if we already have enough papers
    existing = list(output_dir.glob("*.tex"))
    if len(existing) >= n_papers:
        logger.info(f"ArXiv cache hit: {len(existing)} papers already in {output_dir}")
        return len(existing)

    logger.info(f"Downloading {n_papers} arXiv papers → {output_dir}")

    # Generate candidate IDs from recent months (math papers are dense)
    # Format: YYMM.NNNNN — we try random IDs in recent months
    rng = random.Random(42)
    candidate_ids = []
    # Recent months with many math papers
    months = [
        "2501", "2412", "2411", "2410", "2409", "2408",
        "2407", "2406", "2405", "2404", "2403", "2402",
        "2401", "2312", "2311", "2310", "2309", "2308",
    ]
    for month in months:
        # Each month has ~15000-20000 papers; math papers are roughly IDs 00001-05000
        ids = list(range(1, 6000))
        rng.shuffle(ids)
        for i in ids[:500]:  # 500 candidates per month
            candidate_ids.append(f"{month}.{i:05d}")

    rng.shuffle(candidate_ids)

    downloaded = len(existing)
    errors = 0
    consecutive_errors = 0
    max_consecutive = 20

    for arxiv_id in candidate_ids:
        if downloaded >= n_papers:
            break
        if consecutive_errors >= max_consecutive:
            logger.warning(f"  {max_consecutive} consecutive errors, "
                          f"trying next month batch...")
            consecutive_errors = 0
            continue

        safe_name = arxiv_id.replace("/", "_")
        tex_path = output_dir / f"{safe_name}.tex"
        if tex_path.exists():
            downloaded += 1
            consecutive_errors = 0
            continue

        url = f"https://export.arxiv.org/e-print/{arxiv_id}"
        try:
            req = urllib.request.Request(url, headers={
                "User-Agent": "LatexPerfML/1.0 (research; dylan@perfectionist.dev)"
            })
            with urllib.request.urlopen(req, timeout=30) as resp:
                data = resp.read()

            tex_content = _extract_tex_from_source(data, arxiv_id)
            if tex_content and len(tex_content) > 500:  # Skip trivial files
                tex_path.write_text(tex_content, encoding="utf-8")
                downloaded += 1
                consecutive_errors = 0
                if downloaded % 50 == 0:
                    logger.info(f"  Downloaded {downloaded}/{n_papers} papers")
            else:
                errors += 1
                consecutive_errors += 1

        except urllib.error.HTTPError as e:
            if e.code == 404:
                consecutive_errors += 1
            else:
                errors += 1
                consecutive_errors += 1
        except Exception as e:
            errors += 1
            consecutive_errors += 1
            if errors % 20 == 0:
                logger.debug(f"  Download error ({errors}): {e}")

        # Rate limit: 1 request/sec is fine for e-print
        time.sleep(1)

    logger.info(f"ArXiv download complete: {downloaded} .tex files "
                f"({errors} errors) in {output_dir}")
    return downloaded


def _extract_tex_from_source(data: bytes, arxiv_id: str) -> Optional[str]:
    """Extract the main .tex file from arXiv source data.

    ArXiv source can be: gzipped tar, gzipped single file, or plain TeX.
    """
    import io

    # Try gzipped tar
    try:
        with gzip.open(io.BytesIO(data)) as gz:
            decompressed = gz.read()

        # Check if it's a tarball
        try:
            with tarfile.open(fileobj=io.BytesIO(decompressed)) as tar:
                tex_files = [m for m in tar.getmembers()
                            if m.name.endswith(".tex") and m.isfile()]
                if not tex_files:
                    return None
                # Prefer the largest .tex file (likely the main document)
                main_tex = max(tex_files, key=lambda m: m.size)
                f = tar.extractfile(main_tex)
                if f:
                    content = f.read()
                    try:
                        return content.decode("utf-8")
                    except UnicodeDecodeError:
                        return content.decode("latin-1")
        except tarfile.TarError:
            # Not a tar — plain gzipped TeX
            try:
                text = decompressed.decode("utf-8")
            except UnicodeDecodeError:
                text = decompressed.decode("latin-1")
            if "\\begin{document}" in text or "\\documentclass" in text:
                return text
            return None

    except gzip.BadGzipFile:
        # Plain TeX (not compressed)
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            try:
                text = data.decode("latin-1")
            except Exception:
                return None
        if "\\begin{document}" in text or "\\documentclass" in text:
            return text
        return None
    except Exception:
        return None


# ── Step 2: Labeling ──────────────────────────────────────────────────────

def run_labeling(
    config: Dict,
    arxiv_dir: Optional[Path] = None,
) -> str:
    """Label all corpus files (+ arXiv) with VPD pattern replay."""
    from ml.data.label_spans import run_labeling_pipeline

    paths = config["paths"]
    config_dir = PROJECT_ROOT / "ml"

    # Primary corpus
    corpus_dir = str(config_dir / paths["corpus_dir"])
    vpd_path = str(config_dir / paths["vpd_patterns"])
    golden_path = str(config_dir / paths["golden_yaml"])
    output_path = str(config_dir / paths["labeled_jsonl"])

    # All corpus dirs from config
    corpus_dirs = [str(config_dir / d) for d in paths.get("corpus_dirs", [])]

    # Add arXiv dir if available
    if arxiv_dir and arxiv_dir.is_dir() and list(arxiv_dir.glob("*.tex")):
        corpus_dirs.append(str(arxiv_dir))
        logger.info(f"Including arXiv papers from {arxiv_dir}")

    summary = run_labeling_pipeline(
        corpus_dir=corpus_dir,
        vpd_patterns_path=vpd_path,
        golden_yaml_path=golden_path,
        output_path=output_path,
        corpus_dirs=corpus_dirs,
    )

    logger.info(f"Labeling: {summary['total_documents']} docs, "
                f"{summary['total_spans']} spans, "
                f"{summary['rules_found']} rules")

    return output_path


# ── Step 3: Split ─────────────────────────────────────────────────────────

def run_split(config: Dict, labeled_path: str) -> tuple:
    """Stratified train/dev split."""
    from ml.data.split_data import load_labeled_jsonl, stratified_split, \
        compute_split_stats, write_jsonl

    split_cfg = config.get("split", {})
    train_ratio = split_cfg.get("train_ratio", 0.80)
    seed = config.get("seed", 42)

    config_dir = PROJECT_ROOT / "ml"
    train_path = str(config_dir / config["paths"]["train_jsonl"])
    dev_path = str(config_dir / config["paths"]["dev_jsonl"])

    docs = load_labeled_jsonl(labeled_path)
    logger.info(f"Loaded {len(docs)} docs for splitting")

    train, dev = stratified_split(docs, train_ratio, seed)
    stats = compute_split_stats(train, dev)

    logger.info(f"Split: {stats['train_docs']} train / {stats['dev_docs']} dev, "
                f"coverage OK: {stats['rule_coverage_ok']}")

    write_jsonl(train, train_path)
    write_jsonl(dev, dev_path)

    return train_path, dev_path


# ── Step 4: Windowing ─────────────────────────────────────────────────────

def run_windowing(
    config: Dict,
    train_path: str,
    dev_path: str,
    max_train_windows: int = 30000,
    max_dev_windows: int = 10000,
) -> tuple:
    """Extract training windows from train and dev sets.

    Subsamples to max_train_windows/max_dev_windows to keep training
    tractable on CPU/MPS (CRF is CPU-bound). 30K windows is still
    far more than typical NER datasets (~5K-15K).
    """
    from ml.data.label_spans import extract_training_windows

    seed = config.get("seed", 42)

    # Load raw splits
    train_docs = _load_jsonl(train_path)
    dev_docs = _load_jsonl(dev_path)

    logger.info(f"Windowing {len(train_docs)} train + {len(dev_docs)} dev docs...")

    t0 = time.time()
    train_windowed = extract_training_windows(
        train_docs, window_size=300, stride=150,
        negative_ratio=0.3, seed=seed,
    )
    dev_windowed = extract_training_windows(
        dev_docs, window_size=300, stride=150,
        negative_ratio=0.3, seed=seed + 1,
    )
    elapsed = time.time() - t0
    logger.info(f"Windowing done in {elapsed:.1f}s: "
                f"{len(train_windowed)} train / {len(dev_windowed)} dev windows")

    # Subsample if too many windows (keeps training tractable on MPS/CPU).
    # With large arXiv papers and dense patterns, most windows contain spans,
    # so we subsample both positive and negative windows proportionally.
    rng = random.Random(seed)
    if len(train_windowed) > max_train_windows:
        has_spans = [w for w in train_windowed if w.get("spans")]
        no_spans = [w for w in train_windowed if not w.get("spans")]
        ratio = max_train_windows / len(train_windowed)
        n_pos = min(len(has_spans), max(1, int(len(has_spans) * ratio)))
        n_neg = min(len(no_spans), max_train_windows - n_pos)
        rng.shuffle(has_spans)
        rng.shuffle(no_spans)
        train_windowed = has_spans[:n_pos] + no_spans[:n_neg]
        rng.shuffle(train_windowed)
        logger.info(f"Subsampled train: {len(train_windowed)} windows "
                    f"({n_pos} positive, {n_neg} negative)")

    if len(dev_windowed) > max_dev_windows:
        rng.shuffle(dev_windowed)
        dev_windowed = dev_windowed[:max_dev_windows]
        logger.info(f"Subsampled dev: {len(dev_windowed)} windows")

    # Write windowed files
    config_dir = PROJECT_ROOT / "ml"
    train_w_path = str(config_dir / "data" / "train_windowed.jsonl")
    dev_w_path = str(config_dir / "data" / "dev_windowed.jsonl")

    _write_jsonl(train_windowed, train_w_path)
    _write_jsonl(dev_windowed, dev_w_path)

    return train_w_path, dev_w_path


# ── Step 5: Train BERT+CRF ───────────────────────────────────────────────

def run_training(
    config: Dict,
    train_path: str,
    dev_path: str,
    device: str,
    use_crf: bool = True,
    model_name_override: str = None,
) -> Dict[str, Any]:
    """Train BERT+CRF model."""
    from ml.models.bert_crf import train_bert_crf

    bert_cfg = config.get("bert_crf", {})
    seed = config.get("seed", 42)
    model_name = model_name_override or bert_cfg.get("model_name", "allenai/scibert_scivocab_uncased")

    # Without CRF, everything runs on MPS — can use larger batches
    batch_size = 16
    mode = "BERT+CRF" if use_crf else "BERT+CE (cross-entropy)"

    logger.info(f"Training {mode} on device={device}")
    logger.info(f"  model: {model_name}")
    logger.info(f"  epochs: {bert_cfg.get('epochs', 50)}, "
                f"batch_size: {batch_size}, "
                f"lr: {bert_cfg.get('learning_rate', 3e-5)}")

    t0 = time.time()
    results = train_bert_crf(
        train_jsonl=train_path,
        dev_jsonl=dev_path,
        model_name=model_name,
        max_length=bert_cfg.get("max_length", 128),
        batch_size=batch_size,
        epochs=bert_cfg.get("epochs", 50),
        learning_rate=bert_cfg.get("learning_rate", 3e-5),
        warmup_ratio=bert_cfg.get("warmup_ratio", 0.1),
        weight_decay=bert_cfg.get("weight_decay", 0.01),
        crf_lr=bert_cfg.get("crf_learning_rate", 1e-3),
        patience=bert_cfg.get("patience", 7),
        min_epochs=bert_cfg.get("min_epochs", 15),
        seed=seed,
        device=device,
        output_dir=str(PROJECT_ROOT / "ml" / "checkpoints"),
        use_crf=use_crf,
    )
    elapsed = time.time() - t0
    logger.info(f"Training complete in {elapsed/60:.1f}min")
    logger.info(f"Best dev F1: {results.get('overall_f1', 0):.4f}")
    logger.info(f"Delta: {results.get('delta', 1.0):.4f}")

    return results


# ── Step 6: Export for Coq ────────────────────────────────────────────────

def run_export(results: Dict, config: Dict) -> Dict:
    """Export evaluation results and Coq bound."""
    from ml.export_eval import export_for_coq

    # Save eval results
    eval_path = str(PROJECT_ROOT / "ml" / config["paths"]["eval_results"])
    Path(eval_path).parent.mkdir(parents=True, exist_ok=True)
    with open(eval_path, "w") as f:
        json.dump(results, f, indent=2)
    logger.info(f"Eval results → {eval_path}")

    # Export Coq bound
    bound_path = str(PROJECT_ROOT / "proofs" / "ML" / "eval_bound.json")
    bound = export_for_coq(eval_path, bound_path)

    f1 = results.get("overall_f1", 0)
    threshold = 0.94
    if f1 >= threshold:
        logger.info(f"PASS: F1={f1:.4f} >= {threshold} threshold")
    else:
        logger.warning(f"BELOW THRESHOLD: F1={f1:.4f} < {threshold}")

    logger.info(f"Coq bound → {bound_path}")
    return bound


# ── Utilities ──────────────────────────────────────────────────────────────

def _load_jsonl(path: str) -> List[Dict]:
    docs = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                docs.append(json.loads(line))
    return docs


def _write_jsonl(docs: List[Dict], path: str):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for doc in docs:
            json.dump(doc, f, ensure_ascii=False)
            f.write("\n")


def detect_device() -> str:
    """Auto-detect best available device: mps > cuda > cpu."""
    try:
        import torch
        if torch.backends.mps.is_available():
            return "mps"
        if torch.cuda.is_available():
            return "cuda"
    except Exception:
        pass
    return "cpu"


# ── Main ──────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Local ML span extractor training pipeline"
    )
    parser.add_argument("--skip-arxiv", action="store_true",
                        help="Skip arXiv download (use local corpus only)")
    parser.add_argument("--n-papers", type=int, default=1000,
                        help="Number of arXiv papers to download (default: 1000)")
    parser.add_argument("--device", default="auto",
                        help="Device: auto, mps, cuda, cpu (default: auto)")
    parser.add_argument("--config", default="ml/config.yaml",
                        help="Config file path (default: ml/config.yaml)")
    parser.add_argument("--skip-labeling", action="store_true",
                        help="Skip labeling (reuse existing labeled_spans.jsonl)")
    parser.add_argument("--skip-windowing", action="store_true",
                        help="Skip windowing (reuse existing windowed files)")
    parser.add_argument("--max-train-windows", type=int, default=30000,
                        help="Max training windows (default: 30000)")
    parser.add_argument("--max-dev-windows", type=int, default=10000,
                        help="Max dev windows (default: 10000)")
    parser.add_argument("--no-crf", action="store_true",
                        help="Disable CRF layer (use cross-entropy, faster on MPS)")
    parser.add_argument("--model-name", default=None,
                        help="Override model name (e.g., distilbert-base-uncased)")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    # Load config
    config_path = PROJECT_ROOT / args.config
    with open(config_path, "r") as f:
        config = yaml.safe_load(f)
    logger.info("=== ML Span Extractor: Local Training Pipeline ===")

    # Device
    if args.device == "auto":
        device = detect_device()
    else:
        device = args.device
    logger.info(f"Device: {device}")

    total_t0 = time.time()

    config_dir = PROJECT_ROOT / "ml"

    # ── Step 1: ArXiv download ────────────────────────────────────────
    arxiv_dir = config_dir / "data" / "arxiv_papers"
    if not args.skip_arxiv:
        logger.info("=" * 60)
        logger.info("STEP 1: Downloading arXiv papers")
        logger.info("=" * 60)
        t0 = time.time()
        n = download_arxiv_papers(arxiv_dir, n_papers=args.n_papers)
        logger.info(f"Step 1 done: {n} papers ({time.time()-t0:.0f}s)")
    else:
        logger.info("STEP 1: Skipping arXiv download (--skip-arxiv)")

    # ── Step 2: Labeling ──────────────────────────────────────────────
    labeled_path = str(config_dir / config["paths"]["labeled_jsonl"])

    if not args.skip_labeling:
        logger.info("=" * 60)
        logger.info("STEP 2: Labeling corpus with VPD patterns")
        logger.info("=" * 60)
        t0 = time.time()
        arxiv_d = arxiv_dir if not args.skip_arxiv and arxiv_dir.is_dir() else None
        labeled_path = run_labeling(config, arxiv_d)
        logger.info(f"Step 2 done ({time.time()-t0:.0f}s)")
    else:
        logger.info("STEP 2: Skipping labeling (--skip-labeling)")

    # ── Step 3: Split ─────────────────────────────────────────────────
    logger.info("=" * 60)
    logger.info("STEP 3: Stratified train/dev split")
    logger.info("=" * 60)
    t0 = time.time()
    train_path, dev_path = run_split(config, labeled_path)
    logger.info(f"Step 3 done ({time.time()-t0:.0f}s)")

    # ── Step 4: Windowing ─────────────────────────────────────────────
    train_w_path = str(config_dir / "data" / "train_windowed.jsonl")
    dev_w_path = str(config_dir / "data" / "dev_windowed.jsonl")

    if not args.skip_windowing:
        logger.info("=" * 60)
        logger.info("STEP 4: Extracting training windows")
        logger.info("=" * 60)
        t0 = time.time()
        train_w_path, dev_w_path = run_windowing(
            config, train_path, dev_path,
            max_train_windows=args.max_train_windows,
            max_dev_windows=args.max_dev_windows,
        )
        logger.info(f"Step 4 done ({time.time()-t0:.0f}s)")
    else:
        logger.info("STEP 4: Skipping windowing (--skip-windowing)")

    # ── Step 5: Train BERT+CRF ───────────────────────────────────────
    logger.info("=" * 60)
    logger.info("STEP 5: Training BERT+CRF")
    logger.info("=" * 60)
    t0 = time.time()
    results = run_training(config, train_w_path, dev_w_path, device,
                           use_crf=not args.no_crf,
                           model_name_override=args.model_name)
    logger.info(f"Step 5 done ({time.time()-t0:.0f}min)")

    # ── Step 6: Export ────────────────────────────────────────────────
    logger.info("=" * 60)
    logger.info("STEP 6: Exporting results for Coq proof")
    logger.info("=" * 60)
    bound = run_export(results, config)

    # ── Summary ───────────────────────────────────────────────────────
    total_elapsed = time.time() - total_t0
    logger.info("=" * 60)
    logger.info("PIPELINE COMPLETE")
    logger.info(f"  Total time: {total_elapsed/60:.1f} min")
    logger.info(f"  F1: {results.get('overall_f1', 0):.4f}")
    logger.info(f"  Delta: {results.get('delta', 1.0):.4f}")
    logger.info(f"  Bound holds: {bound.get('bound_holds', False)}")
    logger.info(f"  Device used: {device}")
    logger.info("=" * 60)


if __name__ == "__main__":
    main()
