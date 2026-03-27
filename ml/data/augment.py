#!/usr/bin/env python3
"""Data augmentation: inject errors into REAL corpus .tex excerpts.

Addresses extreme data scarcity (~216 spans, 53 rules, ~4 examples/rule)
by taking real LaTeX text from the project corpus, injecting VPD-pattern
errors at random positions, and labeling with the full replay pipeline.

Strategy:
  1. Load ALL .tex files from corpus (including perf/ benchmarks for bulk text)
  2. Extract random 50-200 char excerpts from real files
  3. For each VPD pattern, inject the target error into a real excerpt
  4. Label with full ``label_document()`` so all patterns fire naturally
  5. Add augmented docs to training set ONLY (dev stays natural)

Expected boost: ~200 real docs  →  ~2000+ training docs.
"""

import os
import random
import logging
from pathlib import Path
from typing import List, Dict, Optional, Tuple

logger = logging.getLogger(__name__)


# ── Corpus excerpt pool ──────────────────────────────────────────────────────

_excerpt_pool: List[str] = []


def load_corpus_excerpts(
    corpus_dirs: List[str],
    excerpt_len_range: Tuple[int, int] = (50, 200),
    max_excerpts: int = 5000,
    seed: int = 42,
) -> List[str]:
    """Load random text excerpts from real .tex files.

    Reads every .tex file in the given directories, splits into
    fixed-size excerpts, and returns a shuffled pool.
    """
    global _excerpt_pool
    if _excerpt_pool:
        return _excerpt_pool

    rng = random.Random(seed)
    all_text_chunks: List[str] = []
    min_len, max_len = excerpt_len_range
    files_read = 0

    for d in corpus_dirs:
        p = Path(d)
        if not p.is_dir():
            continue
        for tex_file in sorted(p.glob("**/*.tex")):
            try:
                text = tex_file.read_text(encoding='utf-8')
            except UnicodeDecodeError:
                try:
                    text = tex_file.read_text(encoding='latin-1')
                except Exception:
                    continue
            files_read += 1

            # Slide a window over the file to extract excerpts
            if len(text) < min_len:
                all_text_chunks.append(text)
                continue
            step = max(min_len // 2, 20)
            for start in range(0, len(text) - min_len, step):
                end = start + rng.randint(min_len, max_len)
                end = min(end, len(text))
                chunk = text[start:end]
                # Skip chunks that are mostly whitespace or empty
                if len(chunk.strip()) > min_len // 2:
                    all_text_chunks.append(chunk)

    rng.shuffle(all_text_chunks)
    _excerpt_pool = all_text_chunks[:max_excerpts]
    logger.info(f"Loaded {len(_excerpt_pool)} real excerpts from {files_read} .tex files")
    return _excerpt_pool


def _real_excerpt(rng: random.Random) -> str:
    """Pick a random real corpus excerpt."""
    if _excerpt_pool:
        return rng.choice(_excerpt_pool)
    # Fallback if pool not loaded (shouldn't happen in normal use)
    return "The function $f(x) = x^2$ is continuous on $\\mathbb{R}$."


# ── Insertion helpers ────────────────────────────────────────────────────────

def _safe_insert_pos(text: str, rng: random.Random, avoid_math: bool = False) -> int:
    """Pick a random insertion position, optionally outside math mode."""
    if not text:
        return 0
    if not avoid_math or '$' not in text:
        return rng.randint(0, len(text) - 1)

    safe = []
    depth = 0
    for i, c in enumerate(text):
        if c == '$':
            depth = 1 - depth
        elif depth == 0:
            safe.append(i)
    return rng.choice(safe) if safe else rng.randint(0, len(text) - 1)


def _inject_at(text: str, pos: int, payload: str) -> str:
    return text[:pos] + payload + text[pos:]


# ── Per-family injection (using real excerpts) ───────────────────────────────

def _inject_count_char(rng, char, n=None):
    text = _real_excerpt(rng)
    n = n or rng.randint(1, 3)
    for _ in range(n):
        pos = _safe_insert_pos(text, rng)
        text = _inject_at(text, pos, char)
    return text


def _inject_count_char_strip_math(rng, char):
    # Try to find an excerpt containing math
    for _ in range(10):
        text = _real_excerpt(rng)
        if '$' in text:
            pos = _safe_insert_pos(text, rng, avoid_math=True)
            return _inject_at(text, pos, char)
    # Fallback: just inject into any excerpt
    text = _real_excerpt(rng)
    pos = _safe_insert_pos(text, rng)
    return _inject_at(text, pos, char)


def _inject_count_substring(rng, needle, n=None):
    text = _real_excerpt(rng)
    n = n or rng.randint(1, 2)
    for _ in range(n):
        pos = _safe_insert_pos(text, rng)
        text = _inject_at(text, pos, needle)
    return text


def _inject_count_substring_strip_math(rng, needle):
    for _ in range(10):
        text = _real_excerpt(rng)
        if '$' in text:
            pos = _safe_insert_pos(text, rng, avoid_math=True)
            return _inject_at(text, pos, needle)
    text = _real_excerpt(rng)
    pos = _safe_insert_pos(text, rng)
    return _inject_at(text, pos, needle)


def _inject_multi_substring(rng, needles):
    needle = rng.choice(needles)
    return _inject_count_substring(rng, needle)


# ── Regex generators (manual, for common patterns) ───────────────────────────

_REGEX_EXAMPLES: Dict[str, list] = {}


def _generate_for_regex(rng, regex_str, rule_id):
    if rule_id in _REGEX_EXAMPLES:
        base = rng.choice(_REGEX_EXAMPLES[rule_id])
        prefix = _real_excerpt(rng)[:rng.randint(10, 40)]
        return prefix + " " + base
    return None


# ── Custom-pattern generators (using real excerpts) ──────────────────────────

def _gen_TYPO_048(rng):
    """En-dash used as minus sign."""
    return _inject_count_char(rng, '\u2013')


def _gen_TYPO_052(rng):
    """Unescaped < or > outside math."""
    char = rng.choice(['<', '>'])
    for _ in range(10):
        text = _real_excerpt(rng)
        if '$' in text:
            pos = _safe_insert_pos(text, rng, avoid_math=True)
            return _inject_at(text, pos, char)
    text = _real_excerpt(rng)
    return _inject_at(text, _safe_insert_pos(text, rng), char)


def _gen_TYPO_040(rng):
    """Inline math exceeding 80 characters."""
    long_math = "a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t + u + v + w + x + y + z"
    excerpt = _real_excerpt(rng)
    pos = _safe_insert_pos(excerpt, rng)
    return excerpt[:pos] + f" ${long_math}$ " + excerpt[pos:]


def _gen_TYPO_045(rng):
    """Non-ASCII punctuation in math mode."""
    char = rng.choice(['\u2212', '\u00d7', '\u00f7', '\u2264', '\u2265'])
    excerpt = _real_excerpt(rng)
    # Insert a short math expression with the non-ASCII char
    pos = _safe_insert_pos(excerpt, rng)
    return excerpt[:pos] + f" ${char} x$ " + excerpt[pos:]


def _gen_TYPO_013(rng):
    """Single ASCII backtick."""
    return _inject_count_char(rng, '`')


def _gen_TYPO_024(rng):
    """Dangling dash at end of line."""
    excerpt = _real_excerpt(rng)
    mid = len(excerpt) // 2
    return excerpt[:mid] + " -\n" + excerpt[mid:]


def _gen_TYPO_028(rng):
    """$$ display math."""
    excerpt = _real_excerpt(rng)
    pos = _safe_insert_pos(excerpt, rng)
    return excerpt[:pos] + " $$x = y$$ " + excerpt[pos:]


def _gen_TYPO_062(rng):
    """Bare \\\\ not followed by [ or *."""
    excerpt = _real_excerpt(rng)
    mid = len(excerpt) // 2
    return excerpt[:mid] + " \\\\\n" + excerpt[mid:]


def _gen_TYPO_007(rng):
    """Trailing whitespace."""
    excerpt = _real_excerpt(rng)
    lines = excerpt.split('\n')
    if lines:
        idx = rng.randint(0, len(lines) - 1)
        lines[idx] = lines[idx] + " " * rng.randint(1, 4)
    return '\n'.join(lines)


def _gen_ENC_002(rng):
    """BOM not at position 0."""
    excerpt = _real_excerpt(rng)
    pos = rng.randint(1, max(len(excerpt) - 1, 1))
    return _inject_at(excerpt, pos, '\ufeff')


_CUSTOM_GENERATORS = {
    "TYPO-048": _gen_TYPO_048,
    "TYPO-052": _gen_TYPO_052,
    "TYPO-040": _gen_TYPO_040,
    "TYPO-045": _gen_TYPO_045,
    "TYPO-013": _gen_TYPO_013,
    "TYPO-024": _gen_TYPO_024,
    "TYPO-028": _gen_TYPO_028,
    "TYPO-062": _gen_TYPO_062,
    "ENC-002":  _gen_ENC_002,
}

_LINE_PRED_GENERATORS = {
    "TYPO-007": _gen_TYPO_007,
}


# ── Main augmentation entry point ───────────────────────────────────────────

def generate_augmented_docs(
    vpd_patterns: Dict[str, Dict],
    corpus_dirs: List[str],
    num_per_pattern: int = 20,
    seed: int = 42,
) -> List[Dict]:
    """Generate augmented training documents by injecting errors into real corpus text.

    For each VPD pattern, creates ``num_per_pattern`` documents by:
      1. Extracting a random excerpt from a real .tex file
      2. Injecting the target error into the excerpt
      3. Labeling with ``label_document()`` (all patterns fire naturally)

    Args:
        vpd_patterns: dict loaded from ``vpd_patterns.json``
        corpus_dirs:  list of directories containing .tex files
        num_per_pattern: how many augmented docs per VPD rule
        seed: random seed for reproducibility

    Returns:
        List of document dicts (same schema as ``label_spans`` JSONL rows).
    """
    from ml.data.label_spans import label_document

    # Load real corpus text into the excerpt pool
    load_corpus_excerpts(corpus_dirs, seed=seed)

    rng = random.Random(seed)
    docs: List[Dict] = []
    attempted = 0
    succeeded = 0
    family_stats: Dict[str, Dict[str, int]] = {}

    for rule_id, rule_def in sorted(vpd_patterns.items()):
        pattern_def = rule_def.get("pattern", {})
        family = pattern_def.get("family", "")
        family_stats.setdefault(family, {"ok": 0, "fail": 0})

        for i in range(num_per_pattern):
            attempted += 1
            text = _make_text(rng, family, pattern_def, rule_id)
            if text is None:
                family_stats[family]["fail"] += 1
                continue

            doc = label_document(f"aug/{rule_id}_{i:03d}.tex", text, vpd_patterns)
            if doc.spans:
                docs.append(doc.to_dict())
                succeeded += 1
                family_stats[family]["ok"] += 1
            else:
                family_stats[family]["fail"] += 1

    logger.info(
        f"Augmentation: {succeeded}/{attempted} docs with spans "
        f"({attempted - succeeded} empty/skipped)"
    )
    for fam, fs in sorted(family_stats.items()):
        logger.info(f"  {fam:30s}  ok={fs['ok']:4d}  fail={fs['fail']:3d}")

    # Summary
    rule_counts: Dict[str, int] = {}
    for doc in docs:
        for span in doc.get("spans", []):
            rid = span["rule_id"]
            rule_counts[rid] = rule_counts.get(rid, 0) + 1
    logger.info(f"Augmented rules: {len(rule_counts)}")
    for rid, cnt in sorted(rule_counts.items()):
        logger.info(f"    {rid}: {cnt} spans")

    return docs


def _make_text(
    rng: random.Random,
    family: str,
    pattern_def: Dict,
    rule_id: str,
) -> Optional[str]:
    """Generate text that should trigger *family* for *rule_id*."""

    if family == "count_char":
        ch = pattern_def.get("char", "")
        return _inject_count_char(rng, ch) if ch else None

    if family == "count_char_strip_math":
        ch = pattern_def.get("char", "")
        return _inject_count_char_strip_math(rng, ch) if ch else None

    if family == "count_substring":
        needle = pattern_def.get("needle", "")
        return _inject_count_substring(rng, needle) if needle else None

    if family == "count_substring_strip_math":
        needle = pattern_def.get("needle", "")
        return _inject_count_substring_strip_math(rng, needle) if needle else None

    if family == "multi_substring":
        needles = pattern_def.get("needles", [])
        return _inject_multi_substring(rng, needles) if needles else None

    if family == "regex":
        regex_str = pattern_def.get("regex", "")
        return _generate_for_regex(rng, regex_str, rule_id)

    if family == "custom":
        gen = _CUSTOM_GENERATORS.get(rule_id)
        return gen(rng) if gen else None

    if family == "line_pred":
        gen = _LINE_PRED_GENERATORS.get(rule_id)
        return gen(rng) if gen else None

    return None
