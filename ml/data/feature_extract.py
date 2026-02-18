#!/usr/bin/env python3
"""Token-level feature extraction for ML span extractor.

Extracts character-level and token-level features from LaTeX documents,
replicating the tokenizer_lite.ml token kinds for consistency with the
OCaml runtime.

Features per character position:
  - Character n-grams (unigram, bigram, trigram) in context window
  - Unicode character class (letter, digit, punct, whitespace, math, other)
  - Token kind from lightweight tokenizer
  - In-math context flag
  - Line-level features (length, position, leading whitespace)
  - Context window of ±5 characters

Usage:
    python -m ml.data.feature_extract --input data/labeled_spans.jsonl --output data/features.jsonl
"""

import json
import re
import unicodedata
from dataclasses import dataclass
from enum import Enum, auto
from pathlib import Path
from typing import List, Dict, Tuple, Optional, Any
import argparse
import logging

import numpy as np

logger = logging.getLogger(__name__)


# ── Token kinds (mirrors tokenizer_lite.ml) ──────────────────────────────────

class TokenKind(Enum):
    Word = auto()
    Space = auto()
    Newline = auto()
    Command = auto()
    BracketOpen = auto()
    BracketClose = auto()
    Quote = auto()
    Symbol = auto()
    MathDelim = auto()
    Other = auto()


@dataclass
class Token:
    kind: TokenKind
    start: int
    end: int
    text: str


def tokenize_lite(text: str) -> List[Token]:
    """Lightweight tokenizer replicating tokenizer_lite.ml logic.

    Produces tokens with byte-offset spans and kind classification.
    """
    tokens = []
    n = len(text)
    i = 0
    while i < n:
        c = text[i]

        # Newline
        if c == '\n':
            tokens.append(Token(TokenKind.Newline, i, i + 1, '\n'))
            i += 1
            continue

        # Whitespace (not newline)
        if c in ' \t\r':
            j = i + 1
            while j < n and text[j] in ' \t\r':
                j += 1
            tokens.append(Token(TokenKind.Space, i, j, text[i:j]))
            i = j
            continue

        # LaTeX command: \xxx
        if c == '\\':
            j = i + 1
            if j < n and text[j].isalpha():
                while j < n and text[j].isalpha():
                    j += 1
                tokens.append(Token(TokenKind.Command, i, j, text[i:j]))
            elif j < n:
                # Single-char command like \$ \\ \{
                j += 1
                tokens.append(Token(TokenKind.Command, i, j, text[i:j]))
            else:
                tokens.append(Token(TokenKind.Symbol, i, j, text[i:j]))
            i = j
            continue

        # Brackets
        if c in '({[':
            tokens.append(Token(TokenKind.BracketOpen, i, i + 1, c))
            i += 1
            continue
        if c in ')}]':
            tokens.append(Token(TokenKind.BracketClose, i, i + 1, c))
            i += 1
            continue

        # Math delimiters
        if c == '$':
            if i + 1 < n and text[i + 1] == '$':
                tokens.append(Token(TokenKind.MathDelim, i, i + 2, '$$'))
                i += 2
            else:
                tokens.append(Token(TokenKind.MathDelim, i, i + 1, '$'))
                i += 1
            continue

        # Quotes
        if c in '`\'"' or c in '\u201c\u201d\u2018\u2019':
            tokens.append(Token(TokenKind.Quote, i, i + 1, c))
            i += 1
            continue

        # Word (letters, digits, and connected hyphens/apostrophes)
        if c.isalpha() or c.isdigit():
            j = i + 1
            while j < n and (text[j].isalpha() or text[j].isdigit()
                             or text[j] in "-'" and j + 1 < n
                             and (text[j + 1].isalpha() or text[j + 1].isdigit())):
                j += 1
            tokens.append(Token(TokenKind.Word, i, j, text[i:j]))
            i = j
            continue

        # Everything else is Symbol
        tokens.append(Token(TokenKind.Symbol, i, i + 1, c))
        i += 1

    return tokens


# ── Unicode character class ──────────────────────────────────────────────────

def char_class(c: str) -> str:
    """Classify a character into a broad Unicode category."""
    if c.isalpha():
        return "letter"
    if c.isdigit():
        return "digit"
    if c in ' \t\r':
        return "whitespace"
    if c == '\n':
        return "newline"
    cat = unicodedata.category(c)
    if cat.startswith('P'):
        return "punctuation"
    if cat.startswith('S'):
        return "symbol"
    if cat.startswith('Z'):
        return "whitespace"
    return "other"


# ── Math-mode tracking ───────────────────────────────────────────────────────

def compute_in_math_array(text: str) -> List[bool]:
    """For each character position, determine if it's inside math mode."""
    n = len(text)
    in_math = [False] * n
    math_mode = False
    math_delim = None
    i = 0
    while i < n:
        c = text[i]
        if c == '$':
            if i + 1 < n and text[i + 1] == '$':
                if math_mode and math_delim == '$$':
                    in_math[i] = True
                    in_math[i + 1] = True
                    math_mode = False
                    math_delim = None
                elif not math_mode:
                    math_mode = True
                    math_delim = '$$'
                    in_math[i] = True
                    in_math[i + 1] = True
                i += 2
                continue
            else:
                if math_mode and math_delim == '$':
                    in_math[i] = True
                    math_mode = False
                    math_delim = None
                elif not math_mode:
                    math_mode = True
                    math_delim = '$'
                    in_math[i] = True
                i += 1
                continue
        elif c == '\\' and i + 1 < n:
            nxt = text[i + 1]
            if nxt == '(' and not math_mode:
                math_mode = True
                math_delim = '\\('
                in_math[i] = True
                in_math[i + 1] = True
                i += 2
                continue
            elif nxt == ')' and math_mode and math_delim == '\\(':
                in_math[i] = True
                in_math[i + 1] = True
                math_mode = False
                math_delim = None
                i += 2
                continue
            elif nxt == '[' and not math_mode:
                math_mode = True
                math_delim = '\\['
                in_math[i] = True
                in_math[i + 1] = True
                i += 2
                continue
            elif nxt == ']' and math_mode and math_delim == '\\[':
                in_math[i] = True
                in_math[i + 1] = True
                math_mode = False
                math_delim = None
                i += 2
                continue

        if math_mode:
            in_math[i] = True
        i += 1

    return in_math


# ── Line-level features ─────────────────────────────────────────────────────

def compute_line_features(text: str) -> List[Dict[str, int]]:
    """Compute per-character line-level features."""
    lines = text.split('\n')
    features = []
    for line_idx, line in enumerate(lines):
        line_len = len(line)
        leading_ws = len(line) - len(line.lstrip())
        for pos_in_line in range(len(line)):
            features.append({
                "line_idx": line_idx,
                "line_length": line_len,
                "pos_in_line": pos_in_line,
                "leading_whitespace": leading_ws,
            })
        # Newline character (except last line)
        if line_idx < len(lines) - 1:
            features.append({
                "line_idx": line_idx,
                "line_length": line_len,
                "pos_in_line": line_len,
                "leading_whitespace": leading_ws,
            })

    # Pad if needed (should match text length)
    while len(features) < len(text):
        features.append({
            "line_idx": -1,
            "line_length": 0,
            "pos_in_line": 0,
            "leading_whitespace": 0,
        })

    return features[:len(text)]


# ── Context window n-grams ───────────────────────────────────────────────────

def extract_ngram_features(text: str, pos: int, window: int = 5) -> Dict[str, str]:
    """Extract character n-grams around a position."""
    n = len(text)

    # Unigram
    unigram = text[pos] if 0 <= pos < n else ''

    # Bigrams (pos-1..pos, pos..pos+1)
    bigram_l = text[max(0, pos - 1):pos + 1] if pos > 0 else '<S>' + unigram
    bigram_r = text[pos:min(n, pos + 2)] if pos + 1 < n else unigram + '<E>'

    # Trigram (pos-1..pos+1)
    trigram = text[max(0, pos - 1):min(n, pos + 2)]

    # Context window
    ctx_start = max(0, pos - window)
    ctx_end = min(n, pos + window + 1)
    context = text[ctx_start:ctx_end]

    return {
        "unigram": unigram,
        "bigram_l": bigram_l,
        "bigram_r": bigram_r,
        "trigram": trigram,
        "context_window": context,
    }


# ── Token kind assignment ────────────────────────────────────────────────────

def assign_token_kinds(text: str) -> List[str]:
    """Assign a token kind string to each character position."""
    tokens = tokenize_lite(text)
    kinds = ['Other'] * len(text)
    for tok in tokens:
        for i in range(tok.start, min(tok.end, len(text))):
            kinds[i] = tok.kind.name
    return kinds


# ── Main feature extraction ──────────────────────────────────────────────────

def extract_features_for_document(
    text: str,
    context_window: int = 5,
) -> List[Dict[str, Any]]:
    """Extract per-character features for a document.

    Returns list of feature dicts, one per character position.
    """
    n = len(text)
    if n == 0:
        return []

    # Precompute arrays
    in_math = compute_in_math_array(text)
    line_feats = compute_line_features(text)
    token_kinds = assign_token_kinds(text)

    features = []
    for pos in range(n):
        ngrams = extract_ngram_features(text, pos, context_window)
        feat = {
            "pos": pos,
            "char": text[pos],
            "char_class": char_class(text[pos]),
            "char_ord": ord(text[pos]),
            "in_math": in_math[pos],
            "token_kind": token_kinds[pos],
            "unigram": ngrams["unigram"],
            "bigram_l": ngrams["bigram_l"],
            "bigram_r": ngrams["bigram_r"],
            "trigram": ngrams["trigram"],
            **line_feats[pos],
        }
        features.append(feat)

    return features


def extract_features_from_jsonl(
    input_path: str,
    output_path: str,
    context_window: int = 5,
) -> Dict[str, Any]:
    """Extract features from labeled JSONL, writing enriched JSONL.

    Each output line is: {file, text, bio_tags, features: [...]}
    For memory efficiency with large documents, features are a list of
    compact dicts rather than full feature vectors.
    """
    from pathlib import Path

    output_file = Path(output_path)
    output_file.parent.mkdir(parents=True, exist_ok=True)

    total_chars = 0
    total_docs = 0

    with open(input_path, 'r', encoding='utf-8') as fin, \
         open(output_path, 'w', encoding='utf-8') as fout:
        for line in fin:
            doc = json.loads(line.strip())
            text = doc["text"]
            bio_tags = doc["bio_tags"]

            # Extract features
            features = extract_features_for_document(text, context_window)

            # Write compact output
            out_record = {
                "file": doc["file"],
                "text": text,
                "bio_tags": bio_tags,
                "rule_ids": doc.get("rule_ids", []),
                "features": features,
            }
            json.dump(out_record, fout, ensure_ascii=False)
            fout.write('\n')

            total_chars += len(text)
            total_docs += 1

    return {
        "total_documents": total_docs,
        "total_characters": total_chars,
        "context_window": context_window,
    }


# ── Vectorization for sklearn models ────────────────────────────────────────

def vectorize_for_sklearn(
    features_jsonl_path: str,
) -> Tuple[np.ndarray, np.ndarray, List[str], List[str]]:
    """Convert feature JSONL to numpy arrays for sklearn models.

    Returns:
        X: (N, d) feature matrix (float)
        y: (N,) label array (int: 0=O, 1=B-*, 2=I-*)
        tag_names: list of unique BIO tag strings
        file_names: list of source file names (one per sample)
    """
    all_X = []
    all_y = []
    all_files = []
    tag_set = set()

    with open(features_jsonl_path, 'r', encoding='utf-8') as f:
        for line in f:
            doc = json.loads(line.strip())
            feats_list = doc["features"]
            bio_tags = doc["bio_tags"]
            file_name = doc["file"]

            for feat, tag in zip(feats_list, bio_tags):
                # Numeric features for sklearn
                row = [
                    feat["char_ord"],
                    1.0 if feat["in_math"] else 0.0,
                    _char_class_to_int(feat["char_class"]),
                    _token_kind_to_int(feat["token_kind"]),
                    feat["line_length"],
                    feat["pos_in_line"],
                    feat["leading_whitespace"],
                ]
                all_X.append(row)
                tag_set.add(tag)
                all_y.append(tag)
                all_files.append(file_name)

    # Encode tags
    tag_names = sorted(tag_set)
    tag_to_idx = {t: i for i, t in enumerate(tag_names)}
    y_encoded = np.array([tag_to_idx[t] for t in all_y], dtype=np.int32)
    X = np.array(all_X, dtype=np.float32)

    return X, y_encoded, tag_names, all_files


_CHAR_CLASS_MAP = {
    "letter": 0, "digit": 1, "whitespace": 2, "newline": 3,
    "punctuation": 4, "symbol": 5, "other": 6,
}

_TOKEN_KIND_MAP = {
    "Word": 0, "Space": 1, "Newline": 2, "Command": 3,
    "BracketOpen": 4, "BracketClose": 5, "Quote": 6,
    "Symbol": 7, "MathDelim": 8, "Other": 9,
}


def _char_class_to_int(cc: str) -> float:
    return float(_CHAR_CLASS_MAP.get(cc, 6))


def _token_kind_to_int(tk: str) -> float:
    return float(_TOKEN_KIND_MAP.get(tk, 9))


# ── CLI ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Extract features from labeled JSONL")
    parser.add_argument("--input", default="ml/data/labeled_spans.jsonl",
                        help="Input labeled JSONL")
    parser.add_argument("--output", default="ml/data/features.jsonl",
                        help="Output features JSONL")
    parser.add_argument("--context-window", type=int, default=5,
                        help="Context window size (default: 5)")
    parser.add_argument("--verbose", "-v", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        datefmt="%H:%M:%S",
    )

    logger.info("=== Feature Extraction ===")
    summary = extract_features_from_jsonl(args.input, args.output, args.context_window)
    logger.info(f"Extracted features for {summary['total_documents']} documents, "
                f"{summary['total_characters']} characters")
    logger.info("Done.")


if __name__ == "__main__":
    main()
