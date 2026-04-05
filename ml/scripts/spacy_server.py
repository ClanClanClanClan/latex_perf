#!/usr/bin/env python3
"""spaCy NLP pipeline server (spec W71).

Provides sentence-level NLP processing for L4 style validators.
Supports en/fr/de language models.

Usage:
    python spacy_server.py --host 0.0.0.0 --port 8090

Endpoints:
    GET  /health              → {"status": "ok"}
    POST /analyze             → sentence analysis (POS, NER, deps)
    POST /sentences           → sentence boundary detection
"""

import argparse
import json
import sys
from typing import Any, Dict, List

try:
    import spacy
    from flask import Flask, jsonify, request
except ImportError:
    print("Missing dependencies. Install with: pip install -r requirements-spacy.txt")
    sys.exit(1)

app = Flask(__name__)

# Lazy-loaded language models
_models: Dict[str, Any] = {}

SUPPORTED_LANGS = {
    "en": "en_core_web_sm",
    "fr": "fr_core_news_sm",
    "de": "de_core_news_sm",
}


def get_model(lang: str) -> Any:
    """Load and cache a spaCy model for the given language."""
    if lang not in _models:
        model_name = SUPPORTED_LANGS.get(lang)
        if model_name is None:
            raise ValueError(f"Unsupported language: {lang}. Supported: {list(SUPPORTED_LANGS.keys())}")
        _models[lang] = spacy.load(model_name)
    return _models[lang]


@app.route("/health", methods=["GET"])
def health():
    """Health check endpoint."""
    return jsonify({"status": "ok", "models": list(SUPPORTED_LANGS.keys())})


@app.route("/analyze", methods=["POST"])
def analyze():
    """Analyze text: returns tokens with POS, lemma, dependency parse."""
    data = request.get_json()
    if not data or "text" not in data:
        return jsonify({"error": "Missing 'text' field"}), 400

    lang = data.get("lang", "en")
    text = data["text"]

    try:
        nlp = get_model(lang)
    except ValueError as e:
        return jsonify({"error": str(e)}), 400

    doc = nlp(text)
    tokens: List[Dict[str, Any]] = []
    for token in doc:
        tokens.append({
            "text": token.text,
            "lemma": token.lemma_,
            "pos": token.pos_,
            "dep": token.dep_,
            "is_stop": token.is_stop,
            "is_punct": token.is_punct,
        })

    return jsonify({
        "lang": lang,
        "token_count": len(tokens),
        "tokens": tokens,
    })


@app.route("/sentences", methods=["POST"])
def sentences():
    """Split text into sentences using spaCy's sentence boundary detection."""
    data = request.get_json()
    if not data or "text" not in data:
        return jsonify({"error": "Missing 'text' field"}), 400

    lang = data.get("lang", "en")
    text = data["text"]

    try:
        nlp = get_model(lang)
    except ValueError as e:
        return jsonify({"error": str(e)}), 400

    doc = nlp(text)
    sents = [{"text": sent.text, "start": sent.start_char, "end": sent.end_char} for sent in doc.sents]

    return jsonify({
        "lang": lang,
        "sentence_count": len(sents),
        "sentences": sents,
    })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="spaCy NLP pipeline server")
    parser.add_argument("--host", default="127.0.0.1", help="Host to bind to")
    parser.add_argument("--port", type=int, default=8090, help="Port to listen on")
    args = parser.parse_args()

    # Pre-load English model for fast first request
    print(f"Loading en_core_web_sm...")
    get_model("en")
    print(f"spaCy server ready at http://{args.host}:{args.port}")

    app.run(host=args.host, port=args.port, debug=False)
