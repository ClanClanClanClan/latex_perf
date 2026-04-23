# Architecture Handbook

Revision 2026-04-23. Evergreen document (spec L-9).

---

## Overview

LaTeX Perfectionist v26.2 is a five-layer incremental LaTeX analysis pipeline
with formal (Coq) soundness proofs for every validator rule, a tiered
language contract (LP-Core / LP-Extended / LP-Foreign), a real validator
dependency graph driven by `specs/rules/rule_contracts.yaml`, a pre-compile
T0–T5 readiness contract (`Compile_contract.check_ready_to_compile`), and a
byte-lossless CST + rewrite-engine substrate (`Cst`, `Cst_of_ast`,
`Cst_edit`, `Rewrite_engine`).

```
Source ─► L0 Tokenizer ─► L1 Expander ─► L2 Parser ─► L3 Semantics ─► L4 Style
             │                │              │              │              │
             ▼                ▼              ▼              ▼              ▼
          catcode.ml    rest_simple_     parser_l2.ml  semantic_state  validators_l4
          tokenizer_lite  expander.ml                   file_context    _style.ml
                         macro_catalogue
                                                        log_parser
```

---

## Layer Architecture

### L0 — Tokenizer (`tokenizer_lite.ml`)

Single-pass byte-level tokenizer. UTF-8 multi-byte support (Latin Extended,
Greek, Cyrillic, Arabic, CJK). CJK characters produce individual Word tokens.

- **Input**: raw LaTeX source (string)
- **Output**: `tok list` (Word, Space, Newline, Command, Bracket, Quote, Symbol)
- **Proof**: `LexerDeterminism.v`, `LexerTotality.v`, `LexerIncremental.v`
- **SIMD path**: `real_processor.ml` → C FFI → AVX2/NEON kernel

### L1 — Macro Expander (`rest_simple_expander.ml`, `macro_catalogue.ml`)

Fuel-bounded iterative expansion of 520 catalogued macros (441 symbol + 79
argsafe). Max depth 100. Deterministic, side-effect-free.

- **Input**: expanded source string
- **Output**: string with macros resolved
- **Proof**: `Expand.v`, `ExpandProofsFinal.v` (sufficient_fuel, expand_no_teof)

### L2 — PEG Parser (`parser_l2.ml`)

Recursive descent parser producing located AST. Handles math environments (26),
verbatim (5), floats (6), sections (5). Dirty-region detection for incremental
re-parse.

- **Input**: source string
- **Output**: `node list`, `document` (preamble, body, labels, refs, packages)
- **Key function**: `find_dirty_region` for incremental analysis
- **Proof**: `ParserSound.v`

### L3 — Semantic State (`semantic_state.ml`, `file_context.ml`)

> **Caveat first (memo §15.5):** current L3 is *partly* source-regex-derived.
> Label/ref/cite extraction scans the raw source via regex rather than
> walking the CST. This is correct on LP-Core documents (no catcode
> mutation, no macro-expanded `\label{...}`) and wrong on LP-Extended
> inputs where macros expand into the anchor commands. Full AST-derived
> L3 is v26.2 work; see [`L3_ROADMAP.md`](L3_ROADMAP.md) for the
> migration plan. The 20 binary-file validators (PNG/JPEG/PDF/font)
> operate on extracted binary metadata and do not share this
> limitation — they carry Formal Conservative proofs.

Label/ref tracking, duplicate detection, undefined/forward ref identification.
File-based analysis (PNG/JPEG/PDF/font binary readers) for L3 validator rules.

- **Thread-local state**: `set_state`/`get_state` per-thread Hashtbl
- **File context**: `set_file_context`/`get_file_context` for binary file metadata
- **Log context**: `set_log_context`/`get_log_context` for .log file events
- **Proof**: `LabelsUnique.v`, `InterpLocality.v` (conditional on the
  extractor matching AST semantics — v26.2 closes this gap)

### L4 — Style Validators (`validators_l4_style.ml`)

Sentence-level heuristic rules (49 STYLE + 10 locale). Operates on text after
math/verbatim stripping via `strip_math_segments`.

---

## Elder Runtime

Incremental analysis engine managing document state across edits (spec
Appendix I). Orchestrates L0-L4, maintains cross-layer consistency.

### Key Components

| Module | Purpose |
|--------|---------|
| `layer_sync.ml` | Version vectors, generation counters, snapshot consistency |
| `event_bus.ml` | Pub/sub semantic events (label/ref/section/environment) |
| `lockfree_queue.ml` | MPMC ring buffer (OCaml 5 Atomic, target 8M events/sec) |
| `chunk_store.ml` | Paragraph-level splitting, xxh64 hashing, per-chunk caching |
| `edf_scheduler.ml` | Deadline-ordered task execution (edit proximity + layer) |
| `cache_key.ml` | DJB2-based document-level result caching with TTL |
| `incremental_nlp.ml` | Sentence-level diff detection |

### Execution Flow

1. `chunk_store.split_into_chunks` → paragraph/environment boundaries
2. `Invalidation.compute ~old_snap ~new_snap` → semantic-aware dirty chunk set
   (replaced `chunk_store.diff_snapshots` in v26.0 WS4)
3. `edf_scheduler.submit_batch` → priority-ordered tasks per chunk×layer
4. `edf_scheduler.drain` → sequential execution
5. Cache clean chunk results, merge with dirty chunk results
6. Cross-chunk rules (L3+) bypass cache, run on full source

### Entry Points

- `run_all` — full re-evaluation (default)
- `run_all_incremental` — chunk-level caching, dirty-only re-validation
- `run_all_scheduled` — EDF-ordered incremental validation
- `run_all_scored` — confidence-weighted results with ML boost

---

## Validator Engine (`validators.ml`)

629 rules across 645 spec entries. Rules organized by family prefix
(TYPO, ENC, CHAR, SPC, MATH, etc.) and layer (L0-L4).

### Rule Registration

Each rule: `{ id : string; run : string -> result option; languages : string list }`.
Rules collected into lists (`rules_enc`, `rules_char`, etc.) and composed in
`rules_enc_char_spc`. Per-rule metadata (execution class, proof class,
consumes/provides edges, fix scope, project scope) lives in
`specs/rules/rule_contracts.yaml` and is loaded at startup by
`Rule_contract_loader.load` — this populates the `Validator_dag` metas
that drive the topological execution order.

### Evidence Scoring

`evidence_scoring.ml` assigns confidence (High/Medium/Low) based on rule
family, VPD certification, and ML-measured precision. ML confidence map
(`data/ml_confidence_map.json`) suppresses zero-TP rules and weight-adjusts
others.

---

## Regex Engine (`re_compat.ml`)

Thread-safe drop-in replacement for OCaml's `Str` module. Translates Str regex
syntax to PCRE, backed by the `Re` library. No global mutable state — match
results returned as values.

---

## ML Pipeline

v2 ByteClassifier (CNN+BiLSTM, 538K params) for 8 ambiguous TYPO rules.
Trained on A100, F1=0.9799. Formally verified in
`proofs/ML/SpanExtractorSound.v`.

- **Deterministic rules** (8): F1=1.0 by construction
- **Ambiguous rules** (8): ML candidate classifier
- **Integration**: Pre-computed confidence map in `evidence_scoring.ml`

---

## Proof System

142 Coq files, 1,130 theorems/lemmas, 0 admits, 0 axioms.

- **Core proofs** (33): Lexer, parser, expansion, arena, snapshot consistency,
  language contract, execution classes, validator DAG, hybrid invalidation,
  partial-parse locality, damage containment, repair monotonicity, stable
  node IDs, project/include graph, user-macro expansion, build-log
  conditional soundness
- **Generated proofs** (108): Per-rule soundness via `gen_coq_proofs.py`
- **ML proof** (1): `SpanExtractorSound.v` with measured precision/recall bounds
- **Tactic**: `qed_text_sound` in `RegexFamily.v` — one-shot solver for VPD families

---

## Build System

- `dune build` — OCaml + Coq compilation
- `dune runtest` — 92 test suites (~7,800 cases)
- Dependencies: OCaml ≥5.1.1, Coq 8.18.0, re ≥1.11.0, yojson ≥2.1, uutf ≥1.0.3

---

## Service Layer

- **SIMD Worker Pool**: fork+socketpair, hedge timer (12ms kqueue/epoll)
- **IPC Protocol**: framed Req/Resp/Cancel, big-endian wire format
- **REST API**: 6 endpoints (tokenize, expand, health, metrics, tokens, ready)
- **CLI**: `validators_cli.exe [--layer l0|l1|l2|l3|l4] <file.tex>`
