# Appendix C — Validator DSL & Generator Architecture

Per v25 master plan §15, Table C (47 pages).

## C.1 Overview

The validator framework processes LaTeX documents through 623 rules organised in a dependency DAG. Rules are defined in `specs/rules/rules_v3.yaml` and implemented as OCaml functions in the `validators_*.ml` modules.

## C.2 Rule Schema

Each rule in `rules_v3.yaml` follows this schema:

```yaml
- id: TYPO-001
  layer: L0_Lexer
  severity: Warning
  message: "Double space detected"
  fix: remove_extra_space
  languages: []           # empty = universal
  precondition: null
  category: typography
```

### Fields

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Unique rule identifier (FAMILY-NNN) |
| `layer` | enum | L0_Lexer, L1_Expanded, L2_Ast, L3_Semantics, L4_Style |
| `severity` | enum | Error, Warning, Info |
| `message` | string | Human-readable diagnostic message |
| `fix` | string | Suggested fix identifier |
| `languages` | list | ISO 639-1 codes; empty = all languages |
| `precondition` | string? | Rule ID that must pass first |
| `category` | string | Rule family (typography, spacing, encoding, ...) |

## C.3 Rule Families

| Family | Count | Layer | Description |
|--------|-------|-------|-------------|
| TYPO | 65 | L0 | Typographic errors (double spaces, wrong quotes) |
| SPC | 42 | L0 | Spacing rules (thin space, non-breaking space) |
| ENC | 31 | L0 | Encoding issues (UTF-8 BOM, invalid bytes) |
| MATH | 38 | L1-L2 | Mathematical typesetting |
| FIG | 22 | L2 | Figure/table structure |
| REF | 15 | L2-L3 | Cross-references and labels |
| BIB | 17 | L2 | Bibliography formatting |
| FONT | 14 | L1 | Font usage |
| STYLE | 49 | L4 | Writing style heuristics |
| TIKZ | 10 | L2 | TikZ/PGFplots |
| CJK | 15 | L0-L2 | CJK-specific rules |
| RTL | 5 | L0-L1 | Right-to-left script rules |
| LANG | 16 | L1 | Language-specific rules |
| Others | 284 | Various | META, DOC, PDF, CE, IB, TH, AR, ... |

## C.4 Implementation Pattern

### OCaml Validator Shape

```ocaml
let r_typo_001 : rule =
  mk_rule "TYPO-001" (fun s ->
    (* s is the full document source text *)
    if contains_double_space s then
      [ mk_result Warning "Double space detected" ]
    else [])
```

### Language-Gated Rule

```ocaml
let r_lang_003 : rule =
  mk_lang_rule "LANG-003" (fun s ->
    if has_wrong_quotes s then
      [ mk_result Warning "Wrong quote style for language" ]
    else [])
    ["fr"; "de"]  (* only fires for French and German *)
```

### Common Helpers (`validators_common.ml`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `count_char` | `string -> char -> int` | Count occurrences of a character |
| `count_substring` | `string -> string -> int` | Count substring occurrences |
| `contains_substring` | `string -> string -> bool` | Pure OCaml, no Str dependency |
| `strip_math_segments` | `string -> string` | Remove `$...$` and `\[...\]` content |
| `extract_env_blocks` | `string -> string -> string list` | Extract environment bodies |
| `extract_usepackages` | `string -> string list` | List packages from preamble |

## C.5 Dependency Graph

### DAG Construction

At startup, `validator_dag.ml` builds a directed acyclic graph:

1. Parse `requires` and `conflicts` from each rule's manifest
2. Build adjacency list
3. Run Kahn's topological sort
4. Detect cycles → bootstrap failure if any found

### Conflict Resolution

When two rules conflict (e.g., both want to modify the same text region):
- Priority tuple: `(severity, phase_ordinal, id_lexicographic)`
- Higher severity wins
- On tie: earlier phase wins
- On tie: lexicographically smaller ID wins

### Proof

`proofs/ValidatorGraphProofs.v` proves the DAG is acyclic given the topological sort succeeds.

## C.6 Execution Pipeline

```
Source text
  │
  ├─ L0 validators (token-level)      ← SIMD batch-AC where possible
  │     │
  │     ▼
  ├─ L1 validators (expanded tokens)  ← after macro expansion
  │     │
  │     ▼
  ├─ L2 validators (AST-level)        ← after parsing
  │     │
  │     ▼
  ├─ L3 validators (semantic)         ← label/ref state, log parsing
  │     │
  │     ▼
  └─ L4 validators (style)            ← sentence-level heuristics
```

### Caching

`cache_key.ml` computes a DJB2 hash over `(source, validator_count, language)`. On cache hit, validators are skipped entirely.

### Evidence Scoring

`evidence_scoring.ml` assigns confidence levels:
- **High**: VPD-certified rules (regex proven in Coq)
- **Medium**: Heuristic rules (text pattern matching)
- **Low**: ML-assisted rules (byte classifier)

## C.7 Adding a New Validator

1. Add rule to `specs/rules/rules_v3.yaml`
2. Implement in appropriate `validators_*.ml` file
3. Register in `validators.ml` `get_rules()` function
4. Add test cases in `test_validators_*.ml`
5. Run `gen_coq_proofs.py` to generate soundness theorem
6. Verify: `dune build && dune runtest`

## C.8 Generator Architecture

`scripts/infra/proof_farm/gen_coq_proofs.py`:

1. Reads `rules_v3.yaml` for rule IDs and metadata
2. Reads `vpd_patterns.json` for regex patterns
3. Generates `proofs/generated/<Layer>_<Family>.v` files
4. Each file contains:
   - Check function definition
   - Soundness theorem
   - Rule catalogue list
5. Uses `PROOF_LAYERS` config for layer-to-file mapping

**Current output**: 141 generated `.v` files, 429 soundness theorems.
