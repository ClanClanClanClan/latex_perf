# Appendix B — Layer Interfaces & Core Data-Structures

Per v25 master plan §15, Table B (93 pages). Canonical unified spec.

---

## B-0 Reading Map & Conventions

| Symbol | Meaning |
|--------|---------|
| `=>` | Pure function (no side-effects, total) |
| `delta` | Incremental delta type (layer-specific) |
| `...` | Omitted fields identical to previous definition |

Language: OCaml 5.1.1, dune-coq 0.8.0, `--safe-string`.

Proof twin: each `.ml` module has a Coq twin `.v` exporting the same interface
with soundness lemmas.

---

## B-1 Shared Data Types

### B-1.1 Location (`parser_l2.ml`)

```ocaml
type loc = { line : int; col : int; offset : int }
```

Byte-offsets into original UTF-8 source (half-open intervals).

### B-1.2 Token Types

#### L0 Token (`tokenizer_lite.ml`)

```ocaml
type kind =
  | Word           (* text content *)
  | Space          (* horizontal whitespace *)
  | Newline        (* line break *)
  | Command        (* \foo *)
  | Bracket_open   (* ( [ { *)
  | Bracket_close  (* ) ] } *)
  | Quote          (* " *)
  | Symbol         (* everything else *)

type tok = { kind : kind; s : int; e : int; ch : char option }
```

#### L2 AST Node (`parser_l2.ml`)

```ocaml
type cmd = { name : string; opts : string list; args : string list }

type node =
  | Word of string
  | Cmd of cmd
  | Group of node list
  | Environment of { env_name : string; opts : string list; body : node list }
  | MathInline of string
  | MathDisplay of string
  | Comment of string
  | Verbatim of { env_name : string; content : string }
  | Whitespace of string
  | Newline
  | Error of { message : string; position : int }

type located_node = { node : node; loc : loc }
```

### B-1.3 Catcode (`catcode.ml`, `proofs/Catcode.v`)

```ocaml
(* 16 TeX category codes, proven total *)
let classify_ascii (b : int) : int =
  match b land 0xFF with
  | 92  -> 0  (* \ = Escape *)     | 123 -> 1  (* { = BeginGrp *)
  | 125 -> 2  (* } = EndGrp *)     | 36  -> 3  (* $ = Math *)
  | 38  -> 4  (* & = AlignTab *)   | 10 | 13 -> 5  (* Newline *)
  | 35  -> 6  (* # = Param *)      | 94  -> 7  (* ^ = Superscr *)
  | 95  -> 8  (* _ = Subscr *)     | 0   -> 9  (* NUL = Ignored *)
  | 32 | 9 -> 10 (* Space *)       | 126 -> 13 (* ~ = Active *)
  | 37  -> 14 (* % = Comment *)    | 127 -> 15 (* DEL = Invalid *)
  | c when is_letter c -> 11        (* Letter *)
  | _   -> 12                       (* Other *)
```

Coq proof: `Catcode.v` — `nat_catcode_inverse`, `catcode_eq_dec` (both QED).

### B-1.4 Severity & Validation Result (`validators_common.ml`)

```ocaml
type severity = Error | Warning | Info

type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
}

type rule = {
  id : string;
  run : string -> result option;
  languages : string list;   (* ISO 639-1; empty = universal *)
}

type layer = L0 | L1 | L2 | L3 | L4

let mk_rule id run = { id; run; languages = [] }
let mk_lang_rule id run langs = { id; run; languages = langs }
```

### B-1.5 Delta Types (Cross-Layer)

```ocaml
(* Spec-defined delta types for incremental processing.
   Currently, run_all does full re-evaluation; deltas
   are planned for the Elder runtime (v26). *)

type token_delta =
  | ReplaceSlice of { start_idx : int; end_idx : int; with_ : tok array }
  | NoChange

type parser_delta =
  | ReplaceSubtree of { path : int list; with_ : node list }
  | NoAstChange

type sem_delta =
  | Patch of sem_patch
  | NoSemChange
```

---

## B-2 Layer 0 — Tokenizer (`tokenizer_lite.ml`)

```ocaml
val tokenize : string -> tok list
```

Single-pass byte-level tokenizer producing flat token list. Features:
- ASCII fast path via `is_letter`
- UTF-8 multi-byte support via `decode_uchar_at` (Latin Extended, Greek,
  Cyrillic, Arabic, CJK)
- CJK characters: individual Word tokens (no whitespace word boundaries)
- Command extraction: `\` + ASCII letters

Complexity: O(n) time, single pass.

### Key Helpers

```ocaml
val is_letter : char -> bool         (* ASCII a-z, A-Z, 0-9 *)
val decode_uchar_at : string -> int -> int * int  (* codepoint, byte_count *)
val is_unicode_letter : int -> bool  (* Latin Ext, Greek, Cyrillic, Arabic, CJK *)
val is_cjk : int -> bool            (* CJK Unified, Hiragana, Katakana *)
```

---

## B-3 Layer 1 — Macro Expander (`simple_expander.ml`)

```ocaml
val expand_fix : string -> string
  (** Iterative expansion to fixpoint. max_expansion_depth = 100. *)

val expand_fix_with : Catalogue_loader.config -> string -> string
  (** Expansion with custom catalogue. *)
```

### Macro Catalogue

| Category | Count | Source |
|----------|-------|--------|
| Symbol macros | 441 | `macro_catalogue.v25r2.json` |
| Argsafe macros | 79 | `macro_catalogue.argsafe.v25r1.json` |
| **Total** | **520** | epsilon-safe, deterministic |

Fuel bound: `max_expansion_depth = 100`. Proof: `ExpandProofsFinal.v` —
`sufficient_fuel` theorem (QED).

### Brace-Aware Expansion

```ocaml
let find_brace_block s i =
  (* Returns Some (content_start, content_length) or None *)
  (* Tracks brace depth; handles nested {} correctly *)
```

Handles: `\textbf`, `\emph`, `\bfseries`, all catalogue controls.

---

## B-4 Layer 2 — PEG Parser (`parser_l2.ml`)

```ocaml
val parse : string -> node list
val parse_located : string -> located_node list * (string * loc) list
val parse_with_envs : string -> node list
val extract_document : string -> document
val parse_success : string -> bool
val find_dirty_region : string -> string -> dirty_region
val serialize : node list -> string
```

### Document Structure

```ocaml
type document = {
  preamble : located_node list;
  body : doc_element list;
  labels : (string * loc) list;
  refs : (string * loc) list;
  errors : (string * loc) list;
  packages : (string * string option * loc) list;
  documentclass : (string * string option) option;
}
```

### Environment Recognition

| Category | Count | Environments | AST Node | Parsing |
|----------|-------|-------------|----------|---------|
| Math | 26 | equation, equation*, align, align*, gather, gather*, multline, multline*, eqnarray, eqnarray*, math, displaymath, flalign, flalign*, split, cases, matrix, pmatrix, bmatrix, Bmatrix, vmatrix, Vmatrix, smallmatrix, aligned, alignedat, gathered | `MathDisplay` | Opaque string body via `parse_env_body` |
| Verbatim | 5 | verbatim, lstlisting, minted, Verbatim, tikzpicture | `Verbatim` | Opaque string body via `parse_env_body` |
| Float | 6 | figure, figure*, table, table*, algorithm, algorithm* | `Float` | Recursive parse; caption/label extracted |
| Section | 5 | chapter, section, subsection, subsubsection, paragraph | `Section` | Command args → level 0-4, title |
| Other | ∞ | all unrecognised `\begin{env}` | `Environment` | Recursive `parse_nodes` on body |

Dispatch order in `parse_nodes` (line 334-346): verbatim checked first
(`is_verbatim_env`), then math (`is_math_env`), then recursive fallback.
Float and section recognition happens in `extract_document`, not during parsing.

### Metadata Extraction

`extract_document` extracts:
- Labels: `\label{...}` → `(key, loc)` list
- Refs: `\ref`, `\eqref`, `\autoref`, `\cref`, `\Cref`, `\pageref`, `\nameref`, `\href` → `(key, loc)` list
- Packages: `\usepackage[opts]{pkg}` → `(name, opts, loc)` list (comma-separated args split)
- Document class: `\documentclass[opts]{class}` → `(class, opts) option`
- Sections: `\chapter`, `\section`, `\subsection`, `\subsubsection`, `\paragraph` → level 0-4

Grammar origin: `specs/v25_R1/l2_parser_peg_grammar.peg` (239 lines).

---

## B-5 Layer 3 — Semantic State (`semantic_state.ml`)

```ocaml
type label_entry = { key : string; position : int; prefix : string }
type ref_entry = { key : string; position : int; command : string }

type semantic_state = {
  labels : label_entry list;
  refs : ref_entry list;
  duplicate_labels : string list;
  undefined_refs : string list;
  forward_refs : string list;
}

val analyze : string -> semantic_state
val build_state : string -> semantic_state  (* alias for analyze *)
val set_state : semantic_state -> unit    (* thread-local *)
val get_state : unit -> semantic_state option
val clear_state : unit -> unit
```

Labels carry a `prefix` field (`"fig:"`, `"eq:"`, `"sec:"`, `"tab:"`, or `""`).
Refs carry a `command` field (`"ref"`, `"eqref"`, `"autoref"`, `"cref"`, etc.).

Consumers: REF-001 (duplicate labels), REF-002 (undefined refs), REF-009 (forward refs).

---

## B-6 Layer 4 — Style Validators (`validators_l4_style.ml`)

Sentence-level heuristic rules operating on text after math/verbatim stripping.

```ocaml
(* 49 STYLE rules + 10 locale rules *)
val sentence_split : string -> string list
val word_count : string -> int
val extract_heading_titles : string -> (string * int) list
```

Style rules detect: sentence length, passive voice, repeated words, weak
phrases, capitalisation errors, list consistency.

---

## B-7 Validator Engine (`validators.ml`, `validators.mli`)

```ocaml
val run_all : string -> result list
  (** Run all active rules. Integrates: cache check, layer-sync snapshot,
      DAG validation, semantic state, event bus, evidence scoring. *)

val run_all_scored :
  ?config:Evidence_scoring.scoring_config ->
  string ->
  Evidence_scoring.scored_result list

val run_all_for_language : string -> string option -> result list
  (** Language-gated execution. Auto-detects if None. *)

val run_all_with_timings :
  string -> result list * float * (string * float) list
  (** Returns (results, total_ms, [(rule_id, ms); ...]). *)

val run_all_with_timings_for_layer :
  string -> layer -> result list * float * (string * float) list

val precondition_of_rule_id : string -> layer
val rules_vpd_catalogue : rule list   (** 80 VPD-certified rules *)
val vpd_catalogue_count : int
```

---

## B-8 Log Parser (`log_parser.ml`, `log_parser.mli`)

Parses LaTeX compile output (`.log` files) into structured events.

```ocaml
type box_type = Hbox | Vbox

type log_event =
  | Overfull of {
      box : box_type;
      amount_pt : float;
      line_start : int;
      line_end : int;
    }
  | Underfull of { box : box_type; badness : int; line_start : int }
  | PageNumber of int
  | WidowPenalty of { page : int }
  | ClubPenalty of { page : int }
  | FloatWarning of { message : string; line : int }
  | LatexWarning of { message : string; line : int }

type log_context = {
  events : log_event list;
  overfull_lines : (int * int) list;  (* (line_start, line_end) pairs *)
  underfull_lines : int list;
  pages : int list;
  max_overfull_pt : float;
  has_widows : bool;
  has_orphans : bool;
  tikz_compile_times : float list;  (* seconds per TikZ externalization *)
}

val empty_context : log_context
val parse_log : string -> log_context

(** Thread-local log context for validators needing compile-log data. *)
val set_log_context : log_context -> unit
val get_log_context : unit -> log_context option
val clear_log_context : unit -> unit
```

Used by LAY/PAGE family validators (55 rules requiring compile-log analysis,
planned for v26 L3 integration).

Regex patterns: `re_overfull_hbox`, `re_overfull_vbox`, `re_underfull_hbox`,
`re_underfull_vbox`, `re_page_number`, `re_float_warning`, `re_widow`, `re_club`.

---

## B-9 Cross-Layer Delta-Flow Summary

| Producer → Consumer | Delta Type | Data Carried |
|---------------------|-----------|--------------|
| Lexer (L0) → Expander (L1) | `token_delta` | Slice replacement |
| Expander (L1) → Parser (L2) | `token_delta` | Idem |
| Parser (L2) → Interpreter (L3) | `parser_delta` | AST subtree splice |
| Interpreter (L3) → Styler (L4) | `sem_delta` | Counter/label diff |
| Styler (L4) → Front-end | `issue_delta` | Added/removed diagnostics |

**Current status:** Full re-evaluation via `run_all`. Incremental delta
propagation planned for Elder runtime (v26).

---

## B-10 Performance Contracts (Spec Targets)

| Layer | Max Latency | Peak RSS | Comments |
|-------|------------|----------|----------|
| L0 | 80 µs / 4 KiB edit | 16 MiB | SIMD xxHash + FSM lexer |
| L1 | 200 µs | 64 MiB | Fuel-bounded, DAG cache |
| L2 | 300 µs | 24 MiB | Window re-parse |
| L3 | 250 µs | 32 MiB | Finger-tree maps |
| L4 | 120 µs / paragraph | 12 MiB | Sentence-level, memoised |
| Elder dispatch | ≤ 40 µs | — | Dispatch, telemetry |
| **Elder total** | **≤ 1 ms** | **4 MiB overhead** | End-to-end budget |

**Measured (2026-04-05, M2-Pro baseline):**

| Benchmark | Target | Actual |
|-----------|--------|--------|
| Full-document p95 (1.1 MB) | ≤ 25 ms | 3.25 ms |
| Edit-window p95 (4 KB) | ≤ 1 ms | 0.075 ms |
| First-token p95 | ≤ 350 µs | 27 µs |

---

## B-11 Module Dependency Graph

```
token ──▶ layer0 ──▶ layer1 ──▶ layer2 ──▶ layer3 ──▶ layer4
 ▲          ▲           │           │           │
 │          └───────────┴───────────┴───────────┘
 └─────────────── data/location
```

No cycles; every `.ml` depends on `.mli` of lower tier only.

---

## B-12 Formal Proof Obligations Matrix

| File | Lines | Key Theorems | Status |
|------|-------|-------------|--------|
| `CoreProofs.v` | 6 | Core imports | QED |
| `Catcode.v` | 64 | `nat_catcode_inverse`, `catcode_eq_dec`, `nat_to_catcode_inv` | QED |
| `LexerDeterminism.v` | 7 | `lexer_step_determinism` | QED |
| `LexerTotality.v` | 10 | `lexer_step_total_nonempty` | QED |
| `LexerFaithfulStep.v` | 45 | `step_deterministic`, `step_progress` | QED |
| `LexerSmallstep.v` | 41 | Small-step lexer semantics | QED |
| `LexerIncremental.v` | 379 | Incremental re-lex correctness | QED |
| `LexerSoA.v` | 715 | SoA layout proofs | QED |
| `L0Smallstep.v` | 305 | Catcode-sensitive classifier | QED |
| `L0SmallstepControl.v` | 136 | Control-flow small-step | QED |
| `Expand.v` | 597 | Full expansion proofs | QED |
| `ExpandProofsFinal.v` | 35 | `sufficient_fuel`, `expand_no_teof` | QED |
| `RegexFamily.v` | 292 | `text_validator_sound`, `qed_text_sound` tactic | QED |
| `ParserSound.v` | 149 | 12 theorems (identity, flatten, well-formedness) | QED |
| `InterpLocality.v` | 138 | 8 theorems (diff algebra, insert/delete length) | QED |
| `LabelsUnique.v` | 31 | Duplicate label detection | QED |
| `ValidatorGraphProofs.v` | 70 | DAG acyclicity | QED |
| `SnapshotConsistency.v` | 76 | Cross-layer snapshot consistency | QED |
| `ElderProofs.v` | 42 | `update_preserves_length`, `update_at_correct` | QED |
| `Arena_safe.v` | 217 | Arena memory safety | QED |
| `ListWindow.v` | 73 | List windowing correctness | QED |
| `SectionRebalance.v` | 84 | 8 theorems (renumber preserves shape) | QED |
| `SplitPreservesOrder.v` | 106 | 7 theorems (sorted segments increasing) | QED |
| `proofs/generated/*.v` | 74 files | 429 per-rule soundness theorems | QED |
| **Total** | **3,662 + gen** | **429+ theorems, 0 admits, 0 axioms** | **QED** |
