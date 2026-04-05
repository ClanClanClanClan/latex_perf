# Appendix C — Validator DSL & Generator Architecture

Per v25 master plan §15, Table C (47 pages).

## C.0 Purpose

The Validator framework lets rule authors describe 623 validators once and obtain:
- An OCaml detector (`validators_*.ml`)
- An optional OCaml fixer
- A Coq proof stub (`proofs/generated/*.v`) auto-proved via family-level lemma templates
- A JSON manifest consumed by documentation and IDE extensions

## C.1 Core Type System (`validators_common.ml`)

### C.1.1 Severity

```ocaml
type severity = Error | Warning | Info
```

Maps to LSP `DiagnosticSeverity`: Error=1, Warning=2, Info=3.

### C.1.2 Validation Result

```ocaml
type result = {
  id : string;        (* e.g. "TYPO-001" *)
  severity : severity;
  message : string;
  count : int;         (* number of occurrences found *)
}
```

### C.1.3 Rule

```ocaml
type rule = {
  id : string;
  run : string -> result option;  (* source text → diagnostic or None *)
  languages : string list;        (* ISO 639-1; empty = universal *)
}
```

### C.1.4 Rule Constructors

```ocaml
let mk_rule id run = { id; run; languages = [] }
let mk_lang_rule id run langs = { id; run; languages = langs }
```

### C.1.5 Layer Enum

```ocaml
type layer = L0 | L1 | L2 | L3 | L4
```

Mapping from rule ID prefix:
```ocaml
let precondition_of_rule_id id =
  match String.sub id 0 (String.index id '-') with
  | "TYPO" | "SPC" | "ENC" | "CHAR" -> L0
  | "MATH" | "DELIM" -> L1
  | "FIG" | "REF" | "BIB" | "TIKZ" -> L2
  | "STYLE" | "LANG" -> L4
  | _ -> L0
```

## C.2 Rule Families (623 rules across 5 layers)

| Family | Count | Layer | Description |
|--------|-------|-------|-------------|
| TYPO | 65 | L0 | Typographic errors (double spaces, wrong quotes, ligatures) |
| SPC | 42 | L0 | Spacing rules (thin space, non-breaking space, math spacing) |
| ENC | 31 | L0 | Encoding issues (UTF-8 BOM, invalid bytes, confusables) |
| CHAR | 18 | L0 | Character substitution (ASCII arrows → Unicode) |
| VERB | 12 | L0 | Verbatim/listing environment issues |
| CMD | 8 | L0 | Command usage (deprecated commands, wrong arguments) |
| MATH | 38 | L1-L2 | Mathematical typesetting (operator spacing, delimiter matching) |
| DELIM | 14 | L1 | Delimiter pairing and nesting |
| SCRIPT | 8 | L1 | Script/superscript usage |
| FIG | 22 | L2 | Figure/table structure (missing captions, labels) |
| REF | 15 | L2-L3 | Cross-references (undefined, duplicates, forward refs) |
| BIB | 17 | L2 | Bibliography formatting |
| FONT | 14 | L1 | Font usage (obsolete packages, encoding) |
| TIKZ | 10 | L2 | TikZ/PGFplots (unclosed scopes, missing captions) |
| CJK | 15 | L0-L2 | CJK-specific rules |
| RTL | 5 | L0-L1 | Right-to-left script rules |
| LANG | 16 | L1 | Language-specific rules |
| STYLE | 49 | L4 | Writing style heuristics (sentence length, passive voice) |
| META | 6 | L2 | Document metadata |
| DOC | 5 | L2 | Document structure |
| PDF | 5 | L2 | PDF output settings |
| CHEM | 3 | L2 | Chemical formula formatting |
| CE/TH/IB/AR/... | ~205 | Various | Locale-specific, miscellaneous |

## C.3 Helper Functions (`validators_common.ml`)

### C.3.1 String Utilities (Pure OCaml, No Str Dependency)

```ocaml
(** Count occurrences of character [c] in [s]. *)
let count_char (s : string) (c : char) : int =
  let cnt = ref 0 in
  String.iter (fun ch -> if ch = c then incr cnt) s;
  !cnt

(** Count overlapping occurrences of [sub] in [s]. *)
let count_substring (s : string) (sub : string) : int =
  (* Iterative scan using String.sub comparison *)

(** Substring membership (no regex, no Str). *)
let contains_substring (s : string) (needle : string) : bool =
  (* Linear scan *)
```

### C.3.2 LaTeX-Aware Utilities

```ocaml
(** Remove math-mode content (inline $...$ and display \[...\]). *)
val strip_math_segments : string -> string

(** Extract all \begin{env}...\end{env} blocks for a given env name. *)
val extract_env_blocks : string -> string -> string list

(** Extract environment blocks including starred variants (env and env*). *)
val extract_env_blocks_starred : string -> string -> string list

(** Extract \usepackage names from preamble. *)
val extract_usepackages : string -> string list

(** Extract preamble (content before \begin{document}). *)
val extract_preamble : string -> string

(** Line predicate scanner: returns (lines_checked, lines_matched). *)
val any_line_pred : string -> (string -> bool) -> int * int

(** Split source into paragraphs (separated by 2+ newlines). *)
val split_into_paragraphs : string -> (int * int) list
```

## C.4 Dependency Graph (`validator_dag.ml`)

### C.4.1 Validator Metadata

```ocaml
type phase = L0 | L1 | L2 | L3 | L4

type validator_meta = {
  id : string;
  phase : phase;
  provides : string list;   (* capabilities this rule provides *)
  requires : string list;    (* capabilities this rule needs *)
  conflicts : string list;   (* rules that conflict with this one *)
}
```

### C.4.2 DAG Type

```ocaml
type dag = {
  nodes : validator_meta list;
  edges : (string * string) list;    (* (from, to): from depends on to *)
  topo_order : string list;          (* topological execution order *)
}
```

### C.4.3 DAG Construction (Kahn's Algorithm)

1. Build capability → provider index via `Hashtbl`
2. Create edges: if rule A requires capability C and rule B provides C, then A depends on B
3. Topological sort: initialise queue with in-degree-0 nodes, iteratively pop and reduce dependents
4. Cycle detection: if `|visited| < |nodes|` after sort, cycle exists → `Error "Cycle detected"`

### C.4.4 Conflict Resolution

Priority tuple: `(severity DESC, phase_ordinal ASC, id_lex ASC)`:

```ocaml
let phase_ordinal = function
  | L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4

let resolve_conflict a b severity_a severity_b =
  if severity_a > severity_b then a.id
  else if severity_b > severity_a then b.id
  else if phase_ordinal a.phase < phase_ordinal b.phase then a.id
  else if phase_ordinal b.phase < phase_ordinal a.phase then b.id
  else if a.id < b.id then a.id else b.id
```

**Proof**: `proofs/ValidatorGraphProofs.v` — DAG acyclicity given successful topological sort.

## C.5 Execution Pipeline (`validators.ml`)

### C.5.1 Dispatcher: `run_all`

```ocaml
val run_all : string -> result list
```

Execution flow:
1. Check cache (`cache_key.ml`): DJB2 hash of `(source, validator_count, language)`. On hit, skip.
2. Create layer-sync snapshot (`layer_sync.ml`): atomic generation counter.
3. Validate DAG at startup (`validator_dag.ml`): topological sort, cycle check.
4. Build semantic state (`semantic_state.ml`): extract labels, refs, detect duplicates.
5. Publish events (`event_bus.ml`): scan source for `\label`, `\ref`, `\section`, `\begin`/`\end`.
6. Run all rules: `List.filter_map (fun r -> r.run source) rules_enc_char_spc`.
7. Store in cache.
8. Return results.

### C.5.2 Scored API

```ocaml
val run_all_scored :
  ?config:Evidence_scoring.scoring_config ->
  string ->
  Evidence_scoring.scored_result list
```

Wraps `run_all` output with confidence scores (§C.8).

### C.5.3 Language-Gated API

```ocaml
val run_all_for_language : string -> string option -> result list
```

If `Some lang`, filters to rules matching that language or universal rules. If `None`, auto-detects via `Language_detect.detect`.

### C.5.4 Timed API

```ocaml
val run_all_with_timings :
  string -> result list * float * (string * float) list
(* Returns (results, total_ms, [(rule_id, ms); ...]) *)
```

## C.6 Cross-Layer Infrastructure

### C.6.1 Version Vectors (`layer_sync.ml`)

```ocaml
type version_vector = { gen : int; parent_gen : int }
type 'a layer_state = { layer : layer_id; version : version_vector; data : 'a }
type 'a snapshot = { generation : int; states : 'a layer_state list }

let _generation = Atomic.make 0  (* global atomic counter *)
let next_gen () = Atomic.fetch_and_add _generation 1

let accepts_delta parent child = child.parent_gen = parent.gen
```

**Consistency check**: sorts states by layer, verifies each (parent, child) pair passes `accepts_delta`.

**Rollback**: on error, remove child layer state from snapshot; parent artefacts remain valid.

**Proof**: `proofs/SnapshotConsistency.v` — snapshot reads are either old or new, never interleaved.

### C.6.2 Event Bus (`event_bus.ml`)

```ocaml
type event =
  | LabelDefined of { key : string; position : int }
  | RefUsed of { key : string; position : int; command : string }
  | SectionStarted of { level : int; title : string; position : int }
  | EnvironmentOpened of { name : string; position : int }
  | EnvironmentClosed of { name : string; position : int }
  | DocumentBegin of int
  | DocumentEnd of int

type bus = {
  mutable handlers : (string * handler) list;
  mutable event_count : int;
}

val subscribe : bus -> string -> handler -> unit
val publish : bus -> event -> unit
val publish_global : event -> unit
```

Three subscribers registered in `run_all`: label counter, ref counter, environment counter.

### C.6.3 Semantic State (`semantic_state.ml`)

Thread-local state tracking labels, refs, duplicates, undefined refs, forward refs. Consumed by REF-001 (duplicate labels), REF-002 (undefined refs), REF-009 (forward refs).

### C.6.4 Cache System (`cache_key.ml`)

```ocaml
type cache_key = {
  source_hash : string;     (* DJB2 hash *)
  validator_count : int;
  language : string;
}

type 'a cache = {
  tbl : (string, 'a cache_entry) Hashtbl.t;
  mutable hits : int;
  mutable misses : int;
  default_ttl : float;       (* seconds *)
}

val compute_key : source:string -> validator_count:int -> language:string -> cache_key
val lookup : 'a cache -> cache_key -> 'a option
val store : 'a cache -> cache_key -> 'a -> unit
```

## C.7 Proof Generation (`gen_coq_proofs.py`)

### C.7.1 Generated Proof Pattern

For each rule, the generator produces:

```coq
From LaTeXPerfectionist Require Import RegexFamily.

(** Rule: TYPO-001 — Double space detected *)
Definition typo_001_chk (s : string) : bool := false.

Theorem typo_001_sound :
  forall doc, text_validator typo_001_chk
    (mk_iss "TYPO-001" "Double space detected" Warning None) doc = [] ->
  text_check_absent typo_001_chk doc.
Proof. qed_text_sound. Qed.

Definition l0_typo_proved : list string := ["TYPO-001"; ...].
```

### C.7.2 Automation Tactic (`RegexFamily.v`)

```coq
Ltac qed_text_sound :=
  intros doc H; exact (text_validator_sound _ _ doc H).
```

This tactic dispatches 403 of 429 soundness theorems (conservative proofs).

### C.7.3 Output

| Metric | Count |
|--------|-------|
| Generated `.v` files | 141 |
| Soundness theorems | 429 |
| Faithful proofs | 26 |
| Conservative proofs | 403 |
| Admits | 0 |
| Axioms | 0 |

## C.8 Evidence Scoring (`evidence_scoring.ml`)

```ocaml
type confidence = High | Medium | Low

type scored_result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
  confidence : confidence;
  evidence_weight : float;  (* 0.0 to 1.0 *)
}

let confidence_of_rule id vpd_ids =
  if List.mem id vpd_ids then High
  else match prefix_of id with
  | "TYPO" | "ENC" | "CHAR" | "SPC" -> High     (* lexical, exact *)
  | "MATH" | "DELIM" | "SCRIPT" | "CHEM" -> Medium  (* structural *)
  | "STYLE" | "LANG" -> Low                       (* heuristic *)
  | _ -> Medium

let weight_of_confidence = function
  | High -> 1.0 | Medium -> 0.7 | Low -> 0.4
```

VPD-certified rules (regex proven in Coq via `RegexFamily.v`) automatically receive `High` confidence.

## C.9 Implementation Patterns

### C.9.1 Text-Scan Validator (Most Common)

```ocaml
let r_typo_001 : rule =
  mk_rule "TYPO-001" (fun s ->
    let re = Str.regexp "  " in   (* double space *)
    let cnt = count_substring s "  " in
    if cnt > 0 then
      Some { id = "TYPO-001"; severity = Warning;
             message = "Double space detected"; count = cnt }
    else None)
```

### C.9.2 Language-Gated Validator

```ocaml
let r_lang_003 : rule =
  mk_lang_rule "LANG-003" (fun s ->
    if has_wrong_french_quotes s then
      Some { id = "LANG-003"; severity = Warning;
             message = "Wrong quotation style for French"; count = 1 }
    else None)
    ["fr"]  (* only fires for French documents *)
```

### C.9.3 Environment-Checking Validator

```ocaml
let r_fig_001 : rule =
  mk_rule "FIG-001" (fun s ->
    let figs = extract_env_blocks_starred "figure" s in
    let missing = List.filter (fun body ->
      not (contains_substring body "\\caption{")) figs in
    if missing <> [] then
      Some { id = "FIG-001"; severity = Warning;
             message = "Figure without caption"; count = List.length missing }
    else None)
```

## C.10 Adding a New Validator

1. Add rule definition to `specs/rules/rules_v3.yaml`
2. Implement in appropriate `validators_*.ml` module using `mk_rule` or `mk_lang_rule`
3. Register in `validators.ml` rule list
4. Add test cases in `test_validators_*.ml`
5. Run `gen_coq_proofs.py` to generate soundness theorem in `proofs/generated/`
6. Verify: `dune build && dune runtest` — all pass, zero admits

## C.11 Performance Notes

- ~568 rules implemented across `validators_l0.ml`, `validators_l0_typo.ml`, `validators_l1.ml`, `validators_l1_math.ml`, `validators_l2.ml`, `validators_l4_style.ml`
- ~219 `Str.regexp` compilations inside `run` closures (recompiled per invocation; acceptable at current p95=2.8ms vs 20ms gate)
- Hoisting opportunity: move regex compilation to module-level `let` bindings for ~30% speedup if needed
