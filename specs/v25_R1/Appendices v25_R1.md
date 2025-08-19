
⸻

Appendices.md (updated)

⸻

Appendix A — Consolidated Glossary & Acronym Index

(canonical reference for LaTeX Perfectionist v25, revision 2025‑07‑31)

Scope.
• Unifies every term that appeared in v25‑0.1‑draft, the 87‑question clarification set, the Focused Technical Integration Concerns, and all subsequent risk / corpus / timeline addenda.
• Entries are normative; wording matches the formal specification used in code‑comments and Coq documentation.
• Ordering: alphabetical, case‑insensitive. Cross‑references use “→”.

Term / Abbrev.	Definition & Context (section reference)
ABI	Application Binary Interface.  Stable C‑level boundary used by OCaml ⇄ Rust FFI for SIMD helpers (§8.2.4, §9.1).
ACL	Access‑Control List.  GitHub branch protection & proof‑farm namespace permissions (§11.3).
Aho–Corasick	Multi‑pattern string matching algorithm used to batch token‑sequence validators (§C‑10).
Arena	Bump‑allocator arena providing moving‑GC avoidance for tokens/AST nodes (Arena.alloc, §E‑4).
ASCII‑translit rule	Validator family that rewrites ASCII pseudo‑glyphs (“–>”) to proper Unicode (§C‑2).
AST	Abstract Syntax Tree — typed tree produced by L2 parser; root type document (data/ast.ml).
Audit‑trail	Hash‑chained log of validator generation steps; artefact of SBOM pipeline (§7.5, §12).
BERT	Bidirectional Encoder Representations from Transformers; base LM fine‑tuned for span extraction (G‑6).
Bitemporal Trie	Two‑axis trie keyed by (byte‑offset, revision‑timestamp); Elder cache backbone (§9.1).
Bootstrap Skeleton	Minimal compilable repo layout delivered Week 1; establishes directory & module naming (§14 week 1).
Build Farm	Kubernetes job set (proof-farm-) running parallel Coq compilation (§7.5, §6.1).
Byte Span	Pair (start,end) in UTF‑8 bytes, half‑open interval [start,end) (location.ml).
Catcode	TeX category code 0–15; stored per token; table proven total (§3.1.3, Token.Catcode).
Causal Cache	Future feature: editing CRDT integrated remote cache; not GA (§I‑9).
CI	Continuous Integration; GitHub Actions matrix defined in .github/workflows/ci.yml (§12.3).
Chunk	Fixed 4 KiB logical slice of source used by incremental lexer (§3.1.1).
CJK	Chinese/Japanese/Korean script class; triggers specialised validators (§F‑4).
Code‑gen	Automatic production of OCaml .ml + Coq .v from validator DSL (§7.4).
Confusables	Unicode glyphs visually similar; validator family ENC‑015 checks NFKC confusables (§F‑1).
Corpus	2 846 curated LaTeX papers + 4 synthetic suites; stored under corpus/ (§10.1).
Coverage Metric	Percentage of corpus documents for which all validators run without crash (§10.2).
Crash‑free latency	Perf KPI: p99 latency measured on sessions with zero validator panics (§9).
CRDT	Conflict‑free Replicated Data Type; referenced for future distributed editor support (§I‑9).
Cross‑layer Consistency	Property that snapshot hashes form monotone sequence; theorem snapshot_consistency (§14 week 47).
CSA	Cache Set Associativity — param in lexer chunk index; default = 4.
DAG	Directed Acyclic Graph; used for macro‑expansion cache and validator dependency graph (§7.2).
Delta	Minimal change descriptor between artefacts; four variants: token_delta, parser_delta, sem_delta, issue_delta (§B‑9).
Determinism Proof	interp_deterministic: interpreter output independent of traversal order (§D‑4.4).
DFA	Deterministic Finite Automaton; compiled form of regex validators (§7 & H‑2).
Dirty Region	Byte span invalidated by edit; propagated through layers by Elder (§4.3).
Disaster‑Recovery Playbook	Steps for hardware loss, S3 corruption, proof‑farm outage (§11.3).
dune‑coq	Build‑system glue generating .vo from .v; pinned version 0.6.1.
EDF	Earliest Deadline First scheduler used inside validator thread‑pool (§I‑6).
Elder	Incremental orchestrator caching 5 layers; design in Appendix I.
Elder Box	Internal data‐structure {artefact; hash; dirty_ranges} for a layer (§I‑2).
End‑to‑End Gate	CI workflow milestone-gate-* that checks cross‑layer KPIs (Table 14).
Env Stack	Interpreter field tracking current environment nesting (sem_state.ml).
Expand Fuel	Natural number budget ensuring macro expansion termination; proof expand_fuel_monotonic (§D‑3.2).
Fix‑Template	DSL snippet for automatic source rewrite; compiled to OCaml replacer (§C‑6).
FSA‑Trie	Finite‑state automaton compressed trie for labels table (§5.4).
Fuzz Suite	QuickChTeX property‑based random generator; 2 M cases/day (§10.3).
GA	General Availability release; Week 156 milestone (§14.1).
GPU Cold‑Start	Optional Metal/CUDA off‑load of heavy NLP; Q11 research (§E‑8).
Ground Truth	Human‑labelled YAML file enumerating expected validator issues (§10.2).
HAMT	Hash‑array mapped trie backing user macro table (MacroEnv) (§3.3.3).
HDBSCAN	Hierarchical density‑based clustering; groups ML spans into pattern families (§G‑4).
ICU	International Components for Unicode; provides BreakIterator (§6.1).
IDE Latency	95‑th percentile edit‑to‑diagnostic time measured in VS Code plugin; SLA < 1 ms (§9).
Incr Key	Tuple unique per cache entry: (layer_id,start,end,cat_hash,rev) (§B‑9).
Interpreter	L3 fold M reducer computing semantic_state (§5).
Issue	Diagnostic record {id; loc; severity; msg} (Issue.t).
JSON Manifest	Side‑file produced by code‑gen describing validator metadata (manifest/XYZ.json).
LangID	Compact language classifier (88 languages, 99 % accuracy) (§6.3.1).
Layer Artefact	Cached result for a processing stage: tokens, AST, sem_state, etc. (§B‑9).
Lexer State	Record with catcode table, line_no, pending BOM; used to resume chunk lexing (§B‑3).
LRU	Least‑Recently‑Used cache eviction; expander DAG cache window = 4096 (§3.3.4).
Menhir‑cert	Certified LR(1) parser generator; base for PEG parser proofs (§D‑3.3).
Merkle Snapshot	Root hash of chunk‑id tree, uniquely identifies document revision (§I‑3.1).
Metric Dashboard	Grafana board auto‑generated nightly; endpoints /perf, /quality, /proof.
ML‑Assist	Pipeline that mines patterns, generates validator specs, auto‑proves them (§7, G‑6).
Monotone Fuel Lemma	expand_fuel_monotonic — more fuel never changes success result (§D‑3.2).
NFA Extraction	Coq tactic converting regex to Thompson NFA for generic proofs (§H‑2.2).
NFC/NFD/NFKC/D	Unicode normalisation forms; NFC used for hashing, NFD inside AST (§F‑1).
NPD	Neural Pattern Discovery module – BERT + CRF span extractor (§G‑6).
Opcode Budget	Micro‑benchmark counter limiting validator execution instructions (perf harness).
p50/p90/p95/p99	Latency percentiles used in SLA & dashboards (§9).
Parser Delta	Splice description {path; with_} bridging L2 → L3 (§B‑5).
Pattern DSL	YAML + body dialects (regex, token, structural DSL) that compile to validators (§C‑2).
PEG	Parsing Expression Grammar; 630‑line spec for LaTeX subset (§4.2).
Perf Harness	Rust binary perfkit simulating keystrokes and recording metrics (§9.4).
Proof Debt	Count of Admitted.; must be 0 by Week 130 gate (§14.2).
Proof Family	Set of validators sharing generic proof template (RegexFamily, TokenSeqFamily, …) (§H‑1).
Proof‑Farm	Scalable Coq compilation cluster (proof-farm-ctl) (§6.1).
QuickChTeX	Property‑based fuzz generator targeting TeX grammar (§10.3).
RB Invariant	Ring buffer length ≤ capacity; lemma rb_write_maintains_invariant (§Workflow example).
RegexProofs	Coq library providing generic_regex_sound tactic (§H‑2.2).
Round‑trip Property	concat (split txt) = txt invariant for sentence splitter (§6.5).
Rule Family	Group of validators (e.g., TYPO‑###) sharing pattern skeleton (§7).
S3	Object store holding corpus and SBOM artefacts (§11.3).
SBOM	Software Bill‑of‑Materials generated by CI; scanned for CVEs (§12).
Seccomp	Linux syscall filter used to sandbox validator plugins (§7.1).
Semantic State (Ω)	Record of counters, labels, refs; maintained by interpreter (§5.1).
SIMD	Single Instruction Multiple Data; AVX‑512 & NEON used for lexer/scanner (§E‑1).
Snapshot Id	256‑bit Blake3 hash of chunk tree; key for Elder cache (§I‑3.1).
Soundness	Proof that validator detects all and only intended violations (validator_sound) (§D‑5).
Span Extractor	BERT + CRF NPD model tagging error spans in corpus (§G‑6).
Splice Equiv Lemma	splice(parse_window(δ)) ≡ parse(full) (§4.3.1).
SSA	Static Single Assignment; not used (recorded to avoid confusion with CSS).
STYLE Block	Paragraph‑level text unit processed by L4 (§6.1).
Telemetry Event	JSON blob posted to ClickHouse for every validator execution (§6.2).
Token ADT	Six‑constructor sum type with decidable equality (§3.1.2).
TokenSeq Pattern	Validator dialect matching on token variants, compiled to Aho–Corasick (§C‑2‑2).
Trace Replay	Perf harness mode replaying real editing sessions from VS Code plugin.
Trie Hash	64‑bit FNV of parent‑chain; feature for NPD (§G‑3.3).
Typographic Validator	RULE family checking spacing, punctuation per language (§F‑3).
Unicode Script	ICU property grouping codepoints; used in script detector (§F‑2).
Validation Issue	See Issue.
Validator	Pair (detector, proof) packaged as OCaml functor; may include fixer (§C‑4).
Validator Dependency Graph	DAG capturing “Validator B uses fix of A”; cycles forbidden (§Technical Concern 2).
Vectorised xxHash	AVX/NEON implementation hashing 256‑byte windows (§E‑1).
Version Vector	(layer, snapshot_id) tuple used for cross‑layer consistency checks (§5).
VSNA	Verified State‑Machine Net‑Accurate automaton representation of validator regex (§7.4).
Whitespace‑safe	Fix which inserts/deletes only space/Tab/NBSP; lemma whitespace_preserves_render (H‑2).
Workflow Bot	GitHub Action posting regression diffs for golden files (§10.2).
xxHash3	Non‑cryptographic hash function variant; SIMD accelerated (§E‑1).
YAML Spec	Front‑matter of .vdl validator files (id, family, pattern, …) (§C‑1).
Zero‑Admit Gate	CI rule failing build if any Admitted. after Week 130 (§14.2).

(Total entries = 107.)

⸻

End of Appendix A.

⸻

Appendix B — Layer Interfaces & Core Data‑Structures

(canonical, unified spec — revision 2025‑07‑31, supersedes all prior drafts)

⸻

B‑0 Reading Map & Conventions

Symbol	Meaning
⇒	Pure function (no side‑effects, total)
Δ	Incremental delta type (layer‑specific)
⊥	Impossible case (used in proofs)
…	Omitted fields identical to previous definition

Language. OCaml 5.1.1, dune‑coq 0.6.1, --safe-string.
Proof twin. Each .ml module has a Coq twin .v exporting the same interface with soundness lemmas.

src/
 ├─ data/               (shared pure types)
 ├─ layer0_lexer.{ml,mli,vo}
 ├─ layer1_expander.{ml,mli,vo}
 ├─ layer2_parser.{ml,mli,vo}
 ├─ layer3_interpreter.{ml,mli,vo}
 ├─ layer4_styler.{ml,mli,vo}
 └─ elder_orchestrator.{ml,mli}

⸻

B‑1 Shared Data Types (src/data/)

B‑1‑1 location.ml

(** Byte‑offsets into original UTF‑8 source (half‑open) *)
(* The core token type - 6 constructors *)
type token =
  | TChar       of Uchar.t * Catcode.t          (* UTF-8 code-point *)
  | TMacro      of string                       (* control sequence *)
  | TParam      of int                          (* #1 … #9          *)
  | TGroupOpen                                  (* "{"              *)
  | TGroupClose                                 (* "}"              *)
  | TEOF                                         (* virtual sentinel *)

(* Metadata wrapper used by L1+ *)
type token_with_meta = { tok : token; loc : Location.t; cat : Catcode.t }

val equal : token -> token -> bool
val printable : token -> string     (* debug pretty-printer *)

Memory Footprint:

Variant	Bytes (x86‑64)	Bytes (arm64)
TChar	24	24
TMacro	24	24
TParam	16	16
TGroup*	8	8
TEOF	8	8
Average (thesis corpus)	17.3	17.3

Proofs. TokenEq.v shows equal ↔ Leibniz equality.

⸻

B‑1‑3 Delta Types (cross‑layer)

type token_delta =
  | ReplaceSlice of { start_idx : int; end_idx : int; with_ : t array }
  | NoChange

type parser_delta =
  | ReplaceSubtree of { path : int list; with_ : Ast.block list }
  | NoAstChange

type sem_delta =
  | Patch of Sem_state.patch   (* diff‑algebra element *)
  | NoSemChange

⸻

B‑2 Layer 0 — Incremental Lexer (layer0_lexer.mli)

open Data

type state = {
  cat_table   : Catcode.t array;  (** immutable snapshot *)
  line_no     : int;
  in_math     : bool;
  pending_bom : bool;
}

type edit =
  | Insert of { offset : int; bytes : bytes }
  | Delete of { offset : int; length : int }

val lex :
     prev_tokens : Token.t array
  -> prev_state  : state
  -> edit list
  -> Token.t array        (** updated stream  *)
  *  state                (** updated lexer state *)
  *  token_delta          (** compressed diff  *)

Complexities. O(edit_size + Δ_tokens) time, independent of whole document length.
Proof hooks — exports lemma lexer_locality : ….

⸻

B‑3 Layer 1 — Macro Expander (layer1_expander.mli)

type macro_def =
  | Simple    of Token.t list
  | Param     of { params : int; body : Token.t list }
  | LongParam of { params : int; body : Token.t list }

type env = private { defs : (string, macro_def) Hashtbl.t }

type expander_state = {
  env       : env;
  fuel_left : int;
}

val default_fuel : int

val expand :
     prev_tokens : Token.t array
  -> token_delta : token_delta
  -> prev_state  : expander_state
  -> Token.t array * expander_state * token_delta

Fuel bound. default_fuel = 4 × doc_tokens.
Cache. internal LRU 4096 keyed by (macro_hash, cat_hash).
Proofs — Expand.v supplies:
	•	expand_no_teof
	•	expand_terminates_acyclic
	•	expand_fuel_insensitive
	•	expand_fuel_monotonic

—all Qed.

⸻

B‑4 Layer 2 — Incremental PEG Parser (layer2_parser.mli)

val parse :
     prev_tokens : Token.t array
  -> token_delta : token_delta
  -> prev_ast    : Ast.document
  -> Ast.document * parser_delta

Grammar origin. grammar/Latex25.peg → Menhir‑cert code‑gen.
Window size. Parser re‑parses ≤ 4 000 tokens.
Proofs — ParserSound.v, SpliceEquiv.v.

⸻

B‑4‑1 data/ast.ml (excerpt)

type inline =
  | PlainText   of string
  | InlineMath  of math_ast
  | Command     of { name : string; args : inline list }
  | Verbatim    of string

type block =
  | Paragraph     of inline list
  | Environment   of { name : string; options : inline list option; body : block list }
  | Equation      of math_ast * label option
  | DisplayMath   of math_ast

type document = block list

Invariants. WellTyped ast proven by parser.

⸻

B‑5 Layer 3 — Semantic Interpreter (layer3_interpreter.mli)

type t = Sem_state.t   (* alias *)

val interpret :
     prev_ast     : Ast.document
  -> parser_delta : parser_delta
  -> prev_sem     : t
  -> t * sem_delta

Reducer signature. foldM : t -> Ast.node -> t.
Proof interp_locality ensures delta correctness.

⸻

B‑6 Layer 4 — Styler & NLP (layer4_styler.mli)

val style :
     sem_delta       : sem_delta
  -> style_blocks    : Style_block.t array
  -> validator_issue list * Style_block.t array

Guarantees. No modification outside supplied blocks; passive detectors only (no AST mutation).

⸻

B‑7 Elder Orchestrator (elder_orchestrator.mli)

type session

val open_doc  : bytes -> session
val apply_edit : session -> Layer0.edit list -> validator_issue list
val save_doc  : session -> unit
val close_doc : session -> unit

Internals — maintains five Elder Boxes, EDF scheduler, telemetry hooks.

⸻

B‑8 Validator Runtime (validator.mli)

module type S = sig
  val id        : string
  val layer     : Layer_id.t
  val severity  : Severity.t
  val check     : LayerArtefact.t -> Issue.t list
  val apply_fix : ?limit:int -> bytes -> Issue.t -> bytes option
end

Dynamically loaded via Registry (dune virtual_library).

⸻

B‑9 Cross‑Layer Delta‑Flow Summary

Producer → Consumer	Delta Type	Data Carried
Lexer (L0) → Expander (L1)	token_delta	slice replacement
Expander → Parser	token_delta	idem
Parser → Interpreter	parser_delta	AST subtree splice
Interpreter → Styler	sem_delta	counters/label diff
Styler → Front‑end	issue_delta	added/removed diagnostics

All deltas implement val serialize : t -> bytes.

⸻

B‑10 Performance Contracts (p99 targets, M2 Max single‑core)

Layer	Max Latency	Peak RSS	Comments
L0	80 µs / 4 KiB edit	16 MiB	SIMD xxHash + FSM lexer
L1	200 µs	64 MiB	Fuel‑bounded, DAG cache
L2	300 µs	24 MiB	Window re‑parse
L3	250 µs	32 MiB	Finger‑tree maps
L4	120 µs / paragraph	12 MiB	spaCy in‑proc, memoised
Elder dispatch	≤ 40 µs	—	Dispatch, telemetry
Elder total	≤ 1 ms	4 MiB overhead	End‑to‑end budget

⸻

B‑11 Module Dependency Graph

token ─▶ layer0 ─▶ layer1 ─▶ layer2 ─▶ layer3 ─▶ layer4
 ▲        ▲          │          │          │
 │        └──────────┴──────────┴──────────┘
 └──────────── data/location

No cycles; every .ml depends on .mli of lower tier only.

⸻

B‑12 Formal Proof Obligations Matrix (excerpt)

File	LOC	Lemmas	Status
Lexer.v	2 304	19	✔ zero admit
Expand.v	3 122	24	✔
ParserSound.v	1 810	9	✔
SpliceEquiv.v	480	3	✔
Semantics.v	1 204	7	✔
StyleDet.v	228	2	✔

All certificates re‑checked nightly by proof farm.

⸻

End of Appendix B.

⸻

Appendix C — Validator‑DSL Specification & Generator Architecture

(canonical spec — revision 2025‑07‑31, merges all clarifications, resolves 87 Q & follow‑up doubts)

⸻

C‑0 Purpose & High‑Level Overview

The Validator‑DSL (VDL) is a strictly typed, YAML‑front‑matter + body language that lets rule authors describe 623 validators once and obtain automatically:
	•	an OCaml detector (rules/ID.ml, compiles into the runtime plugin);
	•	an optional OCaml fixer (same module, if fix: ≠ null);
	•	a Coq proof stub (proofs/rules/ID.v) that is fully proved automatically via family‑level lemma templates (§C‑7);
	•	a JSON manifest consumed by the documentation site & VS Code extension.

Architecture pipeline:

.vdl            (rules_src/)
   │  parse                                   ┌─────────────┐
   ├────────────┐                             │ Proof Farm  │
   ▼            ▼                             └─────▲───────┘
Front‑matter  Body ──► IR (ValidatorCore.t) ──► Code‑gen ──►    *.ml / *.v / *.json
                                          (OCaml + Coq  )      (build/generated/)

⸻

C‑1 File‑Level Syntax

A validator file ID.vdl begins with YAML 1.2 front‑matter terminated by ---, followed by a body whose syntax depends on pattern:.

id: "TYPO-001"               # UNIQUE, UPPER‑SNAKE + numeric suffix
family: "TYPO"               # grouping key
title: "Replace straight quotes with curly"
severity: "Warning"          # Error | Warning | Info
layer: "L1_Expanded"         # Where the rule runs
pattern: "regex"             # regex | token | dsl
fix: "auto_replace"          # built‑in, custom OCaml, or null
tags: ["quotes", "english"]
examples:
  - input: "\"hello\""
    output:
      - id: "TYPO-001@[0,7]"
    fixed: "“hello”"
---
/"([^"]+)"/

⸻

C‑2 Front‑Matter Keys (complete)

Key	Type	Req’d	Notes
id	string (regex ^[A-Z]+-[0-9]{3}$)	✔	Must be globally unique
family	string	✔	Determines proof template & plugin bucket
title / description	string	✔ / opt	Title ≤ 72 chars
severity	Error | Warning | Info	✔	Maps to LSP DiagnosticSeverity
layer	see enum §C‑2.1	✔	Compile‑time check vs runtime artefact
pattern	regex | token | dsl	✔	Selects body dialect
fix	null | built‑in id | OCaml block	✔	Must type‑check if present
tags	string list	opt	≤ 8 tags, lower_snake
examples	list	opt	Triples {input; output; fixed?}

C‑2.1 layer enum

Layer tag	Runs on artefact	Allowed delta source
L0_Raw	raw bytes slice	initial load
L0_Lexer	token array	lexer delta
L1_Expanded	expanded token array	expander delta
L2_AST	AST subtree	parser delta
L3_Semantic	semantic delta	interpreter delta
L4_StyleBlock	style block	styler delta

⸻

C‑3 Body Dialects

C‑3.1 Regex dialect

Delimiter /…/ or «…».
Engine RE2 (subset of PCRE, guaranteed linear).
Flags i (ignore case), m (multi‑line) via trailing ;i.
Named groups propagate to fix replacements.

Example:

/(?P<open>("|“|«))(?P<text>[^"]+)(?P<close>("|”|»))/;i

C‑3.2 Token‑sequence dialect

TOKENSEQ
  TChar "\""           (* literal " token *)
  PlainText  "[^"]+"   (* regex on token.text *)
  TChar "\""
END

Grammar

sequence   ::= line+
line       ::= Constructor Literal? Regex?
Constructor ::= TChar | TMacro | TGroupOpen | ...
Literal    ::= STRING   (* OCaml lex string literal *)
Regex      ::= /.../

_ wildcard and {m,n} repetition allowed.

C‑3.3 Structural DSL dialect

OCaml‑like pattern matcher embedded via ppx_vdl_dsl.

Example:

DSL
match block::Paragraph(inlines) with
| _ when sentence_length inlines > 40 ->
    issue ~loc:(loc_of inlines) "STYLE-017" "Sentence too long"
end

The DSL compiles to a first‑class OCaml detector; static analysis ensures termination.

⸻

C‑4 Intermediate Representation — ValidatorCore.t

type layer = L0_Raw | L0_Lexer | L1_Expanded | L2_AST | L3_Semantic | L4_StyleBlock

type pattern =
  | Regex    of { re : string }
  | TokenSeq of token_expr list
  | DSL      of string              (* α‑renamed, type‑checked OCaml *)

type fix =
  | None
  | Builtin of builtin
  | CustomOCaml of string           (* expression : bytes -> Issue.t -> bytes option *)

type t = {
  id          : string;
  family      : string;
  severity    : Severity.t;
  layer       : layer;
  pattern     : pattern;
  fix         : fix;
  tags        : string list;
  title       : string;
  description : string option;
  examples    : example list;
}

⸻

C‑5 Code‑Generation

File layout (auto‑generated)

_build/generated/
 ├─ rules/
 │   └─ FAMILY/
 │       ├─ ID.ml
 │       └─ ID.dune        (library variant stanza)
 ├─ proofs/rules/
 │   └─ ID.v
 └─ manifest/
     └─ ID.json

C‑5.1 OCaml detector skeleton

open Validator_runtime

module V : Validator.S = struct
  let id = "TYPO-001"
  let layer = L1_Expanded
  let severity = Warning

  (* ==== detector === *)
  let detector =
    let open PatternCombinators in
    seq (re "\"") (re "[^\"]+") |> seq (re "\"")
    |> report ~mk_issue:(fun loc -> Issue.make ~id ~loc)

  let check artefact =
    ArtefactTok.pattern_scan detector artefact

  (* ==== fixer === *)
  let apply_fix ?limit ~doc_bytes issue =
    Fix_builtin.auto_replace
      ~search:"\"([^\"]+)\"" ~template:"“$1”"
      ?limit ~doc_bytes issue
end

let () = Registry.register (module V)

All generated code is compiled with -w +a-32-40-41-42-48.

C‑5.2 Coq proof stub template

Require Import ValidatorCore RegexProofs.

Module TYPO_001.

Definition re := «"([^"]+)"».

Lemma sound : regex_sound re.
Proof. apply regex_generic_sound. Qed.

Lemma fix_preserves :
  fixer_preserves_semantics
    (Fix_builtin.auto_replace "\"" "“" "”") re.
Proof. solve_auto_replace. Qed.

End TYPO_001.

Family‑level tactics (RegexProofs.v) discharge both lemmas automatically; CI fails if Qed. is replaced by admit.

⸻

C‑6 Built‑in Fixers (complete list)

Name	Captures	Behaviour	Proof Template
auto_replace	$0 or named groups	single regex substitution	fix_auto_replace_sound
insert_nbsp	$pos offset	inserts U+00A0 before span	fix_nbsp_sound
wrap_braces	span	{ … } wrapping	fix_wrap_sound
collapse_spaces	span	replace  + → “ “	fix_ws_collapse_sound

All built‑ins proven fixer_preserves_semantics.

⸻

C‑7 Proof Automation Library (families)

Family	Count	Proof template	Complexity
TYPO (ASCII/quotes/spaces)	260	regex_generic_sound, fix_auto_replace_sound	O(n)
SPC (spacing)	46	regex_ws_sound	O(n)
MATH (math grammar)	133	tok_seq_math_sound, uses Menhir‑cert CFG	O(n)
STRUCT	95	ast_pred_sound via structural induction	O(nodes)
SEM	66	sem_invariant_sound	O(Δ)
LANG (CJK/RTL)	23	lang_regex_sound, locale_fix_sound	O(n)

Generation pipeline selects template by family.

⸻

C‑8 Generator CLI (generate_validators.exe)

Flag	Purpose
–src-dir DIR	root of .vdl files
–out-dir DIR	where to emit generated artefacts
–check-only	parse & type‑check, no code‑gen
–families F1,F2	restrict generation
–threads N	parallelism for proof pre‑check

dune runtest invokes the generator in check‑only mode to enforce schema correctness before proofs build.

⸻

C‑9 Error Codes

Code	Message	Typical Fix
E001	Duplicate id	rename file/id
E011	Unknown front‑matter key	prefix with _comment: or remove
E101	Regex parse error	escape metacharacters
E201	Unknown token constructor	sync with token.ml
E401	Fixer references undefined capture	add capture or rename

All generator diagnostics include file:line:col snippet.

⸻

C‑10 Validator‑Life‑Cycle Diagram

author.vdl
   └─▶ generator check‑only  (CI Stage 1)
           │
           ▼
     *.ml / *.v emitted
           │
           ▼
     dune build rules/      (CI Stage 2)
           │                 ├─ proof farm (@coq)
           │                 └─ ocamlopt compile
           ▼
   plugin *.cmxs + .vo
           │
           ▼
   integration tests        (CI Stage 3)

A PR merges only when all three stages are green.

⸻

End of Appendix C.

⸻

# Appendix D — Proof Template Catalogue (v25)

**Status:** Authoritative for v25.  
**Scope:** Generic, reusable Coq proof templates and instantiation guidance that cover the validator families and phases defined in `rules.yaml` (623 rules across TYPO/SPC/ENC/… families). The catalogue maps each rule *precondition* (L0–L4) to a small set of canonical obligation shapes and automation tactics.

---

## D.1 Goals and non‑goals

**Goals**

1. Provide *template‑level* proof obligations that can be reused across hundreds of validators with identical structure.
2. Guarantee **determinism**, **totality on well‑formed inputs**, and **no‑panic** properties for all rule runners.
3. Prove **semantic preservation** for “normalisation” fixes (e.g., NFC normalisation, whitespace collapse) and **soundness**/**completeness** bounds for detection‑only rules where applicable.
4. Encode **idempotence** of auto‑fixers and **commutativity** for disjoint fixes to enable safe bulk rewriting.

**Non‑goals**

- We do not attempt layout optimality proofs (e.g., “minimal raggedness”); those are style policies proved at L4 under weaker obligations.
- We do not prove external tool conformance (e.g., font embedding by a third‑party PDF engine). Those are checked via metadata rules and reproducibility constraints.

---

## D.2 Notation and conventions

- `Σ` — global configuration (engine branch, language code, rule severity thresholds).
- `doc` — input document as a rope/rope‑like structure; `ast` — expanded AST after L1/L2.
- `run r x` — evaluation of rule `r` on input `x` returning `Result` with optional fix.
- `⟦x⟧` — semantics of `x` (e.g., rendered textual stream at the layer boundary).
- `apply_fix x f` — deterministic application of fix `f` to container `x`.
- `wf_Lk(x)` — well‑formedness predicate for layer `k` (k ∈ {0,1,2,3,4}).

We write Coq in lightweight style, omitting module qualifiers for readability.

---

## D.3 Template index (by precondition)

| Precondition | Template ID | Shape | Typical families |
|---|---|---|---|
| `L0_Lexer` | `T.lex.safety` | totality + no‑panic + locality | `TYPO`, `SPC`, `ENC`, `CHAR`, `VERB` |
| `L1_Expanded` | `T.exp.determinism` | determinism under expansion | `MATH`, `SCRIPT`, `DELIM` |
| `L2_Ast` | `T.ast.ref-int` | reference integrity + structure | `REF`, `TAB`, `FIG`, `PKG`, `DOC` |
| `L3_Semantics` | `T.sem.preservation` | semantics‑preservation of fixes | `LAY`, `PDF`, `COL`, `FONT`, `BIB` |
| `L4_Style` | `T.style.policy` | policy compliance & monotonic scoring | `STYLE`, `LANG`, `CJK` |

> Coverage targets mirror the 623 rules enumerated in `rules.yaml`; any new family must bind to one of these shapes or introduce a new template with proofs at the same granularity. 

---

## D.4 Core templates

### D.4.1 `T.lex.safety` — Lexical runner safety and locality (L0)

**Obligations**

1. **Totality:** `∀ doc. wf_L0(doc) → ∃ res. run r doc = res`  
2. **No‑panic:** `run r doc` never raises exceptions; failures are `Error e` values.  
3. **Locality:** fixes only touch a bounded window around matched span.  
4. **Idempotence (fixers):** if `run r doc = Ok (Fix f)`, then `apply_fix doc f = doc'` and `run r doc' = Ok (Noop)`.

**Sketch (Coq)**

```coq
Record L0_result := { out : doc; delta : delta_out; err : option error }.

Theorem T_lex_total :
  forall r doc,
    wf_L0 doc -> exists res, eval_L0 r doc = res.
Theorem T_lex_no_panic :
  forall r doc, wf_L0 doc -> ~ raises (eval_L0 r doc).
Theorem T_lex_local :
  forall r doc f,
    eval_L0 r doc = Ok (Fix f) -> bounded_span f.span MAX_LEX_WIN.
Theorem T_lex_idem :
  forall r doc f,
    eval_L0 r doc = Ok (Fix f) -> eval_L0 r (apply_fix doc f) = Ok Noop.
```

**Instantiation examples**

- `TYPO-001` ASCII straight quotes → curly quotes (`auto_replace`). Local window = 1–2 glyphs; semantics preserved in L3 sense (see D.4.4).  
- `SPC-007` collapse ≥3 blank lines → 1; idempotent by construction.  
- `ENC-010` NFC normalisation → see D.4.4 for preservation proof obligations.

---

### D.4.2 `T.exp.determinism` — Post‑expansion determinism (L1)

**Obligations**

1. **Context‑determinism:** Expanded stream `E(doc)` is deterministic given `Σ`.  
2. **Rule determinism:** For a fixed `E(doc)`, `run r` yields a unique `res`.  
3. **Expansion‑monotonicity:** A fix at L1 does not introduce new unmatched delimiters or change expansion fuel monotonicity.

**Sketch**

```coq
Hypothesis expand_det : forall doc, E doc = E' doc.
Theorem T_exp_det :
  forall r doc, deterministic (fun d => run r (E d)).
```

Typical families: `MATH-0xx` (operator names, spacing), `DELIM-00x` (paired delimiters).

---

### D.4.3 `T.ast.ref-int` — AST structure and reference integrity (L2)

**Obligations**

- **Well‑formedness:** produced AST satisfies grammar invariants.  
- **Ref‑integrity:** any `\ref{l}` / `\eqref{l}` references a defined label and correct environment.  
- **Package order invariants:** specific orderings (`geometry` before `hyperref`).

**Sketch**

```coq
Inductive LabelEnv := Env (defs : set label).
Theorem T_ref_defined :
  forall ast l, In (Ref l) ast -> defined l ast.
Theorem T_pkg_order :
  forall ast, order_ok ast ["geometry"; "hyperref"].
```

Families: `REF-001..012`, `PKG-00x`, `TAB-00x`, `FIG-00x`, `DOC-00x`.

---

### D.4.4 `T.sem.preservation` — Semantics‑preserving normalisations (L3)

**Goal**: Applying a fix does not alter rendered meaning at the boundary (`⟦·⟧`).

**Obligations**

- **NFC/NFKC policy:** Our normaliser uses **NFC** in text and **no normalisation** inside code/verbatim/math except where explicitly safe; `⟦doc⟧ = ⟦normalize_nfc(doc)⟧`.  
- **Whitespace policy:** Collapsing sequences that do not render visibly (outside verbatim) keeps `⟦·⟧`.  
- **Typography fixes:** “—” vs “---” mapping preserves rendered dash at output.  

**Sketch**

```coq
Theorem T_sem_nfc :
  forall doc, wf_L3 doc -> render (normalize_nfc doc) = render doc.
Theorem T_sem_ws :
  forall doc, context_nonverbatim doc -> render (collapse_ws doc) = render doc.
```

Families: `ENC-010`, `SPC-0xx` (non‑verbatim), `TYPO-002/003`, `MATH-079/105` (redundant displaystyle), etc.

---

### D.4.5 `T.style.policy` — Style policy compliance (L4)

**Obligations**

- **Monotonicity:** style score is non‑decreasing under compliant fixes.  
- **Locality of judgement:** only local n‑gram/AST context affects a given style flag unless rule is explicitly document‑wide.  
- **No false *errors*:** style rules may emit `Info/Warning`, but `Error` at L4 is reserved for structural violations proven at L2/L3.

**Sketch**

```coq
Theorem T_style_mono :
  forall doc f, style_score (apply_fix doc f) >= style_score doc.
```

Families: `STYLE-0xx`, `LANG-0xx`, CJK/RTL pedantics.

---

## D.5 Instantiation guide (selected)

### D.5.1 `TYPO-001` Curly quotes

- **Precondition:** `L0_Lexer` → use `T.lex.safety` + `T.sem.preservation`.  
- **Fix:** local replacement `"..."` → `“…”`.  
- **Proof:** locality bound 1; idempotence by char‑class predicate; semantics preserved as renderer maps both to identical glyph in final PDF under configured font set.

### D.5.2 `PKG-002` geometry before hyperref

- **Precondition:** `L2_Ast` → use `T.ast.ref-int`.  
- **Obligation:** `order_ok ast ["geometry"; "hyperref"]`.  
- **Auto‑fix:** reorder preamble nodes; **Proof:** AST equivalence modulo commutative package order (proof via permutation lemma).

### D.5.3 `MATH-012` operatorname for multi‑letter functions

- **Precondition:** `L1_Expanded` → `T.exp.determinism`.  
- **Fix:** wrap `foo(x)` → `\operatorname{foo}(x)`.  
- **Proof:** expansion determinism ensures identical token boundaries; semantics preserved under math typesetting model equivalence.

---

## D.6 Automation

The **`auto_solver_tactic`** dispatches by rule metadata:

```coq
Ltac auto_solver :=
  match goal with
  | |- context [wf_L0 _] => eapply T_lex_total; eauto
  | |- context [order_ok _ _] => eapply T_pkg_order; eauto
  | |- context [render _ = render _] => eapply T_sem_nfc || eapply T_sem_ws; eauto
  | _ => eauto with core
  end.
```

Manifest fields (`id`, `phase`, `provides`, `requires`, `conflicts`) feed the dispatcher and select the appropriate template obligations.

---

## D.7 Coverage matrix (abbrev.)

- **Lexical families:** `TYPO‑001…063`, `SPC‑001…035`, `ENC‑001…024`, `CHAR‑005…022`, `VERB‑001…017`.  
- **Post‑expansion:** `MATH‑009…108`, `DELIM‑001…011`, `SCRIPT‑001…022`.  
- **AST/Structure:** `REF‑001…012`, `PKG‑001…025`, `TAB‑001…016`, `FIG‑001…025`, `DOC‑001…005`.  
- **Semantics/Layout:** `LAY‑001…024`, `PDF‑005…012`, `COL‑001…007`, `FONT‑001…013`, `BIB‑001…017`.  
- **Style/Locale:** `STYLE‑001…049`, `LANG‑001…016`, `RTL‑001…005`, `CJK‑001…016`, + regional series.

Each block binds to one core template per §D.4, with family‑specific lemmas for boundary cases (e.g., verbatim/math contexts).

---

## D.8 Developer checklist

1. Declare rule in DSL with `precondition`, `severity`, `fix` shape.  
2. Pick template(s) from §D.4; generate stub proofs.  
3. Add manifest metadata for dispatcher.  
4. Run `proof‑ci`; resolve any `@proof‑debt` tags before merge.  
5. Add regression to appropriate corpus bucket; re‑run perf smoke to confirm p95 budget intact.

---

## D.9 Known gaps

- PDF accessibility proofs remain *checks*, not semantic proofs.  
- TikZ compilation time bounds are empirical, documented via CI artefacts.  
- Full Unicode equivalence beyond NFC is purposely **out of scope** for v25; see Appendix F for policy.

---

# Appendix E — SIMD Implementation Notes (v25)

**Status:** Engineering guidance for the optional Rust SIMD kernels with OCaml FFI bindings.  
**Objective:** Keep **perf_smoke** p95 under 25 ms (full doc) and 1 ms (4 KiB edit window), with portable fallbacks and strict correctness parity. See performance targets in the master plan. 

---

## E.1 Where SIMD is used

1. **Byte‑class scanners:** classify ASCII vs non‑ASCII, punctuation, quotes, dashes, math delimiters.  
2. **UTF‑8 validators:** fast path for well‑formed ASCII/UTF‑8; precise slow path for rare errors.  
3. **Multi‑pattern `memchr`‑style probes:** locate any of a small set (e.g., `~`, `%`, `&`, `<`, `>`).  
4. **Whitespace and NBSP sweeps:** detect collapsible runs outside verbatim/math.  
5. **Delimiter balance pre‑scan:** quick reject for obviously unbalanced `{}`, `\left...\right`.

---

## E.2 Memory layout

- **SoA, 64‑byte aligned** slabs for scanning; fall back to AoS for short tails.  
- **Pinned Bigarray** buffers on the OCaml side; Rust borrows as `&[u8]` with `repr(transparent)` shim.  
- **No uninitialised reads:** loads are masked on tails with `k` masks (AVX‑512) or lane‑safe blends (AVX2/NEON).

```rust
#[inline]
fn load_masked_32(ptr: *const u8, len: usize) -> __m256i { /* tail-safe */ }
```

---

## E.3 Feature detection and dispatch

- x86: `std::is_x86_feature_detected!("avx512bw")` → AVX‑512; else `"avx2"` → AVX2; else scalar.  
- AArch64: compile‑time NEON; runtime CPU info gate on OSs that expose it.  
- Dispatch table set **once** at startup; hot loops avoid indirect branches.

---

## E.4 Kernels

### E.4.1 ASCII & class masks

- Precompute lane masks for `["\"", "'", "-", "~", "&", "%", "<", ">", "`]`.  
- Use saturated add/sub to combine class hits; emit bitfields per 32/64 bytes.  
- **Correctness:** masks are advisory; the OCaml validator re‑checks around hits before fixing.

### E.4.2 UTF‑8 fast‑path

- Recognise runs of `x < 0x80` quickly; for non‑ASCII, delegate to a scalar DFA that rejects overlongs, lone continuation bytes, or illegal ranges.  
- **Guarantee:** exact parity with scalar path; failures return precise indices for the Coq proof obligations (§D.4.1 “no‑panic”).

### E.4.3 NBSP and invisible characters

- Vector compare against `0xA0`, `U+2009`, `U+200B`, `U+FEFF` using pre‑expanded UTF‑8 byte sequences; report spans for collapse/removal candidates.  
- **Policy hooks:** Appendix F governs where actions are permitted.

### E.4.4 Multi‑pattern `memchr`

- Use `vpcmpeqb`/`vcmeq` patterns to test N characters at once; OR lanes to form the hit mask; `tzcnt/ctz` find first set bit; iterate.  
- Up to ~5× over scalar on large buffers; gracefully falls back below ~256 B.

---

## E.5 OCaml FFI boundary

- Bindings via **OCaml Ctypes**; pass Bigarray `Array1<u8>` slices with explicit length.  
- **Safety:** no aliasing writes; **zero‑alloc** in hot path; return small `struct { mask, count }` on stack.  
- **Proof notes:** FFI functions are *pure* w.r.t. inputs; we model them axiom‑free by giving a scalar reference implementation and proving bit‑for‑bit equivalence tests in Coq for selected kernels.

---

## E.6 Determinism and parity

- Each SIMD kernel ships with a portable scalar mirror. CI runs *differential tests* across corpora; any divergence fails the zero‑admit gate.  
- Endianness is accounted for (lane order does not leak into semantic decisions).

---

## E.7 Benchmark methodology

- **Harness:** run 100 iterations, drop top/bottom 5, report median and p95.  
- **Targets:** edit window 4 KiB ≤ 1 ms; full document 1.1 MiB ≤ 25 ms.  
- **Hardware baseline:** M2‑Pro 3.5 GHz, 32 GiB RAM (recorded in CI).

---

## E.8 Build & CI

- Cargo features: `simd_avx512`, `simd_avx2`, `simd_neon`, `portable`.  
- Fallback selection in `build.rs`; runtime verification on first call to catch container mis‑configs.  
- CI matrix builds all variants and runs the perf‑smoke job with gate `p95 ≤ SLA`.

---

## E.9 Portability notes

- AVX‑512 may down‑clock on some Intel SKUs; gate with env override.  
- On Windows, enable `/arch:AVX2`; verify that Rust target features propagate when building via opam/dune.

---

## E.10 Micro‑optimisations (checked in perf harness)

- Avoid partial‑register stalls on x86; keep values in XMM/YMM/ZMM.  
- Hoist loop‑invariant table lookups; ensure pointer chasing remains in L1.  
- Keep branches predictable: treat “hit” as the **cold** path for common scans.

---

# Appendix F — Internationalisation & Unicode Strategy (v25)

**Status:** Authoritative policy for text handling, normalisation, bidi, and locale‑specific linting.  
**Design intent:** Achieve broad language coverage with *param‑by‑language‑code* behaviour while keeping the core deterministic and fast.

---

## F.1 Principles

1. **Predictability first:** We prefer NFC normalisation and explicit macros to ambiguous look‑alikes.  
2. **Context matters:** Verbatim/math/code are **sanctuaries**—no normalisation or spacing fixes inside.  
3. **Local policy knobs:** Language‑code parameters (`en-US`, `fr-BE`, `ja`, `ar`) toggle locale rules and spacing policies.  
4. **Proof‑friendly:** Every normalisation rule has a semantics‑preservation lemma or is marked *non‑semantic* (style‑only).

---

## F.2 Normalisation policy

- **Default:** NFC on text segments; do **not** apply NFKC globally.  
- **Exceptions:** Inside `verbatim`, `lstlisting`, `minted`, and math, skip normalisation; only validate encoding.  
- **Homoglyph policing:** Detect risky codepoints (Greek mu `μ` vs micro `µ`), suggest safe replacements; never auto‑replace in code blocks.

**Rationale:** NFC preserves grapheme equivalence without dropping distinctions that matter in identifiers.

---

## F.3 Grapheme segmentation

- Use Unicode grapheme break algorithm with tailorings for known TeX macro boundaries.  
- Grapheme‑aware operations prevent split‑accent errors in languages using combining marks.

---

## F.4 Bidirectional text

- Enforce isolation marks where LTR acronyms appear in RTL runs and vice‑versa; provide `\textLR`/`\textRL` helpers.  
- Reject stray embeddings (U+202A–U+202E) outside explicit bidi contexts.

---

## F.5 Locale‑specific spacing & punctuation

Examples (non‑exhaustive):

- **French:** NBSP before `; : ! ?`; thin NBSP around `€`.  
- **Russian:** NBSP before em‑dash.  
- **Polish:** NBSP before `r.` `nr` `s.` abbreviations.  
- **Czech/Slovak:** No thin space before `°C`.  
- **Dutch:** `IJ/ij` digraph capitalisation at sentence start.  
- **Chinese/Japanese:** Full‑width punctuation in CJK runs; avoid Western space between CJK glyphs.

Each rule is surfaced as a locale‑aware validator with layer‑appropriate preconditions (L0 vs L4).

---

## F.6 Script modules

- **Latin/Cyrillic/Greek:** normalise quotes; enforce language‑consistent spellings.  
- **Arabic/Hebrew (RTL):** ensure digit direction and quotation marks are mirrored correctly; require RTL fonts configured.  
- **Indic scripts:** flag ZWJ/ZWNJ misuse near conjuncts (policy only).  
- **CJK:** xeCJK presence, spaceskip tuning, and kinsoku shori checks; keep code pages coherent per document.

---

## F.7 Units, numbers, and math

- Thin space before units (`5 cm`), \\, before differentials, and proper decimal/thousand separators per locale (e.g., `pt‑BR`).  
- In math, prefer operators/macros over Unicode symbols; preserve semantics.

---

## F.8 Libraries and implementation notes

- Core Unicode: implemented with **pure OCaml** data tables (no OS ICU dependency) for determinism.  
- Grapheme breaks and normalisation: pre‑generated tables pinned in the repository for reproducibility.  
- CJK width and bidi mirrors: compact bitsets with O(1) probes.

---

## F.9 Configuration

- User sets `lang = <BCP‑47>` in the manifest; defaults to document language or `en`.  
- Per‑rule overrides allowed (e.g., disable `STYLE-015` “double space” for legacy corpora).

---

## F.10 Testing and coverage

- Locale goldens per language with both **positive** and **negative** cases.  
- CI fairness queue: ensure no locale family is left untested in a release block.

---

## F.11 Edge cases

- Mixed RTL numbers inside LTR equation references.  
- Non‑breaking hyphen in URLs: allowed inside `\url{}` but not in plain text.  
- French guillemets inside code comments: ignored by design.

---

## F.12 Glossary (selected)

- **NFC/NFKC:** Canonical vs compatibility normalisation.  
- **Kinsoku shori:** Japanese typesetting line‑break prohibition rules.  
- **Bidi isolate:** Unicode isolates that limit directionality scope.

---

# Appendix G — ML‑Assisted Pattern Pipeline & Extended Glossary (v25)

**Status:** Optional, *offline* assistance for discovering new lint patterns; **never** bypasses the proof‑first gate.  
**Design:** Human‑in‑the‑loop pipeline that proposes candidates from corpora; all merges remain rule‑/proof‑driven.

---

## G.1 Why ML here?

- Some style or locale patterns are hard to enumerate by hand (e.g., journal‑specific quirks).  
- We use small, reproducible models to *propose* rules; validators stay deterministic and formally covered by templates in Appendix D.

---

## G.2 Data sources

- **Corpora buckets:** minimal, standard, categories, perf_smoke.  
- **Signals:** token sequences, AST shapes, compile logs (over/underfull boxes), and rule fire statistics.

---

## G.3 Feature extraction

- **Character n‑grams** with Unicode class features.  
- **AST contexts** (e.g., macro before/after, environment type).  
- **Layout signals** (e.g., float distance, line lengths).

---

## G.4 Modelling

- **Lightweight baselines:** logistic regression / gradient‑boosted trees; calibrated probabilities.  
- **Constraints:** no external network calls; seeded randomness; deterministic training artefacts stored with SBOM metadata.  
- **Output:** candidate `(pattern, precondition, fix?)` with confidence intervals.

---

## G.5 Distant supervision

- Use existing rule fires as weak labels; mine **near‑misses** to uncover new variants (e.g., Unicode look‑alikes).  
- Negative sampling from clean regions of the corpora.

---

## G.6 Ranking and review

- Rank by *lift* over current rules and *disjointness* from existing patterns.  
- Review checklist ensures: locality, semantics‑preservation (if fixer), performance cost within budget.

---

## G.7 Emission to DSL and proofs

- Emit minimal DSL stubs with `id`, `phase`, `provides/requires/conflicts`.  
- Associate a template from Appendix D; generate proof skeletons; open a proof‑farm task.  
- **CI gate:** no candidate ships unless proofs close or are tracked under capped `@proof‑debt` with deadline.

---

## G.8 Telemetry & observability

- Track precision/recall against reviewer decisions.  
- Expose dashboards via OpenTelemetry → Grafana; publish weekly reports for acceptance rate and false‑positive analysis.

---

## G.9 Risk, fairness, and privacy

- **Fairness:** ensure non‑English corpora drive candidate discovery proportionally; hold‑out per language to detect drift.  
- **Privacy:** no user‑private documents; only opt‑in corpora.  
- **Reproducibility:** dataset fingerprints and exact training configs are recorded; builds are hermetic.

---

## G.10 Extended glossary (selected)

- **Candidate pattern:** A machine‑suggested, human‑verified lint.  
- **Disjointness:** Degree to which a pattern flags issues not already caught by existing rules.  
- **Lift:** Improvement in detection rate over baseline with bounded false positives.  
- **Proof debt:** Temporarily allowed proof gap with deadline and CI tracking.  
- **Semantic preservation:** Applying a fixer keeps output meaning unchanged (Appendix D).

---

## G.11 Roadmap

- **v25:** baseline pipeline, reviewer tooling, and dashboards.  
- **v26:** cross‑language transfer learning with per‑script adapters.  
- **v27:** limited structure‑aware models for complex math spacing suggestions (still proof‑gated).

⸻

Appendix H — Advanced Proof‑Automation Cookbook

revision 2025‑07‑31 — synchronised with tactic bundles shipped in proofs/Automation/

Purpose. Guarantee that the 623 validators, the incremental L0–L4 proofs, and the scheduler feasibility proofs can be maintained with < 0.5 person‑day/month. This appendix documents every reusable lemma, tactic, and generator hook that keeps the zero‑admit target sustainable.

⸻

H‑0 Scope & Terminology

Term	Meaning
Obligation	A (soundness, completeness, fix‑preservation, performance) theorem each validator must satisfy.
Strategy	Named proof pattern (e.g., WS_SAFE, REGEX_ASCII).
Sketch	Auto‑generated .v file containing Proof. <tactic>. Qed. only.
Core Lemma	Library lemma proven once and used by ≥ 10 validators.
Kernel Tactic	Ltac2 / ELPI code that closes a class of goals in < 20 ms.


⸻

H‑1 Obligation Matrix

Obligation ID	Trigger (validator/family)	Formal statement (summary)	Typical tactic
WS_SAFE	Fix inserts/removes ASCII space / Tab / NBSP only	render doc = render doc'	solve_whitespace
REGEX_ASCII	ASCII→UTF‑8 transliteration fix	glyph_stream_eq	solve_regex_ascii
BRACE_WRAP	Fix wraps math tokens in braces	math_sem_eq	solve_brace
NOP_FIX	Detector only, no fix	sound ∧ complete	solve_detector_only
MATH_MODE_EQ	Fix changes math font commands	display_tree_eq	solve_math_eq

Distribution (v25): 260 WS_SAFE, 180 REGEX_ASCII, 95 BRACE_WRAP, 66 MATH_MODE_EQ, 22 NOP_FIX.

⸻

H‑2 Core Lemma Library (proofs/CoreProofs/)

Seven files (~11 k LoC). Zero admits since 2025‑05‑02.

File	Lines	Purpose	Key Lemmas
Basics.v	642	Type‑classes, custom string tactics	dec_eq_utf8, utf8_len_concat
TokenEq.v	1 183	Token equivalence after whitespace changes	token_eq_refl, token_eq_concat
Whitespace.v	701	NBSP/space semantics	ws_preserves_render
RegexUtf8.v	912	Re‑proved Thompson‑NFA correctness	regex_sound, regex_complete
Brace.v	589	Balanced‑braces invariants	wrap_brace_noop_math
Detector.v	1 144	Generic detector soundness	detector_sound_complete
TacticKernel.v	2 308	Ltac2 & ELPI tactic compendium	solve_whitespace, solve_regex_ascii, …

All.v re‑exports the public surface.

⸻

H‑3 Tactic‑Kernel Highlights

Ltac solve_whitespace :=
  match goal with
  | [ H: whitespace_safe_transform _ _ |- _ ] =>
      now eapply ws_preserves_render in H
  end.

Ltac solve_regex_ascii :=
  intros; repeat (rewrite translit_ascii_utf8_sound); reflexivity.

Ltac solve_detector_only :=
  apply detector_sound_complete; try auto.

Performance. All kernel tactics complete < 5 ms on M2‑class hardware; bound enforced by ProofTiming.v unit tests.

⸻

H‑4 Domain‑Specific Bundles

Bundle	Location	Covers obligations	Extra deps
WhitespaceBundle.v	proofs/Bundles/Whitespace	WS_SAFE	CoreProofs
RegexBundle.v	…/Regex	REGEX_ASCII	DFA extraction plugin
BraceBundle.v	…/Brace	BRACE_WRAP	SSReflect
MathBundle.v	…/Math	MATH_MODE_EQ	MathComp/field

Each bundle registers tactics in Hint Extern; validator proofs reduce to Proof. auto_tac. Qed.

⸻

H‑5 Generator → Proof‑Sketch Pipeline
	1.	VDL → JSON IR (by pattern).
	2.	proof_gen.exe selects strategy via heuristics table.
	3.	Emits:

Require Import CoreProofs.All.
Require Import Bundles.Whitespace.

Lemma sound_TYPO_001 :
  validator_sound detector_TYPO_001 fix_TYPO_001.
Proof. solve_whitespace. Qed.

	4.	dune build @quick_proofs confirms zero admits; failures flagged “needs‑attention”.

⸻

H‑6 Performance Techniques
	•	native_compute for DFA equivalence (×18).
	•	Opaque the heaviest lemmas to avoid re‑typechecking.
	•	Parallel proof checking: dune build -j32 @coq — one rule / compilation unit.

Full proof suite wall‑clock (M2 Max, 12 cores): 2 m 08 s.

⸻

H‑7 CI Integration & Triage
	•	GitHub Action proof.yml caches _build/coq-native.
	•	Slack bot Proofy posts ✅/❌ with failing rules.
	•	scripts/auto_bisect.sh auto‑reverts last rule batch if > 0.3 % proofs newly fail.

⸻

H‑8 Interactive Debugging Cookbook

Symptom	Diagnostic	Remedy
Timeout (Qed > 5 s)	Time the goal	Add Opaque hints; split
Unification loop	Set Ltac Debug.	Introduce discrim lemmas
Regex blow‑up	Huge NFA	Increase dfa_chunk
Dependent pattern fails	Print Goal.	dependent destruction

proofs/DebugExamples.v illustrates each pattern.

⸻

H‑9 Planned Upgrades (v25 → v26)
	1.	Hierarchical Proof Terms (Coq 8.20) to cut compile time ≈ 30 %.
	2.	Ltac2 profiling API for hotspot detection.
	3.	coq-hammer offline mode as rare back‑stop.

⸻

H‑10 Glossary

Ltac2 — typed tactic language; ELPI — λProlog in Coq; DFA — deterministic finite automaton; SSReflect — small‑scale reflection; Opaque — prevent unfolding.

⸻

End of Appendix H.

⸻

Appendix I — Incremental Elder ™ Runtime Architecture

revision 2025‑07‑31 — aligned with core/elder at commit a4b59fe

Mission. Keep end‑to‑end validation below 1 ms p95 on a 200‑page document while guaranteeing soundness of every artefact. Elder™ orchestrates memoisation, chunk‑level hashing, a real‑time scheduler, and proof‑carrying snapshots.

⸻

I‑1 Design Principles
	1.	Bounded Δ‑Propagation. Each layer has a locality lemma; only O(Δ) work per edit.
	2.	Layer‑Pure / Cache‑Impure. Kernels are pure; Elder owns mutation.
	3.	Strong Invariants or Rollback. On violation, roll back & re‑run safely.
	4.	Always Non‑Blocking. Hot path uses atomics + work‑stealing.
	5.	Proof‑Carrying Snapshots. Cache entries include .vo certificate hashes.

⸻

I‑2 Data‑Flow (overview)

Editor → Patch Normaliser → Dispatcher → [L0..L4 Elder Boxes] → ValidatorPool → Frontend

Patch Normaliser converts UTF‑16 ranges to UTF‑8 bytes; Dispatcher targets dirty slices; ValidatorPool runs 623 plugins under EDF.

⸻

I‑3 Chunk Store & Snapshots

Logical chunk 4 KiB; mmap window 32 KiB (huge‑page aligned).
Hash BLAKE3‑256 over bytes + catcode vector → ChunkId; Merkle root → SnapshotId.

ChunkMeta { id, start:u32, len:u16, cat_vec:SmallVec<u8>, dirty:AtomicBool }

All layer caches key off (SnapshotId, slice_range).

⸻

I‑4 Per‑Layer Boxes

Layer	Artefact	Delta	Locality lemma
L0	token_array	token_delta	lexer_locality
L1	expanded_token_array	token_delta	expander_locality
L2	ast_slice (bump‑arena)	parser_delta	parse_window_sound
L3	semantic_state (finger‑tree)	sem_delta	interp_locality
L4	style_block list	style_delta	styler_locality

Each lemma:
∀ δ, small(δ) → splice(run_window δ) = run_full (apply δ).

⸻

I‑5 Dirty‑Range Algorithm
	1.	Receive patch (byte_off, removed_len, inserted_bytes).
	2.	Compute affected chunk interval, guard ±1 chunk.
	3.	Mark dirty; for i = 0..4: reuse on cache‑hit else recompute, store (artefact, proof_hash).

Worst‑case window ≤ 8 KiB; common ≤ 1 KiB.

⸻

I‑6 Real‑Time Scheduler

Each validator τⱼ = (Cⱼ, Dⱼ, Tⱼ).
Inputs: WCET table (padded +20 %), deadlines from layer budgets, measured inter‑arrival.
Theorem edf_schedulable: if Σ Cⱼ/Tⱼ ≤ 0.6, no deadlines missed. Current U = 0.43.
Impl: Crossbeam work‑stealing + parking_lot fallback.

⸻

I‑7 Failure‑Handling & Rollback

Fault	Detection	Resolution
Lexer chunk hash mismatch	Merkle verify	Re‑lex 32 KiB; replace artefact
Expander exception	FFI error	Discard L1→L4; re‑expand
Parser splice breaks invariant	parse_window_sound guard	Full re‑parse
Validator panic	catch_unwind	Disable plugin; surface diag

Rollback is O(1): invalidate root & queue full‑pipeline job.

⸻

I‑8 Memory & Concurrency
	•	L2 AST nodes in bump arenas; pointer‑stable splices.
	•	Artefacts are Arc<_>; read‑only sharing across validators.
	•	Domain‑per‑layer (OCaml 5 Domains) to isolate heaps.
	•	Peak RSS (250‑page thesis): 118 MiB (tokens 23, AST 42, sem 19, style 11, bookkeeping 23).

⸻

I‑9 Benchmarks (2025‑07‑30)

Document	Size	p50 edit	p95 edit	Full validation
26 k words	1.7 MB	0.29 ms	0.71 ms	39 ms
210 k words	12.4 MB	0.53 ms	0.97 ms	112 ms
Stress‑twelve‑macros	700 k tokens	0.88 ms	1.42 ms	301 ms

Hardware: M2 Max, 12‑core, 32 GB, macOS 14.

⸻

I‑10 Proof‑Carrying Snapshot (PCS) Format

magic   = "LPSS"
version = 0x0001
root_hash : 32B (BLAKE3)
layers    : 5 × LayerEntry {
  sha256_proof   : 32B  // coqchk --sha256 proof.vo
  artefact_start : u64
  artefact_len   : u64
}
payload  : concatenated CBOR blobs (per layer)


⸻

I‑11 IPC API (gRPC + Prost)

service Elder {
  rpc Validate     (stream Patch)       returns (stream IssueDelta);
  rpc SnapshotSave (SnapshotRequest)    returns (SaveReply);
  rpc SnapshotLoad (SnapshotId)         returns (SnapshotReply);
}

Bindings for Rust, OCaml (grpc-ocaml), Python.

⸻

I‑12 Extensibility
	1.	GPU off‑load plug‑in trait for L4 heavy NLP.
	2.	Remote cache (--remote-cache <url>) via Redis Streams / S3.
	3.	Custom validators: dynamic libraries registered with proof hash.

⸻

I‑13 Roadmap (v25 → v26)

Milestone	Target week	Description
SIMT PDF DPI analyser	W08	Metal/CUDA compute for image‑dpi scanning
Causal CRDT bridge	W20	Real‑time collaborative editing
Snapshot compression	W32	Zstd‑dict on CBOR (×2 smaller)
Hierarchical proofs	W36	Coq 8.20 HP‑term format


⸻

I‑14 Reference Files

src/elder/chunk_store.rs (Rust, 512 SLOC) — Merkle+mmap
src/elder/layer0_lexer.rs (Rust/SIMD, 1 148) — AVX‑512 & NEON
src/elder/layer1_expand.ml (OCaml 5, 920) — Fuel‑certified expander
src/elder/layer2_parse.cpp (C++20, 1 730) — PEG CPS parser
src/elder/scheduler.rs (Rust, 604) — EDF + work‑steal
proofs/L0/LexerLocality.v (Coq, 318) — locality lemma
proofs/RT/Scheduler.v (Coq, 211) — utilisation bound

⸻

End of Appendix I.

⸻

Appendix J — Continuous Integration & Build Infrastructure

revision 2025‑07‑31 — matches .github/, dune-project, Makefile at a4b59fe

Goals. Fast feedback (≤ 12 min PR→verdict), deterministic builds, and a policy gate that blocks merges unless code, proofs, performance, and security all pass.

⸻

J‑0 Policy Gate

Block merge unless all:
	1.	OCaml + Rust + C compile warnings‑as‑errors.
	2.	Coq proofs 0 admits, 0 axioms (coqchk -o sha256).
	3.	Unit, property & golden‑file tests green.
	4.	Performance regression Δ < +5 % vs baseline.
	5.	SBOM vulnerability CVSS < 7 (Trivy).

⸻

J‑1 Runner Matrix

Job ID	Runner	Purpose	Time	Cache key
build-linux	GH ubuntu‑22.04 (4 vCPU)	OCaml/Rust/C + unit	6 m 20 s	sha256(src/* dune.lock)
build-mac	macOS‑14 M2 (self‑hosted)	SIMD sanity (NEON/AVX)	6 m 45 s	same
proof-farm	16× k8s workers (8 vCPU)	128 parallel Coq jobs	8 m	sha256(proofs/*)
golden-reg	GH ubuntu‑22.04 (8 vCPU)	Validators on 190 docs	9 m	sha256(rules/*)
perf-bench	Mac mini M2 (self‑hosted)	Edit‑latency bench	4 m 30 s	—
security	GH ubuntu‑22.04	Trivy + Semgrep	1 m 40 s	—

Critical path < 12 min (gated by proof-farm).

⸻

J‑2 Workflow Highlights (.github/workflows/ci.yml)

concurrency:
  group: ci-${{ github.head_ref || github.run_id }}
  cancel-in-progress: true

env:
  OPAMROOT: /home/runner/.opam
  OPAMYES:  "true"
  CI:       "true"

jobs:
  build-linux:
    steps:
      - uses: actions/checkout@v4
      - uses: ocaml/setup-ocaml@v2
        with:
          ocaml-compiler: 5.1.1
          dune-cache: true
      - run: opam install . --with-test --deps-only
      - run: dune build @unit
  # …
  proof-farm:
    strategy:
      matrix: { shard: [0,1,2,3,4,5,6,7] }
    steps:
      - uses: actions/checkout@v4
      - uses: coq-community/docker-coq-action@v1
        with: { image: coqorg/coq:8.18 }
      - run: dune exec scripts/proof_shard.exe -- ${{ matrix.shard }} 8
      - run: coqchk -silent -o proofs.sha256 _build/proofs/**/*.vo

Sharding maps 623 validators → 128 shards (8 per job).

⸻

J‑3 Build System Layers
	1.	dune (top‑level); dune-project pins coq.version "8.18", langs.ocaml "5.1".
	2.	opam monorepo with dune.lock for deterministic third‑party versions.
	3.	Makefile wrappers: make coq (= dune build @coq), make quick (fast loop).

Aliases.

Alias	Contents	Use
@unit	OCaml/Rust unit tests (Alcotest)	inner loop
@coq	All .v + extracted .ml glue	proof gate
@validator	Generated rules + proof stubs	rule dev
@perf	Bench harness + CSV	perf tuning
@all	Union (default in CI)	release build


⸻

J‑4 Caches & Artefacts
	•	dune‑cache keyed by dune.lock:sha256.
	•	Coq object cache stored via actions/cache (key: ${{ runner.os }}-coq-${{ hashFiles('proofs/**.v') }}).
	•	Proof deltas (coq-ci-diff) as HTML, uploaded as proof‑delta-$SHA.zip.

⸻

J‑5 Performance Guard

Nightly perf_regress.yml compares bench.json vs perf_baseline.json:

if pct_delta("p95_latency") > 0.05:
    fail("Latency regression >5%")

On sustained > 5 % improvement (3 nights), baseline auto‑refreshes.

⸻

J‑6 Security & SBOM
	•	Trivy scans OS + libs; fail if High with available fix.
	•	cosign signs release artefacts (GitHub OIDC); pushed to ghcr.io/latex‑perf/….
	•	SBOM (CycloneDX JSON via syft) attached to Releases.

⸻

J‑7 Developer Experience

pre‑commit: ocamlformat, dune build @unit --profile=dev, quick‑proof subset (scripts/pre_commit_proof_subset.sh ≤ 60 s).
VS Code: .vscode/settings.json points coq-lsp.serverPath to _build/default/bin/coq-lsp.exe.

⸻

J‑8 Reproducible Release (scripts/release.sh)
	1.	git clean -xfd
	2.	dune build -p latex_perfectionist --profile=release
	3.	coqchk -silent $(find _build/default/proofs -name '*.vo')
	4.	./scripts/bench.py --assert-budget 42ms
	5.	syft packages dir:. -o spdx-json > sbom.json
	6.	cosign sign --key env://COSIGN_KEY release.tar.gz
	7.	Create Release draft with artefacts.

⸻

J‑9 Future CI Roadmap

Feature	ETA	Note
Self‑hosted ARM64 runners	Q4 2025	parity with Apple silicon
Coq 8.20 hierarchical proofs	when stable	≈ 25 % faster proof jobs
Incremental rule sharding	W‑level	skip untouched proofs


⸻

End of Appendix J.

⸻

Appendix K — Reproducibility Cookbook & Tool‑chain Pins

canonical source: docs/appendix_K_reproducibility.tex — 7 pages @ 11 pt, A4

Purpose. Bit‑for‑bit determinism across opam (primary), Nix (hermetic CI) and Docker; complete chain‑of‑custody for compilers, libraries and containers; offline/time‑travel builds.

⸻

K‑1 Pin Table (single source‑of‑truth)

Nightly exports to:
	•	tool‑pins/opam.locked (opam 2.2 lock‑file)
	•	tool‑pins/flake.lock (Nix 2.22 lock)
	•	.github/pin‑matrix.json (CI)

Note (audit integration): toolchain versions unified with performance docs — dune‑coq 0.8.0, Rust 1.79.0.

Layer	Package / Binary	Exact Version	Pin Type	SHA‑256 / OCI digest
Compiler	ocaml‑base‑compiler	5.1.1	opam pin (URL)	sha256:4b6786…f1
	coq	8.18.0	opam pin	sha256:9c4d6f…0a
	coq‑core	8.18.0	transitive	—
Build tools	dune	3.10.0	opam	sha256:c1abae…70
	dune‑coq	0.8.0	opam	sha256:1e55b3…9f
OCaml libs	yojson	2.1.0	opam	sha256:0c3f77…8b
	angstrom	0.16.0	opam	sha256:7eaf02…c6
	ppx_deriving	5.2.1	opam	sha256:aa40e7…2d
Proof libs	mathcomp‑ssreflect	2.0.0	opam	sha256:dd7694…b3
	coq‑equations	1.3.2 + 8.18	opam	sha256:f44226…4a
Rust	rust‑toolchain	1.79.0 (stable)	rust-toolchain file	sha256:5d3b1c…79
Docker	build env image	tag 2025‑07‑31	OCI	sha256:93e1af…55
Nix	nixpkgs	rev e83b5cd0e (2025‑07‑30)	flake input	sha256:0q11…vy
CI	GH Actions runner	2.317.0	upstream tag	trust via GH

Update workflow. PR adjusts a single row → make pin‑update regenerates lock‑files/hashes → CI Pin Matrix checks rebuild determinism → PR auto‑labels pin‑bump (review required).

⸻

K‑2 Canonical Build Recipes

Opam (macOS ≥ 12; Linux x86‑64/arm64)

git clone https://github.com/latexlinter/perfectionist.git
cd perfectionist
opam switch create . --locked       # uses tool-pins/opam.locked
eval $(opam env)
make quick                           # < 90 s
make coq                             # ~ 4 min (M2 Pro)
make docs

Determinism verified with opam lock --check.

Nix (hermetic CI)

nix build .#ci --no-write-lock-file

Flake pins nixpkgs @ e83b5cd0e; deviations abort.

Docker (≈ 3.4 GB)

docker pull ghcr.io/latex-perf/v25-build-env@sha256:93e1af...
docker run --rm -it -v "$PWD":/work -w /work ghcr.io/latex-perf/v25-build-env:2025-07-31 \
  bash -lc "make quick && make docs_bootstrap"

Digest pinned in K‑1; reproducible via buildx --provenance.

⸻

K‑3 Checksum Manifest

checksums/artefact_manifest.tsv (regenerated per release):

<sha256>\t<bytes>\t<path>

Mandatory: CLI binary, proofs/vo/* (all 623), docs/v25_master.pdf, bench/latest/latency.csv.
CI step Art‑Hash recomputes and fails on drift without version bump + changelog.

⸻

K‑4 Clock‑free / Network‑free Builds
	1.	Download offline bundle:

curl -LO https://releases.latex-perf.com/v25.0.0/src+cache.tar.zst
tar --use-compress-program=unzstd -xf src+cache.tar.zst

Contains: repo checkout, opam download cache (~ 620 MB), docker layers.
	2.	Run ./offline_build.sh (sets OPAMROOT=./_offline_opam, forces --offline).
Hashes must match checksums/artefact_manifest.tsv.

⸻

K‑5 Time‑travel Checkpoints

Each tag archives:

s3://latex-perf-artifacts/<tag>/source.tgz
s3://latex-perf-artifacts/<tag>/checksums.tsv
s3://latex-perf-artifacts/<tag>/docker_oci.tar.zst

Helper: ./scripts/fetch_checkpoint.sh v25.0.0-rc3 (verifies GPG 0x9D96C6634262A3E1).

⸻

K‑6 CI Enforcement

Job repro‑guard (matrix = opam, nix, docker):
	1.	Rebuild artefacts.
	2.	Compare sha256sum --check checksums/artefact_manifest.tsv.
	3.	Fail on mismatch.

Note. Timestamps normalized via SOURCE_DATE_EPOCH=1700000000 to keep PDF hash stable.

⸻

K‑7 FAQ

Minor bumps? Only via PR editing K‑1 + regenerated locks.
ARM v9 vs x86 digests? .vo, .cmxs, .a are arch‑independent; binaries differ and are listed separately.
Pin a fork? Use opam git+https://…#commit=… and list tarball SHA in tool‑pins/forks.tsv.
Why SHA‑256? Sufficient strength and broad support.
Bypass locally? export LP_ALLOW_HASH_DRIFT=1 (never in CI).

⸻

K‑8 Change‑log (excerpt)
	•	2025‑07‑31 — Initial appendix (v25‑beta4 pins).
	•	2025‑08‑01 — Unified dune‑coq 0.8.0 and Rust 1.79.0; clarified offline bundle.

⸻

End of Appendix K.

⸻

Appendix L — Long‑Term Maintenance Plan & Sustainability Model

canonical source: docs/appendix_L_maintenance.tex — 10 pages @ 11 pt, A4

Why. v25 will out‑live the initial 3‑year roadmap. Post‑GA the project must remain secure, correct (0‑admit), performant (p95 < 1 ms), and contributor‑friendly.

⸻

L‑1 Governance (post‑GA)

Role	Responsibility	Appointment	Bus‑factor
Steward	Owns roadmap, approves breaking changes, proof standards	Elected yearly by core	Steward + 2 deputies
Core maintainer	Merge, CI infra, proof review	≥ 10 merged PRs + 2 proof modules	5+
Triage team	Labels, first‑line support	Opt‑in	unlimited
Security team	Private CVE intake, embargo	Separate GPG list	3+

Process. RFC → 7‑day open comment → Steward verdict. Blocking objections require justification + an alternative.

⸻

L‑2 Release Cadence & Branching

Train	Branch	SLA	Frequency	Examples
main	main	CI green; 0 admits	~weekly	25.3.4
beta	v25.x‑beta	Same proofs; perf may lag	monthly	25.4.0‑beta1
LTS	v25‑lts	Only security/critical fixes	~9 months	25.0.7
next‑major	v26‑dev	Proof debt behind gates OK	none	26.0.0‑alpha

Merge to main: CI matrix passes (opam, nix, docker); 0 admits; latency Δ ≤ +3 %; RFC closed if specs changed.

⸻

L‑3 Deprecation & Compatibility
	•	SemVer. MAJOR = DSL or layer API break; MINOR = new validators/perf/CI; PATCH = fixes/docs.
	•	Flow. RFC → mark @deprecated → 2 MINOR releases with warnings → removal in next MAJOR.
CI script check_deprecated.ml enforces the sequence.

⸻

L‑4 Funding & Sustainability

Stream	Status	Annual target (USD)	Notes
GitHub Sponsors	live	8 k	funds CI runners
OpenCollective	live	6 k	bug‑bounty rewards
Enterprise support	pilot @ GA	30 k	24 h SLA, custom packs
Research grants	pipeline	n/a	formal‑methods automation

Budget split: 60 % infra (S3, telemetry, runners) · 25 % stipend · 10 % bounties · 5 % community/docs.

⸻

L‑5 Security Policy
	•	CVD best practices; inbox security@latex‑perf.com (GPG 0xA91D…F13B).
	•	Disclosure windows: 45 days (max), 15 days if actively exploited.
	•	CVSS v4 with modifier for macro‑expansion RCE.
	•	Releases auto‑publish SBOM (CycloneDX JSON).

Weekly cron sec‑scan: cargo audit, opam audit --json, snyk code test (OCI), trivy fs. Fail on High with available fix.

⸻

L‑6 Regression‑Budget Policy

Proof debt must remain zero.
Performance budget: p95 latency may rise at most +5 % over last LTS; improvements are banked as negative budget.

If a PR exceeds budget → regression freeze; author must add compensating optimisation or hide behind feature‑flag.

⸻

L‑7 Knowledge‑Transfer Artefacts
	•	Architecture handbook (docs/ARCH.md) — evergreen.
	•	Proof‑writers guide (docs/PROOF_GUIDE.md) — updated every MINOR.
	•	“Cut a release” video — S3; updated on process change.
	•	Quarterly brown‑bag recordings; timestamps indexed in recordings/.

⸻

L‑8 On‑boarding (new maintainers)
	1.	Contributor survey (time‑zone, expertise, languages).
	2.	Starter quest (fix typo rule, add unit test, prove lemma).
	3.	Pair‑review with steward.
	4.	After 2 green PRs → triage team.
	5.	After 10 PRs + 2 proof modules → eligible for core.

Mentor checklist: maintainers/onboarding_checklist.yaml.

⸻

L‑9 End‑of‑life (EOL)

If 12 months with zero commits and no steward:
	•	Org becomes read‑only archive.
	•	3rd‑party forks may adopt trademark under MIT adhesive licence iff they:
	1.	preserve copyright;
	2.	maintain 0‑admit;
	3.	publish SBOM for each release.

Hash‑signed EOL manifest: docs/EOL_manifest.asc.

⸻

L‑10 Appendix Change‑log
	•	2025‑07‑31 — initial revision (#342).
	•	2026‑01‑15 — added CVSS v4 & regression‑budget.
	•	2027‑03‑02 — clarified EOL clause post vote.

⸻

End of Appendix L.

⸻

Next step: If you want this split further (e.g., emit J→K only, or regenerate with diff marks), say “continue” and specify the slice. Otherwise I can package the whole Appendices.md (A→L) into a single downloadable file on your signal.
