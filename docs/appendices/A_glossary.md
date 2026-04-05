# Appendix A — Glossary & Notation

Per v25 master plan §15, Table A (8 pages).

## Core Terminology

| Term | Definition |
|------|-----------|
| **Arena** | Bump-allocated memory region for token storage; freed as a unit |
| **Catcode** | TeX category code (0–15) assigned to each input character |
| **Delta** | Incremental change between two layer snapshots |
| **Elder** | Orchestrator process managing cross-layer state synchronisation |
| **Fuel** | Bounded recursion counter preventing non-termination in macro expansion |
| **Generation** | Monotonically increasing counter for snapshot versioning |
| **Golden test** | Corpus file with expected validator results in YAML (fire/no-fire assertions) |
| **Layer** | One of five processing stages: L0 (Lexer), L1 (Expander), L2 (Parser), L3 (Semantics), L4 (Style) |
| **Pilot** | Feature-flagged subset of validators enabled via `L0_VALIDATORS=pilot` |
| **Rule** | A single validation check with ID, severity, message, and run function |
| **Snapshot** | Immutable view of all layer states at a given generation |
| **VPD** | Variable Pattern Detection — catalogue of regex/substring patterns for proof generation |

## Rule Families

| Prefix | Layer | Count | Domain |
|--------|-------|-------|--------|
| TYPO | L0 | 63 | Typography (quotes, dashes, accents) |
| SPC | L0 | 35 | Spacing and whitespace |
| ENC | L0 | 24 | Encoding and character validation |
| CHAR | L0 | 22 | Control characters and Unicode |
| VERB | L0 | 17 | Verbatim and code environments |
| CMD | L0/L2 | 14 | Command definition and usage |
| DELIM | L1 | 11 | Delimiter matching |
| MATH | L1/L2 | 100 | Mathematical notation |
| REF | L1/L2 | 12 | Cross-references and citations |
| SCRIPT | L1 | 22 | Sub/superscript formatting |
| TAB | L2 | 16 | Table structure |
| FIG | L2/L3 | 25 | Figure and float handling |
| PKG | L2/L3 | 25 | Package compatibility |
| TIKZ | L2/L3 | 10 | TikZ/PGF diagrams |
| LAY | L3 | 24 | Page layout and typography |
| COL | L3 | 7 | Color management |
| PDF | L3 | 12 | PDF structure and accessibility |
| FONT | L1/L3 | 13 | Font selection and metrics |
| LANG | L2/L4 | 16 | Language consistency |
| RTL | L1/L3 | 5 | Right-to-left text |
| CJK | L0/L3 | 16 | CJK character handling |
| STYLE | L4 | 49 | Prose style and consistency |
| CHEM | L1 | 10 | Chemistry notation |
| L3 (expl3) | L1/L2 | 11 | LaTeX3 programming |
| META | L2/L3 | 4 | PDF metadata |
| DOC | L2/L3 | 5 | Document structure |
| BIB | L3 | 17 | Bibliography hygiene |

## Severity Levels

| Level | Meaning | CI Gate |
|-------|---------|---------|
| **Error** | Likely compilation failure or broken output | Blocks merge |
| **Warning** | Probable issue requiring attention | Informational |
| **Info** | Style suggestion or best practice | Informational |

## Notation

| Symbol | Meaning |
|--------|---------|
| p50/p90/p95/p99 | Latency percentiles used in SLA and dashboards (§8) |
| QED | Proof completed with no admits |
| SLA | Service Level Agreement (performance gate threshold) |
| FPR | False Positive Rate |
| BIO | Begin/Inside/Outside tagging scheme for span extraction |
| `wf_Lk(x)` | Well-formedness predicate for layer k |
| `⟦x⟧` | Semantics of x (rendered textual stream) |

## Full Glossary Index (107 entries)

| Term / Abbrev. | Definition & Context |
|----------------|---------------------|
| ABI | Application Binary Interface. Stable C-level boundary for OCaml-Rust FFI (§8, §E) |
| ACL | Access-Control List. GitHub branch protection and proof-farm namespace permissions (§11.3) |
| Aho-Corasick | Multi-pattern string matching algorithm for batch token-sequence validators (§C-10) |
| Arena | Bump-allocator providing moving-GC avoidance for tokens/AST nodes (`arena.ml`, §E-4) |
| ASCII-translit rule | Validator family rewriting ASCII pseudo-glyphs to proper Unicode (§C-2) |
| AST | Abstract Syntax Tree produced by L2 parser; root type `document` (`parser_l2.ml`) |
| Audit-trail | Hash-chained log of validator generation steps; SBOM pipeline artefact (§7.5, §12) |
| BERT | Bidirectional Encoder Representations from Transformers; base LM for span extraction (§G) |
| Bitemporal Trie | Two-axis trie keyed by (byte-offset, revision-timestamp); Elder cache backbone (§I-3) |
| Bootstrap Skeleton | Minimal compilable repo layout delivered Week 1 (§14 week 1) |
| Build Farm | Kubernetes job set (`proof-farm-`) running parallel Coq compilation (§12) |
| Byte Span | Pair (start,end) in UTF-8 bytes, half-open interval [start,end) (`loc` type) |
| Catcode | TeX category code 0-15; stored per token; table proven total (`Catcode.v`) |
| Causal Cache | Future feature: editing CRDT integrated remote cache; not GA (§I-12) |
| CI | Continuous Integration; GitHub Actions matrix in `.github/workflows/` (§12, §J) |
| Chunk | Fixed 4 KiB logical slice of source for incremental lexer (§I-3) |
| CJK | Chinese/Japanese/Korean script class; triggers specialised validators (§F) |
| Code-gen | Automatic production of OCaml `.ml` + Coq `.v` from validator DSL (§C) |
| Confusables | Unicode glyphs visually similar; validator family ENC-015 checks NFKC (§F-2) |
| Corpus | Curated LaTeX papers + synthetic suites; stored under `corpora/` (§10) |
| Coverage Metric | Percentage of corpus documents for which all validators run without crash (§10.2) |
| Crash-free latency | p99 latency measured on sessions with zero validator panics (§8) |
| CRDT | Conflict-free Replicated Data Type; future distributed editor support (§I-12) |
| Cross-layer Consistency | Snapshot hashes form monotone sequence; theorem `snapshot_consistency` (§5) |
| CSA | Cache Set Associativity; param in lexer chunk index; default = 4 |
| DAG | Directed Acyclic Graph; validator dependency graph (`validator_dag.ml`, §C-4) |
| Delta | Minimal change descriptor; variants: token_delta, parser_delta, sem_delta (§B-9) |
| Determinism Proof | `lexer_step_determinism`: output independent of traversal order (§D) |
| DFA | Deterministic Finite Automaton; compiled form of regex validators (§H-2) |
| Dirty Region | Byte span invalidated by edit; propagated through layers by Elder (§I-5) |
| Disaster-Recovery Playbook | Steps for hardware loss, S3 corruption, proof-farm outage (§11.3) |
| dune-coq | Build-system glue generating `.vo` from `.v`; pinned version 0.8.0 |
| EDF | Earliest Deadline First scheduler inside validator thread-pool (§I-6) |
| Elder | Incremental orchestrator caching 5 layers; design in Appendix I |
| Elder Box | Internal data-structure `{artefact; hash; dirty_ranges}` for a layer (§I-2) |
| End-to-End Gate | CI workflow `milestone-gate-*` checking cross-layer KPIs (§14) |
| Env Stack | Interpreter field tracking current environment nesting (`semantic_state.ml`) |
| Expand Fuel | Natural number budget ensuring macro expansion termination; proof in `ExpandProofsFinal.v` |
| Fix-Template | DSL snippet for automatic source rewrite; compiled to OCaml replacer (§C-6) |
| FSA-Trie | Finite-state automaton compressed trie for labels table (§B-5) |
| Fuzz Suite | QuickChTeX property-based random generator (§10.3) |
| GA | General Availability release; Week 156 milestone (§14) |
| GPU Cold-Start | Optional Metal/CUDA off-load of heavy NLP; Q11 research (§E-8) |
| Ground Truth | Human-labelled YAML file enumerating expected validator issues (§10.2) |
| HAMT | Hash-array mapped trie backing user macro table (§3.3.3) |
| HDBSCAN | Hierarchical density-based clustering; groups ML spans into pattern families (§G) |
| ICU | International Components for Unicode; provides BreakIterator (§F) |
| IDE Latency | p95 edit-to-diagnostic time in VS Code plugin; SLA < 1 ms (§8) |
| Incr Key | Tuple unique per cache entry: (layer_id, start, end, cat_hash, rev) (§B-9) |
| Interpreter | L3 fold reducer computing `semantic_state` (§B-5) |
| Issue | Diagnostic record `{id; loc; severity; msg}` (`result` type in `validators_common.ml`) |
| JSON Manifest | Side-file produced by code-gen describing validator metadata (§C-5) |
| LangID | Compact language classifier; 65-language babel mapping (`language_detect.ml`, §F-3) |
| Layer Artefact | Cached result for a processing stage: tokens, AST, sem_state, etc. (§B-9) |
| Lexer State | Record with catcode table, line_no, pending BOM; for chunk lexing (§B-2) |
| LRU | Least-Recently-Used cache eviction; expander DAG cache window = 4096 |
| Menhir-cert | Certified LR(1) parser generator; base for PEG parser proofs (§D) |
| Merkle Snapshot | Root hash of chunk-id tree, uniquely identifies document revision (§I-3) |
| Metric Dashboard | Grafana board auto-generated nightly; endpoints /perf, /quality, /proof |
| ML-Assist | Pipeline mining patterns, generating validator specs, auto-proving (§G) |
| Monotone Fuel Lemma | `sufficient_fuel` — more fuel never changes success result (§D) |
| NFA Extraction | Coq tactic converting regex to Thompson NFA for generic proofs (§H) |
| NFC/NFD/NFKC/D | Unicode normalisation forms; NFC used for hashing (§F-2) |
| NPD | Neural Pattern Discovery module; BERT + CRF span extractor (§G) |
| Opcode Budget | Micro-benchmark counter limiting validator execution instructions |
| Parser Delta | Splice description `{path; with_}` bridging L2 → L3 (§B-9) |
| Pattern DSL | YAML + body dialects (regex, token, structural) compiling to validators (§C) |
| PEG | Parsing Expression Grammar; 239-line spec for LaTeX subset (`l2_parser_peg_grammar.peg`) |
| Perf Harness | Benchmark suite simulating keystrokes and recording metrics (§8) |
| Proof Debt | Count of `Admitted.`; must be 0 by Week 130 gate (§14, currently 0) |
| Proof Family | Set of validators sharing generic proof template (RegexFamily, etc.) (§H) |
| Proof-Farm | Scalable Coq compilation cluster (`proof.yml` CI job) (§12) |
| QuickChTeX | Property-based fuzz generator targeting TeX grammar (§10.3) |
| RB Invariant | Ring buffer length ≤ capacity; `lockfree_queue.ml` (§I-2.3) |
| RegexProofs | Coq library providing `text_validator_sound` tactic (`RegexFamily.v`, §H) |
| Round-trip Property | `concat(split(txt)) = txt` invariant for sentence splitter (§F-5) |
| Rule Family | Group of validators (e.g., TYPO-###) sharing pattern skeleton (§C-2) |
| S3 | Object store holding corpus and SBOM artefacts (§11.3) |
| SBOM | Software Bill-of-Materials generated by CI; scanned for CVEs (§12, §L-8) |
| Seccomp | Linux syscall filter used to sandbox validator plugins (`seccomp.json`, §11) |
| Semantic State | Record of counters, labels, refs; maintained by `semantic_state.ml` (§B-5) |
| SIMD | Single Instruction Multiple Data; AVX-512 & NEON for lexer/scanner (§E) |
| Snapshot Id | Hash of chunk tree; key for Elder cache (§I-3) |
| Soundness | Proof that validator detects all and only intended violations (`text_validator_sound`) |
| Span Extractor | BERT + CRF model tagging error spans in corpus (§G, retired v1) |
| Splice Equiv Lemma | `splice(parse_window(delta)) ≡ parse(full)` (§4.3.1) |
| SSA | Static Single Assignment; not used (recorded to avoid confusion) |
| STYLE Block | Paragraph-level text unit processed by L4 (§B-6) |
| Telemetry Event | JSON blob posted for every validator execution (§I-8) |
| Token ADT | 8-constructor sum type with byte offsets (`tokenizer_lite.ml`, §B-1.2) |
| TokenSeq Pattern | Validator dialect matching on token variants, compiled to Aho-Corasick (§C-3.2) |
| Trace Replay | Perf harness mode replaying real editing sessions |
| Trie Hash | 64-bit FNV of parent-chain; feature for NPD (§G) |
| Typographic Validator | Rule family checking spacing, punctuation per language (§F) |
| Unicode Script | Property grouping codepoints; used in script detector (`unicode_split.ml`, §F-4) |
| Validation Issue | See Issue |
| Validator | Pair (detector, proof) with optional fixer; OCaml `rule` type (§C-4) |
| Validator Dependency Graph | DAG capturing rule dependencies; cycles forbidden (`validator_dag.ml`, §C-4) |
| Vectorised xxHash | AVX/NEON implementation hashing 256-byte windows (`xxh64.ml`, §E-3) |
| Version Vector | `{gen; parent_gen}` tuple for cross-layer consistency (`layer_sync.ml`, §I-2.1) |
| VSNA | Verified State-Machine Net-Accurate automaton for validator regex (§7.4) |
| Whitespace-safe | Fix inserting/deleting only space/Tab/NBSP; lemma `whitespace_preserves_render` (§H) |
| Workflow Bot | GitHub Action posting regression diffs for golden files (§10.2) |
| xxHash3 | Non-cryptographic hash function variant; SIMD accelerated (`xxh64.ml`, §E-3) |
| YAML Spec | Front-matter of `.vdl` validator files (id, family, pattern, ...) (§C-1) |
| Zero-Admit Gate | CI rule failing build if any `Admitted.` (proof-ci, §7, currently 0) |

(Total entries: 107)
