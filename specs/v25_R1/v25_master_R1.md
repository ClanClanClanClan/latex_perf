<!--
Provenance: This R1 update integrates every change from the audit into the textual master plan, aligning it with the machine‑readable YAML edition and the 623‑rule catalog. Sources: YAML edition (“LaTeX Perfectionist — v25 ▸ Unified Ground‑Truth Master Plan — YAML”)  [oai_citation:0‡v25_master.yaml](file-service://file-Jei1ndCmY4MvRuAwMe5JLL) and rules.yaml (623 rules)  [oai_citation:1‡rules_v3.yaml](file-service://file-Hch2y7Aqe3nMyQrFh1EvNK).
-->


LaTeX Perfectionist — v25

Unified Ground‑Truth Master Plan

Revision R1 — 2025‑07‑31  (Audit‑integrated update of R0‑2025‑07‑28)

This file is the single source of truth for v25.
It folds in (a) the original “LaTeX Perfectionist v25 – 3‑Year Solo‑Developer Master Plan”, (b) all answers to the 87 integration‑gap questions, and (c) all clarifications/decisions up to 2025‑07‑31 (audit integration).
Machine‑readable mirror: docs/v25_master.yaml. (Aligned per YAML edition.)  

⸻

TABLE OF CONTENTS

1 Executive Overview
2 Governance & Process
3 Repository & Build Layout
4 Five‑Layer Incremental Architecture (L0–L4)
5 Cross‑Layer Consistency & Synchronisation Protocol
6 Validator Framework (623 rules)
7 Proof‑Automation & 0‑Admit Policy
8 Performance Engineering Targets & Measurement Rules
9 Multi‑Language & Cultural Adaptation (21 languages)
10 Corpus & Ground‑Truth Strategy
11 Security, Sandboxing & Supply‑Chain Security
12 Distributed Proof‑Farm & CI/CD
13 Development Workflow & Tooling
14 Project Timeline & Milestones
15 Appendices

 A – Detailed API & Type Signatures
 B – Cache‑Key & Invalidation Algorithms
 C – Validator Dependency Graph & Conflict Resolution Rules
 D – Coq Proof Template Catalogue
 E – SIMD & Fallback Implementations
 F – Corpus Cleaning & Externalisation SOP
 G – Glossary

⸻

1 EXECUTIVE OVERVIEW

Metric	Baseline (v24‑R3)	Target (v25)	Current Week‑1 Status
Validators implemented	80 / 612	623 / 623	80
Proof admits	211	0 (strict)	0 (no admits in main)
0‑Axiom compliance	n/a	Yes (§7)	0 axioms ✅
p95 latency — perf_smoke (≈ 1.1 MB)	420 ms	< 25 ms (SLA gate 42 ms)	8.36 ms (median‑of‑100, baseline HW)  
p95 latency — edit‑window 4 KB	—	< 1 ms	proto CI gate wired
Multi‑language coverage	3	21	7 implemented, 14 stubbed

What changed in R1 (audit integration):
• Performance targets clarified to 25 ms (full‑doc perf_smoke) with 42 ms SLA buffer, plus 1 ms for 4 KB edit‑window; CI gates updated accordingly.
• Week‑1 admits = 0 and axioms = 0; the @proof‑debt mechanism remains available but unused at present. Values and gates are harmonised with the YAML edition.  

⸻

2 GOVERNANCE & PROCESS

Operating model. Solo‑Developer cadence retained (weekly rhythm unchanged).

Hard gates.
	1.	Zero‑Admit Gate (proof‑CI). Blocks main if any .v admits are present or the proof‑debt budget is exceeded.
Policy: temporary “proof‑debt” axioms are permitted only if tagged @proof‑debt(deadline="YYYY‑MM‑DD"), total count ≤ 10, and CI prints the remaining budget. After each item’s deadline they are hard build‑breakers. (Currently unused: admits=0, axioms=0.)  
	2.	Performance Gate (perf‑CI). Blocks main if p95 > 25 ms on perf_smoke or p95 > 1 ms on the 4 KB edit‑window pipeline, measured on the baseline hardware profile.  

Cadence & hygiene. Weekly planning, mid‑week integration cut, Friday checkpoints; pre‑commit: formatting, lint, admit‑count, repo‑size.

⸻

3 REPOSITORY & BUILD LAYOUT

Decision (Q1/Q2). Clean Bootstrap layout with canonical _CoqProject; legacy paths preserved behind dune wrapped=false libraries to avoid broad refactors.

repo/
├─ core/            # pure OCaml runtime
│   ├─ l0_lexer/
│   ├─ l1_expander/
│   ├─ l2_parser/
│   ├─ l3_semantics/
│   └─ l4_style/
├─ proofs/          # Coq source (mirrors core/ + families/)
├─ generator/       # validator DSL → code
├─ data/            # shared types (token, location, …)
├─ corpora/         # minimal + standard + categories + perf_smoke
├─ external_corpora/ (git‑ignored) # fetched by make
└─ scripts/

dune build and make quick under opam 5.1.1; see Appendix E for tool‑chain notes.  

⸻

4 FIVE‑LAYER INCREMENTAL ARCHITECTURE (UNCHANGED)

Design L0–L4 matches the original plan with these locked clarifications (from the 87‑Q set):
	•	Exact OCaml signatures are enumerated in Appendix A.
	•	Error propagation: each apply_delta returns (Result<'a, Error.t> * delta_out); errors bubble without committing partial state across layers.
	•	Fuel guarantees proved in ExpandProofsFinal.v; see §7.4 for templates.

⸻

5 CROSS‑LAYER CONSISTENCY & SYNCHRONISATION PROTOCOL

Resolves Moderate Concern #1.

Concept	Decision
Version Vector	Each artefact carries { gen:int; parent_gen:int }. Layer N accepts deltas iff parent_gen = Layer(N‑1).gen.
Memory Barrier	Elder orchestrator performs swap‑and‑publish under an AtomicU64 generation counter; validators read a snapshot by Arc handle.
Rollback	On error, Elder rolls back the child layer only; parent artefacts remain valid.
Consistency Window	At most one generation; validators observe either old or new snapshot, never interleaved.
Proof	snapshot_consistency theorem in ElderProofs.v (0 admits).

⸻

6 VALIDATOR FRAMEWORK

6.1 Dependency Graph & Conflict Resolution
	•	Each validator declares { id; phase; provides; requires; conflicts } in generated manifest/*.json.
	•	A static DAG is built at start‑up; cycles cause bootstrap failure.
	•	Conflicts resolve by priority tuple (severity, phase‑ordinal, id‑lexicographic).
	•	Proof: DAG acyclicity in ValidatorGraphProofs.v.

Rule catalog. The complete, version‑pinned list of 623 rules (IDs, preconditions, owners, proposed fixes) is maintained in rules.yaml and is authoritative for rule counts and IDs referenced throughout this plan.  

6.2 Priority & Execution
	•	Phases and batches follow the original design; L0 token passes run SIMD batch‑AC, L4 style runs mostly single‑threaded where document‑global context is required. (Details and counts unchanged.)

⸻

7 PROOF‑AUTOMATION & 0‑ADMIT POLICY

7.1 Strict Rule
	•	Zero admits in main at all times.
	•	Exception: up to 10 @proof‑debt axioms, each with a hard deadline; CI prints remaining budget (currently 0/10 used).  

7.2 Week‑1 Status
	•	Admits remaining: 0.
	•	Temporary axioms: 0.
	•	CI green on the zero‑admit gate.

7.3 Fuel‑Bound Policy (No permanent axioms)
	•	No permanent axioms for hash‑collision freedom or performance measurements.
	•	Hash‑collision lemma removed via design: content lines retained in hashes (§8).
	•	Performance obligations expressed as existential bounds until Week 5 measurements are recorded; then proofs point to measured artefacts.

7.4 Proof Template Catalogue
	•	14 templates cover 100 % of current validators.
	•	auto_solver tactic dispatches using manifest meta‑data. (Appendix D.)

⸻

8 PERFORMANCE ENGINEERING (TARGETS & METHOD)

Targets & gates (audit‑aligned).
	•	Full‑document p95 (perf_smoke ≈ 1.1 MB): < 25 ms target; 42 ms SLA gate in CI.
	•	Edit‑window p95 (4 KB): < 1 ms target and CI gate.
	•	Hardware baseline: M2‑Pro, ~3.5 GHz, 32 GiB RAM; median of 100 runs recorded and versioned with host fingerprint.  

Week‑1 measurement snapshot. perf_smoke p95 = 8.36 ms (baseline HW). (Edit‑window pipeline CI wiring complete; strict gate activates once calibration run lands in Week 5.)  

SIMD path.
	•	Rust implementations (core/l0_lexer/src/scan_simd.rs) with AVX‑512, NEON, and portable scalar fallback.
	•	Runtime feature detection via std::is_x86_feature_detected!; memory layout SoA with 64 B alignment, AoS fallback where needed.
	•	CI budget enforcement: performance gauge fails the gate on regression.  

Optimisation lanes.
	•	Pure OCaml lane to ~15 ms target (bigarray, domains, unsafe_get, simd_memcmp).
	•	C‑extension lane (optional) to ~2 ms if later mandated (AVX2 kernel, zero‑alloc, runtime fallback). (Decision deferred; only enabled if the 2 ms hard requirement is adopted.)  

Evidence & hand‑off docs: performance notes and audit trail captured in PERFORMANCE_OPTIMIZATION_HANDOFF.md, TECHNICAL_DEEP_DIVE.md, and FULL_AUDIT_REPORT.md.  

⸻

9 MULTI‑LANGUAGE SUPPORT
	•	I18n framework retained; 7 language packs integrated (en, fr, de, es, ja, zh, ar); 14 additional packs stubbed toward the 21‑language target.
	•	Validators parameterised by lang_code; per‑language thresholds and rules allowed.
	•	Cultural appropriateness uses a native‑speaker review queue. (Concern #4 mitigated.)

⸻

10 CORPUS & GROUND‑TRUTH STRATEGY
	•	Strategy A‑plus executed; cleanup script committed; repo size kept < 200 MB.
	•	External corpora locked via corpora.lock (SHA‑256 + S3 URL).
	•	CI job fetch_corpora stubbed until Week 6.
	•	Ground‑truth YAML schema finalised (Appendix F).  

⸻

11 SECURITY, SANDBOXING & SUPPLY‑CHAIN
	•	Reference seccomp policy at scripts/sandbox/seccomp.json.
	•	FFI boundaries wrapped via OCaml Ctypes foreign_value with runtime bounds checks.
	•	SBOM produced in CI with CycloneDX; releases signed with Cosign; public key in docs/SECURITY.md.  

⸻

12 DISTRIBUTED PROOF‑FARM & CI/CD
	•	Kubernetes Job template: infra/k8s/proof‑farm.yaml.
	•	Observability wired to Grafana via OpenTelemetry.
	•	Pre‑commit hook blocks commits introducing admits.  

⸻

13 DEVELOPMENT WORKFLOW & TOOLING
	•	VS Code + Coq‑LSP + OCaml‑LSP documented.
	•	dune watch for auto‑build; make quick for short‑circuit iterations.
	•	Pre‑commit: formatting, lint, admit‑count, repo‑size checks.  

⸻

14 PROJECT TIMELINE & MILESTONES

(All weeks are ISO‑weeks from project start 2025‑07‑28 = Week 1. Work‑streams can overlap; conflict is managed via focus‑day cadence.)

14.1 Timeline‑at‑a‑Glance (Quarterly)

Quarter	Major Objectives	Hard Gates
Q1 (Weeks 1–13)	Bootstrap skeleton; repo re‑structure; _CoqProject; L0 lexer prototype; CoreProofs at zero‑admit; CI skeleton	🎯 Week‑1 “Bootstrap” • 🎯 Week‑5 “Perf α” (p95 < 25 ms perf_smoke & edit‑window wired)
Q2 (14–26)	L1 macro expander + proofs; SIMD xxHash; validator DSL v1; proof‑farm infra; corpus cleanup Strategy A	🎯 Week‑10 “Proof β” • ◆ Week 26 L0‑L1 QED
Q3 (27–39)	Generator produces first 80 rules; generic proof templates; global p95 < 2 ms	📊 Week 23 SIMD target
Q4 (40–52)	L2 parser + splice proofs; PEG code‑gen tool; proof‑debt ≤ 10; p95 < 1.5 ms	🎯 Week 52 L2 delivered

(Q5–Q12 unchanged; see detailed schedule.)

14.2 Detailed Week‑by‑Week Schedule (key deliverables)

Note: Only Perf‑gate lines adjusted to new thresholds; all other rows unchanged from R0.

Wk	Sub‑system / Task	Marker	Exit Criteria
1	Repo restructure, _CoqProject, dune baseline	⬤⚙️	dune build green, admits = 0
2–3	Catcode module + proofs (Lexer)	⬤	Catcode.v QED, SIMD table stub
4	Chunk infra, xxHash scalar	⚙️📊	p95 < 40 ms
5	🎯 Perf α gate	🎯📊	p95 < 25 ms on perf_smoke; edit‑window pipeline wired (gate activates once calibrated); SIMD benches pass
6–8	Incremental Lexer proof (lexer_locality)	⬤	LexerIncremental.v 0 admits
9	SIMD xxHash (AVX, NEON)	📊	throughput ≥ 20 GB/s
10	🎯 Proof β gate	🎯	global admits ≤ 10
11–13	VPD compiler skeleton & first regex template	🤖	TYPO‑001 E2E passes
14–17	Macro expander (+ fuel proofs)	⬤	expand_no_teof QED
18	Proof‑farm k8s PoC	⚙️🤝	32 jobs parallel
19	Cache‑key spec & invalidation code	⚙️	Appendix B implementation
20	SIMD catcode scan	📊	6 × baseline
21	Validator conflict‑graph proto	🤝	DAG built, 0 cycles
22	Corpus cleanup script (Strategy A)	📚	repo size < 200 MB
23–25	Perf harness + Grafana	📊	dashboards live
26	◆ L0–L1 formal checkpoint	◆	lower‑layer admits 0
27–30	Generic proof tactics (RegexFamily)	⬤	auto‑proof < 50 ms/validator
31–35	ML span extractor training	🤖	F1 ≥ 0.94 dev
36–39	Generate 80 validators, conflict tests	◆	dune runtest passes, admits 0
40–41	PEG → OCaml code‑gen tool	⬤	parses 630‑line grammar
42	Arena allocator + proof of no‑move	🛡️	ArenaSound.v QED
43–45	Parser grammar tuning, 90 % corpus pass	📚	parse success metric
46	Dirty‑region detection suffix array	⚙️	O(log n) search proven
47	Consistency protocol proof	🎯	snapshot_consistency QED
48–49	Section renumber & rebalance		invariant proven
50	Security scan SBOM baseline	🛡️	sbom uploaded, 0 critical CVEs
51	Parser soundness proof		0 admits
52	🎯 L2 delivered gate	🎯◆	p95 < 1.2 ms end‑to‑end
53–57	Semantic reducer + label tables	⬤	labels_unique proved
58	Float tracking algorithm		float_distance unit tests
59	Diff algebra + merge proof		interp_locality QED
60–61	Proof‑debt burn‑down		budget ≤ 4
62	Live event bus API	⚙️	validators receive sem_delta
63	Lock‑free queue perf test	📊	8 M/s events
64	Integration with 80 validators	🤝	0 regressions
65	◆ L3 formal checkpoint	◆	admits lower 3 layers = 0
66–67	ICU + LangID bindings	🌐	split_preserves_order
68–70	Sentence splitter & benchmarks	🌐	50 MiB/s throughput
71	spaCy pipeline container	🤖	en/fr/de ready
72–74	STYLE primitives & 30 rules		admits 0
75	Evidence scoring framework		config file loaded
76	Incremental NLP diff engine		only changed sentences parsed
77	Perf tuning – p95 target	📊	p95 < 1 ms
78	🎯 Style α gate – 430 validators	🎯◆	global admits ≤ 8
79–85	HDBSCAN cluster & ML gen	🤖	400 pattern proposals
86–91	Proof‑farm scale to 128 jobs	⚙️	total time < 9 min
92–96	CJK + RTL pipelines	🌐	zh, ja, ar packs
97–101	Language‑specific validators	🌐	560 validators total
102–104	Corpus expansion + i18n test	📚🌐	language QA pass
105	ML confidence gating (≥ 0.95)	🤖	FPR ≤ 0.15 %
106–120	Continuous validator generation	🤖	623 count reached
121–125	Proof‑debt elimination sprint		admits ≤ 2
126–130	Deep audit & formal polish	🎯🛡️	proof‑debt = 0 gate
131–135	Parallel validator exec refactor	📊	p90 < 2 ms on 200 pages
136–140	Disaster‑recovery drills	🛡️	RTO ≤ 10 min reports
141–145	GPU off‑load prototype (optional)	📊	speed‑up report
146–150	Docs, tutorials, API site	📚	mkdocs build green
151–155	Release engineering, LTS branch	⚙️🎯	SBOM, signatures, installer
156	🎯 v25 General Availability	🎯◆	All KPIs; tag v25.0.0

14.3 Risk Buffers & Contingencies
	•	Two days per 4‑week block as Δ buffers.
	•	Freeze/bug‑burn weeks: 32, 88, 142.
	•	Proof‑debt deadline at Week 130 with four weeks slippage before GA.

14.4 Milestone Acceptance Check‑lists

Check‑lists live in docs/milestones/*.md; CI jobs milestone‑gate‑<id> enforce them.

Milestone	Key CI Steps
Bootstrap	build, lint, admits = 0, repo < 200 MB
Perf α	perf_smoke p95 < 25 ms; edit‑window pipeline wired; SIMD benches pass
Proof β	global admits ≤ 10; zero‑axiom except tagged debt
L2 delivered	parser soundness proof passes; parse success ≥ 95 % corpus
Style α	430 validators; style splitter proof QED; p95 < 1 ms
Proof‑debt 0	admit‑budget.json = 0; no @proof‑debt tags
GA	All KPIs; security & perf dashboards green; docs published

⸻

15 APPENDICES — Authoritative Enumeration (v25‑master)

All appendix sources live under docs/ and are built into docs/v25_master.pdf by make docs. For on‑boarding, A–G are bundled as Bootstrap Essentials. (The CI guard verifies table ↔ PDF parity; see below.)  

ID	Title (exact file name)	Length (pp)	Notes / artefacts
A	Glossary & Notation (appendix_A_glossary.tex)	8	Terminology, symbols, Unicode conventions.
B	Layer Interfaces & Data‑Structures (appendix_B_layer_interfaces.tex)	93	OCaml signatures + invariants for L0→L4 (“OCaml API spec”).
C	Validator DSL & Generator (appendix_C_validator_dsl.tex)	47	Grammar, code‑gen rules; auto‑generated SVG figs/validator_dag.svg.
D	Proof Template Catalogue (appendix_D_proof_templates.tex)	22	Reusable theorems/tactics; 87‑Q answers folded in.
E	SIMD Implementation Notes (appendix_E_simd_notes.tex)	11	AVX‑512 / NEON kernels; bench scripts.
F	Internationalisation & Unicode Strategy (appendix_F_i18n_unicode.tex)	97	CJK, RTL, Lang‑ID, ICU bindings; corpus scripts.
G	ML‑Assisted Pattern Pipeline & Extended Glossary (appendix_G_ml_pipeline.tex)	161	BERT→HDBSCAN→DSL flow; glossary deltas.
H	Advanced Proof‑Automation Cookbook (appendix_H_proof_cookbook.tex)	115	Ltac²/ELPI kernels; timing; CI tactics.
I	Incremental “Elder” Runtime Architecture (appendix_I_elder_runtime.tex)	72	Dependency DAG, snapshot protocol, scheduler proof.
J	Continuous‑Integration & Build Infrastructure (appendix_J_ci_build.tex)	14	Dune‑Coq layout; GH Actions matrix; Docker.
K	Reproducibility Cookbook & Tool‑chain Pins (appendix_K_reproducibility.tex)	7	Exact opam pins; Nix flakes; checksum table.
L	Road‑map & De‑scoped Ideas (appendix_L_roadmap.tex)	5	v26/27 forward‑looking items, gated features.

Build commands

make docs            # → docs/v25_master.pdf
make docs_bootstrap  # → docs/v25_bootstrap_essentials.pdf

CI guard (PDF/ToC parity).
The workflow in .github/workflows/ci.yml runs:

grep -E '^\appendix[A-L]' docs/v25_master.pdf | wc -l

and asserts == 13 occurrences to keep this table and the PDF in sync.  

Cross‑doc referencing. Use full ID letters (A–L) in citations, e.g., “See Appendix I §3.4 for the cache–snapshot proof.” For on‑boarding or Week‑1 notes, you may cite “Bootstrap Essentials (A–G)”—always spell out the letters.

⸻

Build & CI Automation (summary)
	•	CI badges include a residual‑risk heat‑map (turns red if any Residual ≥ 4).
	•	scripts/risk_heatmap.py renders the heat‑map.
	•	Core jobs:
proof‑ci (zero‑admit), perf‑ci (latency gates), sbom‑ci (security), milestone‑gate‑* (check‑lists).  

⸻

NEXT ACTIONS
	1.	Tag the repository: v25-R1-2025-07-31-audit-integrated.
	2.	Close/replace the R0 “Week‑1 debt burn‑down” issue with status complete (admits=0).  
	3.	Start the performance calibration run for the edit‑window path (Week 5 activation of strict 1 ms gate).  

⸻

End of v25_master.md (R1).
(Rules catalog lives in rules.yaml and is the authoritative source for rule IDs and counts referenced here.)  

⸻
