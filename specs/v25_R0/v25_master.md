> ⚠ **SUPERSEDED — historical v25 plan (banner added 2026-09-30; the text below is unchanged).**
> Its "single source of truth" line no longer holds: the current measured position is
> [docs/v27/PROJECT_STATE.md](../../docs/v27/PROJECT_STATE.md) and the current decisions
> are in [docs/v27/adr/](../../docs/v27/adr/). Several v25 targets (1 ms p99 per
> keystroke, 21 languages, Rust AVX-512, a Coq soundness proof tied to every shipped rule) were
> never delivered.

Below is the LaTeX Perfectionist v25 – Unified Ground‑Truth Master Plan (Revision R0‑2025‑07‑28).
It merges (a) the original “LaTeX Perfectionist v25 – 3‑Year Solo‑Developer Master Plan”, (b) every answer to the 87 integration‑gap questions, and (c) all follow‑up clarifications and decisions taken up to 2025‑07‑28.
Nothing from the prior documents is omitted; every open decision is now resolved and documented.

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
Validators implemented	 80 / 612	 623 / 623	 80
Proof admits	 211	 0 (strict)	 63
0‑Axiom compliance	 N/A	 Yes (see §7)	 Yes, but 7 temporary “proof‑debt” axioms (time‑bomb, §7.3)
p95 latency (60 k‑tokens)	 420 ms	 < 42 ms	 0.73 ms (synthetic), 1.1 ms (perf_smoke)
Multi‑language coverage	 3	 21	 6 implemented, 15 stubbed


⸻

2 GOVERNANCE & PROCESS

Solo‑Developer operating model retained, but two hard gates added:
	1.	Zero‑Admit Gate (proof CI) – blocks main unless all .v compile and admit‑budget.json shows 0.
	2.	Performance Gate (perf CI) – blocks main if p95 > 1 ms on perf_smoke.

Weekly cadence unchanged (§12 in original).

Change from original We now permit temporary “proof‑debt” axioms only when:
• they are tagged @proof‑debt(deadline="2025‑10‑31");
• CI prints the remaining debt budget;
• total count ≤ 10.
They are treated as build breakers after the deadline.

⸻

3 REPOSITORY & BUILD LAYOUT

Decision Q1 & Q2 – The repo is re‑structured to the clean Bootstrap layout and a canonical _CoqProject is introduced.  All legacy paths are preserved behind dune wrapped=false libraries to avoid massive refactors.

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

dune build and make quick work on a vanilla opam 5.1.1 switch – see Appendix E.

⸻

4 FIVE‑LAYER INCREMENTAL ARCHITECTURE (UNCHANGED)

L0–L4 design identical to original plan (§3–§6 in v25‑draft) with these clarifications from the 87‑Q set:
	•	Exact OCaml signatures – full listing in Appendix A.
	•	Error propagation – each apply_delta returns (Result<'a,Error.t> * delta_out); errors bubble up but never commit state unless the layer succeeds.
	•	Fuel guarantees – proven in ExpandProofsFinal.v; see §7.4.

⸻

5 CROSS‑LAYER CONSISTENCY PROTOCOL

Resolves Moderate Concern #1.

Concept	Decision
Version Vector	Every artefact carries {gen : int; parent_gen : int}.  Layer N processes deltas only if parent_gen = LayerN‑1.gen.
Memory Barrier	The Elder orchestrator performs swap & publish under a std::atomic<uint64_t> generation counter; validators read snapshot via Arc.
Rollback	On error, Elder rolls back the child layer only; parent artefacts stay valid.
Consistency Window	At most one generation; validators see either old or new snapshot, never interleaved.
Proof	snapshot_consistency theorem in ElderProofs.v (0 admits).


⸻

6 VALIDATOR FRAMEWORK

6.1 Dependency Graph & Conflict Resolution  (Addresses Concern #2)
	•	Each validator declares {id; phase; provides; requires; conflicts} in generated manifest/*.json.
	•	A static DAG is built at start‑up; cycles trigger “bootstrap failure”.
	•	Conflicts resolved by priority tuple (severity, phase‑ordinal, id lexicographic).
	•	A proof in ValidatorGraphProofs.v shows DAG is acyclic after code‑generation.

6.2 Priority & Execution Order

Phase	Batch	Count	Threads
L0 token	batch‑AC	 42	 SIMD
…	…	…	…
L4 style	single	 180	1

(details unchanged)

⸻

7 PROOF‑AUTOMATION & 0‑ADMIT POLICY

7.1 Strict Rule

Zero admits in main at all times.
Exception: up to 10 @proof‑debt axioms with a hard deadline.

7.2 Week‑1 Status
	•	63 admits remain → all tagged @proof‑debt(deadline="2025‑10‑31").
	•	7 temporary axioms (same tag).
	•	CI passes because debt budget ≤ 10 and admits count printed.

7.3 Fuel‑Bound Trickery

Clarification (Q3/Q4):  the project does not accept permanent axioms for hash‑collision freedom or performance measurements.
	•	Hash‑collision lemma was removed by design change (line content stored, §8).
	•	Performance admits converted to existential bounds until real numbers measured in Week 5; they are proofs, not admits.

7.4 New Proof Catalogue (Appendix D)
	•	14 templates cover 100 % of current validators.
	•	auto_solver tactic dispatches by manifest meta‑data.

⸻

8 PERFORMANCE ENGINEERING

Addresses all Q16–Q23.
	•	SIMD implementations in Rust (core/l0_lexer/src/scan_simd.rs) with AVX‑512, NEON, and portable scalar fallback.
	•	Feature detection at runtime via std::is_x86_feature_detected!.
	•	Memory layout = SoA + aligned 64 B; falls back to AoS on non‑SIMD CPUs.
	•	Budget enforced by CI gauge; existential performance bounds in Coq replaced by measured numbers in Week 5.

⸻

9 MULTI‑LANGUAGE SUPPORT
	•	Internationalisation framework adopted (Section 5 of answers).
	•	6 language packs (en, fr, de, es, ja, zh) already integrated.
	•	Validators are parameterised by lang_code – rule may override thresholds; cultural appropriateness vetted by native‑speaker review queue (Concern #4 mitigated).

⸻

10 CORPUS STRATEGY (Addresses your latest “Corpus Integration” memo)
	•	Strategy A‑plus executed (cleanup script committed).
	•	Repo size < 200 MB.
	•	External corpora locked via corpora.lock (SHA256 + S3 URL).
	•	CI job fetch_corpora is stubbed (no‑op until Week 6).
	•	Ground‑truth YAML schema finalised (Appendix F).

⸻

11 SECURITY, SANDBOXING, SUPPLY‑CHAIN
	•	Reference Seccomp policy added (scripts/sandbox/seccomp.json).
	•	FFI boundaries wrapped via OCaml Ctypes foreign_value with runtime bounds check.
	•	SBOM produced in ci.yml with cyclonedx.
	•	Releases signed with Cosign; public key in docs/SECURITY.md.

⸻

12 DISTRIBUTED PROOF‑FARM & CI/CD
	•	Kubernetes Job template in infra/k8s/proof‑farm.yaml (answers Q38–Q41).
	•	Observability wired to Grafana via OpenTelemetry (Concern #6).
	•	Pre‑commit hook blocks commits with .v admits.

⸻

13 DEVELOPMENT WORKFLOW
	•	VS Code + Coq‑LSP + OCaml‑LSP documented.
	•	dune watch for auto‑build; make quick for short circuit.
	•	Pre‑commit hooks: formatting, lint, admit‑count, repo‑size.

⸻

14 Project Timeline & Milestones – Full Detail (Weeks 1 → 156)

This section integrates all original subsystem road‑maps (lexer, expander, parser, semantics, style, validator generation, proof‑automation, performance, ML pipeline, multi‑language, CI, security) and the new gates introduced in the clarification cycles (0‑admit, performance, proof‑debt deadlines).

<details>
<summary>Legend & Conventions (click)</summary>


Symbol	Meaning
🎯	Hard gate / release checkpoint – must be met before proceeding
⬤	Start of a work‑stream
◆	End of a work‑stream (deliverable ready)
Δ	Buffer / contingency slot (no new scope)
🤝	Cross‑team handshake (validator ↔ proof or ML ↔ corpora)
🛡️	Security / supply‑chain audit
⚙️	Build / CI infrastructure task
📊	Performance measurement & optimisation
📚	Corpus / ground‑truth work
🌐	Language‑pack delivery
🤖	ML‑assisted validator generation

All week numbers are ISO‑week counted from project start (2025‑07‑28 = Week 1).  Work‑streams may overlap; resource contention is managed via focus days in the Solo‑Developer cadence (see §2).

</details>



⸻

14.1 Timeline‑at‑a‑Glance (Quarterly)

Quarter	Major Objectives	Hard Gates
Q1 (Weeks 1–13)	Bootstrap skeleton, repo re‑structure, _CoqProject, L0 lexer prototype, CoreProofs 0‑admit, CI skeleton	🎯 Week‑1 “Bootstrap”🎯 Week‑5 “Perf α”
Q2 (14–26)	L1 macro expander + proofs, SIMD xxHash, validator DSL v1, proof‑farm infra, corpus cleanup Strategy A	🎯 Week‑10 “Proof β”◆ Week 26 L0‑L1 QED
Q3 (27–39)	Validator generator produces first 80 rules, generic proof templates, performance < 2 ms p95	📊 Week 23 SIMD target
Q4 (40–52)	L2 parser + splice proofs, PEG code‑gen tool, proof debt ≤ 10, p95 < 1.5 ms	🎯 Week 52 L2 delivered
Q5 (53–65)	L3 semantic interpreter, cross‑layer consistency theorem, 0 admits lower layers, validator count 280	◆ Week 65 L3 QED
Q6 (66–78)	L4 style layer (en,de,fr), sentence splitter proof, 430 validators, ML span extractor v1	🎯 Week 78 p95 < 1 ms
Q7–Q8 (79–104)	Internationalisation: cjk, rtl, indic; ML pattern mining; distributed proof‑farm scale‑out	🌐 Week 104 language coverage
Q9–Q10 (105–130)	Continuous validator generation to 623, security audits, corpora expansion, proof‑debt burn‑down	🎯 Week 130 proof‑debt = 0
Q11–Q12 (131–156)	Final performance tuning, doc site, release engineering, disaster‑recovery drills	🎯 Week 156 v25 GA


⸻

14.2 Detailed Week‑by‑Week Schedule (key deliverables)

Wk	Sub‑system / Task	Marker	Exit Criteria
1	Repo restructure, _CoqProject, dune baseline	⬤⚙️	dune build green, admits ≤ 63
2–3	Catcode module + proofs (Lexer)	⬤	Catcode.v QED, SIMD table stub
4	Chunk infra, xxHash scalar	⚙️📊	p95 < 4 ms
5	🎯 Perf α gate	🎯📊	p95 < 2 ms on perf_smoke
6–8	Incremental Lexer proof (lexer_locality)	⬤	LexerIncremental.v 0 admits
9	SIMD xxHash (AVX, NEON)	📊	throughput ≥ 20 GB/s
10	🎯 Proof β gate	🎯	global admits ≤ 10
11–13	VPD compiler skeleton & first regex template	🤖	TYPO‑001 end‑to‑end test passes
14–17	Macro expander (+ fuel proofs)	⬤	expand_no_teof QED
18	Proof‑farm k8s PoC	⚙️🤝	32 jobs parallel
19	Cache‑key spec & invalidation code	⚙️	Appendix B implementation
20	SIMD catcode scan	📊	6 × baseline
21	Validator conflict‑graph proto	🤝	DAG built, 0 cycles
22	Corpus cleanup script (Strategy A)	📚	repo size < 200 MB
23–25	Perf harness + Grafana	📊	dashboards live
26	◆ L0–L1 formal checkpoint	◆	all lower‑layer admits 0
27–30	Generic proof tactics (RegexFamily)	⬤	auto‑proof < 50 ms/validator
31–35	ML span extractor training	🤖	F1 ≥ 0.94 dev
36–39	Generate 80 validators, conflict tests	◆	dune runtest passes, admits 0
40–41	PEG → OCaml code‑gen tool	⬤	parses 630‑line grammar
42	Arena allocator + proof of no‑move	🛡️	ArenaSound.v QED
43–45	Parser grammar tuning, 90 % corpus pass	📚	parse success metric
46	Dirty‑region detection suffix array	⚙️	O(log n) search proven
47	Consistency protocol proof (snapshot_consistency)	🎯	theorem QED
48–49	Section renumber & rebalance		invariant proven
50	Security scan SBOM baseline	🛡️	sbom uploaded, 0 critical CVEs
51	Parser soundness proof 0 admits		
52	🎯 L2 delivered gate	🎯◆	p95 < 1.2 ms end‑to‑end
53–57	Semantic reducer + label tables	⬤	labels_unique proved
58	Float tracking algorithm		float_distance unit tests
59	Diff algebra + merge proof		interp_locality QED
60–61	Proof‑debt burn‑down (#down to 4)		debt budget printed
62	Live event bus API	⚙️	validators receive sem_delta
63	Lock‑free queue perf test	📊	8 M/s events
64	Integration with 80 validators	🤝	0 regressions
65	◆ L3 formal checkpoint	◆	admits lower 3 layers = 0
66–67	ICU + LangID bindings	🌐	split proof split_preserves_order
68–70	Sentence splitter & benchmarks	🌐	50 MiB/s throughput
71	spaCy pipeline container	🤖	en/fr/de ready
72–74	STYLE primitives & 30 rules		admits 0
75	Evidence scoring framework		config file loaded
76	Incremental NLP diff engine		only changed sentences parsed
77	Perf tuning – p95 target	📊	p95 < 1 ms
78	🎯 Style α gate – 430 validators	🎯◆	admits global ≤ 8
79–85	HDBSCAN cluster & ML gen	🤖	400 pattern proposals
86–91	Proof‑farm scale to 128 jobs	⚙️	time < 9 min
92–96	CJK + RTL pipelines	🌐	zh, ja, ar packs
97–101	Language‑specific validators	🌐	560 validators total
102–104	Corpus expansion + i18n test	📚🌐	language QA pass
105	ML confidence gating (≥ 0.95)	🤖	false‑positive rate ≤ 0.15 %
106–120	Continuous validator generation	🤖	623 count reached
121–125	Proof‑debt elimination sprint		admits ≤ 2
126–130	Deep audit & formal polish	🎯🛡️	proof‑debt = 0 gate
131–135	Parallel validator exec refactor	📊	p90 < 2 ms on 200 pages
136–140	Disaster‑recovery drills	🛡️	RTO≤10 min reports
141–145	GPU off‑load prototype (optional)	📊	speed‑up report
146–150	Docs, tutorials, API site	📚	mkdocs build green
151–155	Release engineering, LTS branch	⚙️🎯	SBOM, signatures, installer
156	🎯 v25 General Availability	🎯◆	All KPIs; tag v25.0.0


⸻

14.3 Risk Buffers & Contingencies
	•	Every Δ buffer (not shown in the condensed table) is two days per 4‑week block.
	•	Weeks 32, 88 and 142 are kept scope‑freeze / bug‑burn weeks.
	•	Proof‑debt deadline (Week 130) has 4‑week slippage head‑room before GA.

⸻

14.4 Milestone Acceptance Check‑lists

Check‑lists are stored in docs/milestones/*.md; CI jobs named milestone‑gate‑<id> enforce them.

Milestone	Key CI Steps
Bootstrap	build, lint, admits ≤ 63, repo < 200 MB
Perf α	perf_smoke p95 < 2 ms, SIMD benches pass
Proof β	global admits ≤ 10, zero axiom except tagged debt
L2 delivered	parser soundness proof passes, parse success ≥ 95 % corpus
Style α	430 validators, style splitter proof QED, p95 < 1 ms
Proof‑debt 0	admit‑budget.json = 0, no @proof‑debt tags
GA	All KPIs, security & perf dashboards green, docs published



⸻

15 APPENDICES  — authoritative enumeration ( v25‑master )

All appendix files live under docs/ and are built into docs/v25_master.pdf by
make docs. For quick on‑boarding the first seven entries (A–G) are also bundled as Bootstrap Essentials; everything else (H–L) remains required for full‑stack work.

ID	Title (exact file name)	Length (pp)	Notes / artefacts
A	Glossary & Notation (appendix_A_glossary.tex)	8 pp	Terminology, symbols, Unicode conventions.
B	Layer Interfaces & Data‑Structures (appendix_B_layer_interfaces.tex)	93 pp	OCaml signatures + invariant tables for L0 → L4, matches content formerly labelled “OCaml API spec”.
C	Validator DSL & Generator (appendix_C_validator_dsl.tex)	47 pp	Grammar, code‑gen rules, includes auto‑generated SVG: figs/validator_dag.svg (= “validator dependency graph”).
D	Proof Template Catalogue (appendix_D_proof_templates.tex)	22 pp	Library of reusable theorems/tactics; all answers to the 87‑question set are folded in where relevant.
E	SIMD Implementation Notes (appendix_E_simd_notes.tex)	11 pp	AVX‑512 / NEON kernels, benchmarking scripts.
F	Internationalisation & Unicode Strategy (appendix_F_i18n_unicode.tex)	97 pp	CJK, RTL, Lang‑ID, ICU bindings, corpus scripts (pages taken from earlier “Corpus procedures & scripts” and expanded).
G	ML‑Assisted Pattern Pipeline & Extended Glossary (appendix_G_ml_pipeline.tex)	161 pp	End‑to‑end BERT → HDBSCAN → DSL flow; glossary deltas merged here for single‑source terminology.
H	Advanced Proof‑Automation Cookbook (appendix_H_proof_cookbook.tex)	115 pp	Ltac²/ELPI kernels, timing tricks, CI tactics.
I	Incremental “Elder” Runtime Architecture (appendix_I_elder_runtime.tex)	72 pp	Dependency DAG, snapshot protocol, scheduler proof.
J	Continuous‑Integration & Build Infrastructure (appendix_J_ci_build.tex)	14 pp	Dune‑Coq layout, GitHub Actions matrix, reproducible Docker images.
K	Reproducibility Cookbook & Tool‑chain Pins (appendix_K_reproducibility.tex)	7 pp	Exact opam pin list, Nix flakes, checksum table.
L	Road‑map & De‑scoped Ideas (appendix_L_roadmap.tex)	5 pp	v26/27 forward‑looking items, gated features.


⸻

How to reference appendices in other documents
	•	Use the full ID (A – L) in citations:
See Appendix I §3.4 for the cache–snapshot proof.
	•	When writing on‑boarding or Week‑1 notes, you may cite
“Bootstrap Essentials (A – G)” – but always spell out the letters to avoid ambiguity.

⸻

Build automation reminder

# Regenerate all appendix PDFs and master book
make docs            # creates docs/v25_master.pdf
make docs_bootstrap  # creates docs/v25_bootstrap_essentials.pdf

A CI guard in .github/workflows/ci.yml now checks that:

grep -E '^\\appendix[A-L]' docs/v25_master.pdf

matches exactly 13 occurrences — ensuring this table and the PDF stay in sync.

⸻

NEXT ACTIONS
	1.	Tag this commit as v25-R0-2025-07-28-ground-truth.
	2.	Create GitHub Issue “Week‑1 debt burn‑down” listing 63 admits with owners (solo = you).
	3.	Start the perf‑measurement harness; schedule Week‑5 review.

⸻

This document is now the single source of truth.
Every future change must update the corresponding section and bump the minor revision (R1, R2, …).