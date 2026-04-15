# LaTeX Perfectionist — Repo-Exact Missing Architecture Memo

**Date:** 2026-04-14  
**Audit basis:** uploaded repository snapshot `latex_perf_v25.0.0.zip`  
**Target audience:** Dylan / core maintainer / external expert / future coding agents  
**Purpose:** identify the architecture that is still missing between the current v25 system and the end-state product: a provable, real-time LaTeX authoring platform with compilation guarantees and full rule enforcement, suitable to outcompete Overleaf for expert users, editors, and institutions.

---

## 0. Executive conclusion

The repository shows that v25 is **not** merely a plan or a linter prototype. It is already a serious, high-performance, proof-bearing analysis engine with:

- real lexical/SIMD machinery,
- real generated rule proofs,
- real chunk-store incremental machinery,
- real binary/file validators,
- real compile-log parsing,
- real ML artefacts,
- real CI/release/security plumbing.

However, the repository also makes the missing end-state architecture unmistakable.

> **What is still missing is not “more rules” or “more speed”. It is the architecture above the engine:**
>
> 1. a **formal language contract**;
> 2. a **formal project/build model**;
> 3. a **formal semantics for incomplete documents under editing**;
> 4. a **lossless editing / rewrite representation**;
> 5. a **hybrid invalidation graph**;
> 6. a **real dependency graph for validators and build artefacts**;
> 7. a **trustworthy public truth surface**;
> 8. an **editorial/collaboration platform layer**.

Until those exist, the project remains an exceptional verified LaTeX analysis kernel, but not yet the provable Overleaf-class platform you actually want.

---

## 1. Audit scope and evidence base

This memo is **repo-exact**, not merely briefing-based.

The assessment below is based on the uploaded snapshot and direct inspection of these parts of the tree:

- `latex-parse/src/**`
- `core/**`
- `proofs/**`
- `specs/**`
- `docs/**`
- `.github/workflows/**`
- `governance/**`
- top-level release/build files

The most salient evidence points are:

- `specs/rules/rules_v3.yaml`
- `README.md`
- `docs/index.md`
- `CHANGELOG.md`
- `proofs/generated/Catalogue.v`
- `latex-parse/src/edf_scheduler.ml`
- `latex-parse/src/chunk_store.ml`
- `latex-parse/src/semantic_state.ml`
- `latex-parse/src/parser_l2.ml`
- `latex-parse/src/log_parser.ml`
- `latex-parse/src/validators.ml`

---

## 2. The current system, accurately stated

The current repository contains:

### 2.1 What already exists in substance

1. **A real multi-layer analysis engine**
   - lexical tokenization,
   - macro expansion,
   - source parser,
   - semantic extraction/state,
   - validator orchestration,
   - style/NLP layer.

2. **A serious proof substrate**
   - hand-written core proofs,
   - generated per-rule proof files,
   - proof family infrastructure,
   - ML soundness-style theorem,
   - zero-admit discipline in the proof tree.

3. **A real incremental substrate**
   - paragraph chunking,
   - hash-based chunk identity,
   - cached results,
   - scheduled execution,
   - partial bypasses and re-evaluation paths.

4. **A real systems substrate**
   - C/SIMD tokenizer path,
   - broker/worker/hedge-timeout machinery,
   - REST and CLI surfaces,
   - Prometheus metrics,
   - CI/release/security tooling.

5. **A meaningful semantic/file-analysis surface**
   - refs/labels,
   - file-context threading,
   - PNG/JPEG/PDF/font analysis,
   - compile-log parsing.

### 2.2 What it is not yet

It is **not yet**:

- a formally delimited language implementation with named support tiers;
- a compilation-guarantee system for projects;
- a lossless real-time editing substrate with partial-document semantics;
- a first-class multi-file build/project model;
- a collaboration/editorial product platform;
- a coherent public truth surface.

That is the gap to close.

---

## 3. The most urgent structural defect: the truth surface is drifting

This is now a first-order architecture/governance problem.

### 3.1 Rule counts are not canonical across the repo

The repository currently contains multiple incompatible public numbers.

#### Evidence

- `specs/rules/rules_v3.yaml` header says **623 rules**.
- The same file contains **642** `id:` entries.
- The same file contains **16** entries with `maturity: Reserved`, implying **626 non-reserved** entries.
- `README.md` says **627 rule IDs / 642 spec**.
- `docs/index.md` says **568 / 623 implemented**.

### 3.2 Proof counts are not canonical either

#### Evidence

- `README.md` says **626 per-rule soundness (606 faithful, 20 conservative)**.
- `docs/PROOF_GUIDE.md` repeats **606 faithful / 20 conservative**.
- `docs/index.md` says **607 soundness theorems (26 faithful, 581 conservative)**.
- `proofs/generated/Catalogue.v` says **626 rules with soundness proofs**.

### 3.3 Maturity semantics are drifting

Inside `rules_v3.yaml` the maturity distribution is effectively:

- `Draft`: 607
- `Implemented`: 19
- `Reserved`: 16

This conflicts with the briefing language that presents 626 as implemented.

### 3.4 Release state drifts too

#### Evidence

- project story says v25.0.0 released,
- but `CHANGELOG.md` top entry is `v25.0.0-rc1`.

### 3.5 Why this matters

A system cannot claim strong guarantees if users cannot tell which numbers are authoritative.

### 3.6 Required architecture fix

Create a single generated **canonical facts contract**, e.g.

- `generated/project_facts.json`
- `generated/project_facts.yaml`

and derive from it:

- README summary table,
- docs homepage metrics,
- changelog release header,
- proof dashboard counts,
- support matrix,
- CI assertions.

### 3.7 Required CI gate

Add `ci/spec_drift.yml` that recomputes and checks:

- total rule count,
- non-reserved rule count,
- faithful/conservative/statistical counts,
- theorem count,
- workflow count,
- language pack count,
- current release/tag.

If any public document disagrees, build fails.

---

## 4. Missing architecture #1: a formal language contract

This is the deepest conceptual omission.

The project still lacks a **named, versioned, formal contract** stating what “LaTeX” means for the purposes of guarantees.

### 4.1 Why this is necessary

The desired end-state claim is not merely:

> “we lint LaTeX very well.”

It is:

> “we provide real-time, proved guarantees about parsing, rule enforcement, and eventual compilability, on a strict but practical LaTeX subset.”

That requires a language boundary.

### 4.2 What the contract must define

A new first-class spec document is required. Suggested path:

- `specs/v26/language_contract.md`
- `specs/v26/language_contract.yaml`

### 4.3 Required tiers

#### LP-Core
The fully guaranteed subset.

Must specify:

- supported engines and engine profiles;
- syntax admitted by the parser;
- macro subset admitted by the expander;
- packages/classes admitted under guarantees;
- supported math/environment subset;
- supported file graph constructs;
- supported generated artefacts;
- forbidden constructs;
- proof claims available.

#### LP-Extended
Practical but not fully proved.

Must specify:

- contract-tested extensions,
- extractor-based semantics,
- downgraded claims,
- explicit failure modes,
- sandbox requirements.

#### LP-Foreign
Unsupported / external / non-guaranteed domain.

Examples:

- shell escape,
- arbitrary external preprocessors,
- unrestricted TeX metaprogramming,
- dynamic catcode wizardry,
- exotic conditional programming.

These must either:

- be rejected in guaranteed mode, or
- be accepted only behind an explicit “non-guaranteed extension” boundary.

### 4.4 Required outputs

The language contract must produce machine-readable data consumed by:

- parser tests,
- macro registry,
- support matrix,
- UI diagnostics,
- documentation,
- CI profile gates.

### 4.5 Concrete files to create

**New:**
- `specs/v26/language_contract.md`
- `specs/v26/language_contract.yaml`
- `latex-parse/src/language_profile.ml`
- `latex-parse/src/language_profile.mli`
- `latex-parse/src/unsupported_feature.ml`
- `latex-parse/src/unsupported_feature.mli`

**Rewrite:**
- `README.md`
- `docs/index.md`
- `docs/ARCH.md`
- `docs/PROOFS.md`
- `docs/PROOF_GUIDE.md`

---

## 5. Missing architecture #2: the compilation guarantee theorem stack

You do not yet have the theorem the final product actually needs.

### 5.1 What you have now

The repo currently supports strong statements about:

- lexical correctness,
- expansion correctness,
- parser soundness,
- semantic consistency of some extracted structures,
- rule-level soundness,
- conservative wrappers for file-based rules.

### 5.2 What is still missing

You need a theorem family of the form:

> For projects in `LP-Core(engine, profile)`, if parsing succeeds, all required artefacts resolve, macro registration is accepted, the project DAG is closed, and all Error-level rules pass, then compilation succeeds under the selected build profile and yields a well-formed output artefact.

### 5.3 This is not one theorem

It is a theorem **stack**.

#### T0 — Parser acceptance theorem
If source is in `LP-Core`, parser accepts and produces CST/AST.

#### T1 — Expansion admissibility theorem
For admissible user/builtin macros, expansion terminates and preserves language admissibility.

#### T2 — Project closure theorem
The project include/build graph is finite, acyclic where required, and all required assets resolve.

#### T3 — Build profile admissibility theorem
The selected engine/toolchain profile is compatible with the project’s declared features.

#### T4 — Semantic state coherence theorem
Global semantic state over project files is consistent (labels, refs, counters, bibliography, float metadata, etc.).

#### T5 — Rule safety theorem
If no Error-level rule fires within its proof class/contract class, no statically detectable violation remains inside the contract.

#### T6 — Compilation progress theorem
Given T0–T5 and bounded build assumptions, the project compiles without fatal errors.

#### T7 — Output well-formedness theorem
Produced artefacts satisfy the subset’s output contract (e.g., valid PDF graph, no missing refs, etc., within scope).

### 5.4 What this implies for implementation

You need a new first-class subsystem representing:

- projects,
- build profiles,
- auxiliary artefacts,
- toolchain passes,
- fixed-point / pass iteration semantics.

### 5.5 Concrete files to create

**New specs:**
- `specs/v26/compilation_guarantee_stack.md`
- `specs/v26/compilation_profiles.yaml`

**New runtime modules:**
- `latex-parse/src/project_model.ml`
- `latex-parse/src/project_model.mli`
- `latex-parse/src/build_profile.ml`
- `latex-parse/src/build_profile.mli`
- `latex-parse/src/build_graph.ml`
- `latex-parse/src/build_graph.mli`
- `latex-parse/src/aux_state.ml`
- `latex-parse/src/aux_state.mli`
- `latex-parse/src/compile_contract.ml`
- `latex-parse/src/compile_contract.mli`

**New proofs:**
- `proofs/ProjectClosure.v`
- `proofs/BuildProfileSound.v`
- `proofs/CompileProgress.v`
- `proofs/CompileWellFormed.v`

---

## 6. Missing architecture #3: formal semantics for incomplete documents under editing

Because the target is **real-time while editing**, not just batch correctness.

### 6.1 Current situation

The parser supports error accumulation and partial continuation, but there is no formal editing-state model.

### 6.2 Missing formal objects

You need:

- partial CST/AST with holes,
- damage containment semantics,
- repair monotonicity,
- stable semantic shadow outside local edit neighbourhoods,
- explicit trust zones during broken states.

### 6.3 Required theorem family

#### E0 — Partial parse locality theorem
A local source edit cannot invalidate trusted parse structure outside a bounded region except via declared dependency edges.

#### E1 — Damage containment theorem
Malformed local structure produces bounded untrusted regions, not global semantic collapse.

#### E2 — Repair monotonicity theorem
Repairing a local syntax error restores prior trusted regions monotonically unless the edit crosses dependency boundaries.

#### E3 — Stable identifier theorem
Stable node IDs persist across local edits where CST identity is preserved.

### 6.4 Why this matters

Without these theorems, you can still build a very good incremental editor, but you cannot honestly claim a **perfect real-time parser under live editing**.

### 6.5 Concrete files to create

**New specs:**
- `specs/v26/partial_document_semantics.md`
- `specs/v26/partial_document_semantics.yaml`

**New runtime modules:**
- `core/l2_parser/partial_cst.ml`
- `core/l2_parser/partial_cst.mli`
- `core/l2_parser/error_recovery.ml`
- `core/l2_parser/error_recovery.mli`
- `latex-parse/src/trust_regions.ml`
- `latex-parse/src/trust_regions.mli`

**New proofs:**
- `proofs/PartialParseLocality.v`
- `proofs/DamageContainment.v`
- `proofs/RepairMonotonicity.v`
- `proofs/StableNodeIds.v`

---

## 7. Missing architecture #4: a lossless representation stack (CST)

The current shipped stack is effectively:

- source string,
- token-ish lexical structures,
- AST/document structure,
- semantic/file contexts.

For the intended end-state, this is not enough.

### 7.1 Why a CST is required

A high-end editor / editorial system needs:

- comment preservation,
- whitespace preservation,
- formatting-stable rewrites,
- exact round-trips,
- stable anchors for comments/track changes,
- proof-carrying rewrites.

### 7.2 Required representation stack

You need a five-layer representational stack:

1. **byte/token stream**
2. **lossless CST**
3. **semantic AST**
4. **project graph**
5. **build artefact graph**

### 7.3 Required translation contracts

- token stream → CST (total on admitted subset)
- CST → AST (semantic abstraction)
- AST/project graph → semantic state
- rewrites AST/CST → source round-trip preserving comments/spacing where promised

### 7.4 Concrete files to create or rewrite

**New:**
- `core/l2_parser/cst.ml`
- `core/l2_parser/cst.mli`
- `core/l2_parser/cst_builder.ml`
- `core/l2_parser/cst_builder.mli`
- `latex-parse/src/rewrite_engine.ml`
- `latex-parse/src/rewrite_engine.mli`
- `latex-parse/src/stable_spans.ml`
- `latex-parse/src/stable_spans.mli`

**Rewrite:**
- `latex-parse/src/parser_l2.ml`
- `proofs/ParserSound.v`

**New proofs:**
- `proofs/CSTRoundTrip.v`
- `proofs/CSTtoASTSound.v`
- `proofs/RewritePreservesCST.v`

---

## 8. Missing architecture #5: a project/build model

This is the biggest practical substrate gap.

### 8.1 Current state

The repo supports single-document analysis plus auxiliary contexts. It does not yet contain a first-class project graph.

### 8.2 What the project model must include

- file DAG for `\input`, `\include`, `\includeonly`,
- path-resolution rules,
- per-file CST/AST,
- global semantic projection,
- aux/bbl/toc/index/glossary/log/bcf/run.xml artefact tracking,
- bibliography state,
- engine/profile configuration,
- cache invalidation across file edges,
- project-level diagnostics.

### 8.3 New runtime subsystem

Suggested directory:

- `core/project/`

with modules:

- `include_graph.ml`
- `file_resolution.ml`
- `project_session.ml`
- `artifact_graph.ml`
- `bibliography_state.ml`
- `glossary_state.ml`
- `index_state.ml`
- `project_semantics.ml`

### 8.4 Proof obligations

- include graph closure,
- no unsupported cycles,
- semantic projection consistency,
- build artefact dependency soundness,
- invalidation correctness across project edges.

### 8.5 Concrete files to create

**New:**
- `core/project/dune`
- `core/project/include_graph.ml`
- `core/project/file_resolution.ml`
- `core/project/project_session.ml`
- `core/project/artifact_graph.ml`
- `latex-parse/src/project_runner.ml`
- `latex-parse/src/project_runner.mli`

**New proofs:**
- `proofs/IncludeGraphSound.v`
- `proofs/ProjectSemantics.v`
- `proofs/ArtifactGraphSound.v`

---

## 9. Missing architecture #6: hybrid invalidation / dependency graph

Current paragraph chunking is correct for v25.

It is not sufficient for the final platform.

### 9.1 Current repo state

- paragraph-based chunking,
- xxh64 hash over chunk content + catcode vector,
- cache reuse,
- whole-source fallback for cross-chunk rules.

### 9.2 Required evolution

Keep paragraph chunking as the **cache/storage unit**.

Add three invalidation planes:

#### Syntactic plane
- environment spans,
- math spans,
- section spans,
- float spans,
- macro-definition spans.

#### Semantic plane
- label ↔ ref edges,
- counter ↔ section/float edges,
- cite ↔ bibliography key edges,
- package/class ↔ rule enablement edges.

#### Project plane
- include edges,
- generated-artefact dependencies,
- build-profile dependencies.

### 9.3 Required runtime modules

**New:**
- `latex-parse/src/dependency_graph.ml`
- `latex-parse/src/dependency_graph.mli`
- `latex-parse/src/invalidation_engine.ml`
- `latex-parse/src/invalidation_engine.mli`
- `latex-parse/src/semantic_edges.ml`
- `latex-parse/src/semantic_edges.mli`

**Rewrite:**
- `latex-parse/src/chunk_store.ml`
- `latex-parse/src/validators.ml`
- `latex-parse/src/edf_scheduler.ml`

### 9.4 Required proofs

- paragraph cache correctness,
- dependency invalidation soundness,
- no missed affected-node theorem,
- locality bound under edit theorem.

---

## 10. Missing architecture #7: a real validator dependency graph

The repo contains a DAG framework, but runtime semantics are still mostly defaulted.

### 10.1 Current evidence

`latex-parse/src/validators.ml` constructs DAG metadata via `Validator_dag.default_meta` for all rules.

### 10.2 What is missing

The actual system needs explicit per-rule metadata describing:

- what semantic artefacts a rule consumes,
- what fixes it can produce,
- which rules it blocks or depends on,
- which execution class it belongs to,
- whether it is proof-faithful, conservative, or statistical.

### 10.3 Required machine-readable manifest

New canonical manifest:

- `specs/rules/rule_contracts.yaml`

For every rule:

- `rule_id`
- `phase`
- `execution_class`
- `proof_class`
- `evidence_class`
- `consumes`
- `provides`
- `depends_on`
- `conflicts_with`
- `fix_scope`
- `project_scope`

### 10.4 Required runtime changes

**Rewrite:**
- `latex-parse/src/validators_common.ml`
- `latex-parse/src/validators.ml`
- `latex-parse/src/validator_dag.ml`

**New:**
- `latex-parse/src/rule_contract_loader.ml`
- `latex-parse/src/rule_contract_loader.mli`

**Proofs:**
- strengthen `proofs/ValidatorGraphProofs.v`

---

## 11. Missing architecture #8: execution classes

The end-state system cannot run everything in the same way.

### 11.1 Required execution classes

#### Class A — keystroke-critical
Fast, deterministic, local, exact.

Examples:
- lexical/encoding/spacing/typo,
- local delimiter/mode checks.

#### Class B — debounce semantic
Deterministic, semantic, not necessarily every keystroke.

Examples:
- refs/labels,
- structural package/class checks,
- some math/section/floats.

#### Class C — build-coupled
Requires logs, binaries, or generated artefacts.

Examples:
- PDF/PNG/JPEG/font,
- LAY/PAGE rules,
- compile-log-driven diagnostics.

#### Class D — heuristic/advisory
Style, ML, language heuristics, confidence-weighted.

### 11.2 Required repo changes

**New:**
- `latex-parse/src/execution_class.ml`
- `latex-parse/src/execution_class.mli`
- `latex-parse/src/execution_policy.ml`
- `latex-parse/src/execution_policy.mli`

**Rewrite:**
- `latex-parse/src/validators.ml`
- `latex-parse/src/evidence_scoring.ml`
- `latex-parse/src/edf_scheduler.ml`

This is a prerequisite for adding richer v26 analysis without hurting the hot path.

---

## 12. Missing architecture #9: support matrix and trust model

The repo still lacks one authoritative support contract.

### 12.1 Required document

Create:

- `docs/SUPPORT_MATRIX.md`
- `docs/SUPPORT_MATRIX.yaml`

### 12.2 It must state, explicitly

- supported engines,
- supported document classes,
- supported packages/classes under guarantees,
- supported macro subset,
- supported artefacts,
- supported interfaces,
- live vs stubbed language packs,
- experimental vs guaranteed features,
- per-rule-family proof class.

### 12.3 Why this matters

A strict, explicit support matrix increases trust among expert users. An unclear support matrix destroys it.

---

## 13. Missing architecture #10: editorial policy layer

If the target users include editors and perfectionists, rules are not enough.

### 13.1 Required product layer

You need a policy/editorial layer supporting:

- named house-style profiles,
- severity remapping by profile,
- waivers/exceptions,
- scope-limited suppressions,
- justification storage,
- review ownership,
- audit trails,
- project-wide reports,
- “what changed since last review” summaries.

### 13.2 Required new subsystem

Suggested directory:

- `core/editorial/`

with modules:

- `policy_profile.ml`
- `waiver_store.ml`
- `exception_scope.ml`
- `review_state.ml`
- `reporting.ml`

### 13.3 Required machine-readable artefacts

- `specs/v26/editorial_profiles.yaml`
- `specs/v26/waiver_contract.yaml`

### 13.4 Why this is not optional

Without this layer, the system remains a linter. It does not become an editorial operating system.

---

## 14. Missing architecture #11: collaboration/platform layer

This is the main gap relative to the “Overleaf killer” ambition.

### 14.1 Current repo reality

The uploaded repo does **not** contain a shipped collaboration layer:

No real equivalents of:

- live comments,
- tracked changes,
- review roles,
- presence/cursors,
- project history UI,
- permissions/ACL,
- institutional auth,
- org/user admin.

### 14.2 End-state architecture required

You need a new top-layer platform spec covering:

- collaboration/session model,
- comments/anchors,
- tracked changes,
- review workflows,
- project history and restore,
- permissions and roles,
- institutional/SSO model,
- deployment modes (local/team/org/cloud),
- audit trails.

### 14.3 Required repo work

This should **not** go into the `latex-parse` core.

Suggested top-level directories:

- `platform/collab/`
- `platform/review/`
- `platform/history/`
- `platform/auth/`
- `platform/api/`
- `clients/web/`
- `clients/desktop/`

### 14.4 Required v27 specs

- `specs/v27/collaboration_protocol.md`
- `specs/v27/editorial_review_model.md`
- `specs/v27/platform_roles_acl.md`
- `specs/v27/deployment_modes.md`

---

## 15. Immediate concrete defects to fix before architecture expansion

These should be corrected before starting serious v26 work.

### 15.1 EDF scheduler deadline bug

`latex-parse/src/edf_scheduler.ml` compares a relative “deadline”/priority against wall-clock Unix time.

**Fix options:**

1. make `deadline` absolute (`now + budget`), or
2. rename it to `priority` and stop treating it as a deadline.

### 15.2 Canonical facts drift

Fix via generated facts contract and CI.

### 15.3 Release-state ambiguity

`CHANGELOG.md` must align with actual shipped status.

### 15.4 DAG metadata hollowness

Stop using `default_meta` universally.

### 15.5 L3 semantics over-source

Document honestly that current L3 is partly source-regex-derived, then plan migration toward AST/project semantics.

---

## 16. Concrete v26 plan (repo-exact)

### 16.1 v26.0 — “Formal contract and project foundation”

**Must ship:**

1. canonical facts generator  
2. spec-drift CI  
3. language contract  
4. support matrix  
5. execution classes  
6. compile-log as first-class Class C subsystem  
7. bounded user macro registry  
8. mutation-testing pilot  
9. fuzzing baseline  
10. EDF bug fix  

**Files to create/rewrite:**

#### Governance / truth-surface
- `generated/project_facts.json`
- `generated/project_facts.yaml`
- `scripts/gen_project_facts.py`
- `.github/workflows/spec_drift.yml`
- rewrite `README.md`
- rewrite `docs/index.md`
- rewrite `CHANGELOG.md`

#### Contract layer
- `specs/v26/language_contract.md`
- `specs/v26/language_contract.yaml`
- `specs/v26/support_matrix.yaml`
- `docs/SUPPORT_MATRIX.md`
- `docs/PROOF_CLASSES.md`

#### Runtime / execution
- `latex-parse/src/execution_class.ml`
- `latex-parse/src/execution_policy.ml`
- rewrite `latex-parse/src/validators.ml`
- rewrite `latex-parse/src/evidence_scoring.ml`
- rewrite `latex-parse/src/edf_scheduler.ml`

#### Compile-log integration
- rewrite `latex-parse/src/log_parser.ml`
- new `latex-parse/src/build_profile.ml`
- new `latex-parse/src/build_profile.mli`
- new `latex-parse/src/log_context.ml`
- new `latex-parse/src/log_context.mli`

#### Macro registry
- `core/l1_expander/user_macro_registry.ml`
- `core/l1_expander/user_macro_registry.mli`
- `core/l1_expander/macro_subset.ml`
- `core/l1_expander/macro_subset.mli`
- rewrite `core/l1_expander/rest_simple_expander.ml`

#### Testing
- `testing/mutation/`
- `testing/fuzz/`
- `.github/workflows/mutation.yml`
- `.github/workflows/fuzz.yml`

#### Proofs
- `proofs/UserMacroTermination.v`
- `proofs/UserMacroRegistrySound.v`
- `proofs/ExecutionClasses.v`
- strengthen `proofs/ValidatorGraphProofs.v`

### 16.2 v26.1 — “Project graph and hybrid invalidation”

**Must ship:**

1. include graph  
2. multi-file project session foundation  
3. hybrid invalidation graph  
4. semantic dependency edges  
5. project-scoped refs/labels/cites foundation  
6. conservative-proof hardening for file-based rules  

**Files to create:**
- `core/project/include_graph.ml`
- `core/project/project_session.ml`
- `core/project/file_resolution.ml`
- `latex-parse/src/dependency_graph.ml`
- `latex-parse/src/invalidation_engine.ml`
- `latex-parse/src/semantic_edges.ml`
- `latex-parse/src/project_runner.ml`
- `proofs/IncludeGraphSound.v`
- `proofs/DependencyInvalidation.v`
- `proofs/ProjectSemantics.v`

### 16.3 v26.2 — “Partial parsing and rewrite substrate”

**Should ship if schedule allows:**

1. lossless CST foundation  
2. partial-document/hole semantics  
3. damage containment theorems  
4. stable IDs/spans  
5. rewrite engine v1  

**Files:**
- `core/l2_parser/cst.ml`
- `core/l2_parser/partial_cst.ml`
- `core/l2_parser/error_recovery.ml`
- `latex-parse/src/rewrite_engine.ml`
- `latex-parse/src/stable_spans.ml`
- `proofs/CSTRoundTrip.v`
- `proofs/PartialParseLocality.v`
- `proofs/DamageContainment.v`
- `proofs/RepairMonotonicity.v`

---

## 17. Concrete v27 plan (repo-exact)

### 17.1 v27.0 — “Editorial operating system”

**Theme:** transform the engine into a high-end editorial platform.

**Must ship:**

1. policy profiles  
2. waivers / exception scoping  
3. review ownership / resolution states  
4. project-wide reporting  
5. support for named institutional/journal style packs  

**Files:**
- `core/editorial/policy_profile.ml`
- `core/editorial/waiver_store.ml`
- `core/editorial/review_state.ml`
- `core/editorial/reporting.ml`
- `specs/v27/editorial_profiles.yaml`
- `specs/v27/waiver_contract.yaml`
- `docs/EDITORIAL_MODELS.md`

### 17.2 v27.1 — “Collaboration and review platform”

**Must ship:**

1. comments/anchors  
2. tracked changes  
3. review workflow  
4. version/history model  
5. project permissions/ACL  

**Files/directories:**
- `platform/collab/`
- `platform/review/`
- `platform/history/`
- `platform/auth/`
- `platform/api/`
- `clients/web/`

**Specs:**
- `specs/v27/collaboration_protocol.md`
- `specs/v27/review_model.md`
- `specs/v27/history_model.md`
- `specs/v27/acl_model.md`

### 17.3 v27.2 — “Compilation guarantee closure”

**Must ship if and only if proofs and project model support it:**

1. compilation theorem stack implementation  
2. engine/profile support contract  
3. project-level compile guarantee mode  
4. explicit LP-Core compile mode  

**Proofs:**
- `proofs/CompileProgress.v`
- `proofs/CompileWellFormed.v`
- `proofs/BuildProfileSound.v`
- `proofs/ProjectClosure.v`

---

## 18. What should explicitly remain out of scope until after v27

These should not be allowed to creep back in.

1. full catcode dynamism  
2. unrestricted `\def` semantics  
3. arbitrary conditional expansion  
4. general shell-escape semantics  
5. fully formal semantics of all foreign binaries  
6. hot-path live ML inference  
7. “support all of LaTeX” marketing language  

---

## 19. The single most important theorem/program split

The project should now be thought of as two coupled systems:

### A. The proved core
- LP-Core parser/expander/project semantics,
- rule enforcement,
- compile guarantees,
- incremental editing semantics.

### B. The sandboxed extension plane
- external binaries,
- foreign package behaviours,
- heuristic style/ML,
- institution/editor integrations,
- collaboration UX.

The central architectural mistake to avoid is mixing these layers in claims or interfaces.

---

## 20. Final statement

**Repo-exact conclusion:**

The uploaded repository demonstrates that LaTeX Perfectionist v25 is already a substantial, highly disciplined analysis engine. What is missing is not breadth of rules or raw performance. What is missing is the architecture required to turn that engine into a formally delimited, project-aware, real-time, collaborative authoring platform with defensible compilation guarantees.

In one sentence:

> **v26 must build the formal language/project/editing substrate; v27 must build the editorial and collaboration platform on top of it.**

Until that is done, the system remains a remarkable verified linter and analyzer. After that is done, it can credibly become the platform you are aiming for.
