# LaTeX Perfectionist v26 — Repo-exact master specification

Version: v26-draft-repo-exact  
Status: planning-complete, implementation-not-started  
Basis: repo-exact audit of uploaded v25 snapshot plus 2026-04-14 briefing

---

## 1. Executive objective

v26 is **not** a rule-count release.

v26 exists to convert the current verified analysis engine into the
first version of a **verified LaTeX project system**.

The governing theme is:

> Extend semantic reach without weakening the proof/performance contract.

v26 therefore prioritises:
1. truth-surface freeze and canonical facts,
2. compile-log integration as a first-class build-coupled subsystem,
3. a bounded user macro registry,
4. a project graph foundation,
5. hybrid invalidation,
6. stronger proof taxonomy and conservative-proof architecture,
7. testing hardening.

v26 explicitly does **not** attempt:
- full TeX generality,
- full catcode tracking,
- arbitrary macro metaprogramming,
- hot-path live ML inference,
- full Beamer semantics,
- full collaboration platform parity.

---

## 2. Why v26 exists

The repo already contains:
- a high-performance lexer/validator pipeline,
- rule-level proof generation,
- real compile-log parsing,
- chunk-store incremental analysis,
- SIMD acceleration,
- ML for a bounded ambiguous subset.

What it does **not** yet contain is the formal and architectural layer needed
for the following claim:

> “If a project belongs to the supported subset and all mandatory checks pass,
> compilation succeeds under the supported engine/toolchain profile.”

v26 is the release that builds the missing substrate for that claim.

---

## 3. Non-negotiable constraints

1. **No regression of the v25 proof discipline**
   - zero admits
   - zero axioms
   - explicit proof taxonomy
   - every shipped rule classified

2. **No hot-path regression beyond controlled budget**
   - current v25 latency headroom may be spent, but only through explicit execution classes

3. **No truth-surface drift**
   - all public counts and support claims must derive from canonical facts

4. **No silent scope expansion**
   - all newly supported syntax/project features must be inside a named contract

---

## 4. Product contract for v26

### 4.1 Deliverable identity

v26 is the first release that ships:
- a named supported-language contract,
- a bounded user macro subset,
- build-coupled compile-log analysis,
- project graph foundations for multi-file workspaces,
- support matrix and proof taxonomy as first-class public artefacts.

### 4.2 Public claim after v26

The strongest claim v26 should be able to make is:

> “LaTeX Perfectionist v26 provides real-time, formally classified analysis for LP-Core documents and bounded LP-Extended projects, including build-coupled diagnostics and a safe user macro subset.”

It should **not** yet claim full project compilation guarantees for all supported workflows.

---

## 5. Scope split: LP-Core / LP-Extended / LP-Foreign

### 5.1 LP-Core
The fully guaranteed subset.

Includes:
- single-file documents,
- supported engine profile,
- built-in macro catalogue,
- bounded subset of user macro declarations (once v26 ships them),
- deterministic syntax and semantics within stated package boundaries,
- no shell-escape,
- no dynamic code generation,
- no catcode mutation,
- no unrestricted conditional metaprogramming.

### 5.2 LP-Extended
The practical but weaker subset.

Includes:
- selected multi-file projects,
- compile-log coupled checks,
- supported external artefact readers,
- bounded foreign-package contracts,
- conservative-proof-backed rules where necessary.

### 5.3 LP-Foreign
Explicitly outside strongest guarantees.

Includes:
- arbitrary `\def`,
- catcode mutation,
- shell-escape toolchains,
- heavy external preprocessors,
- unsupported project graph patterns,
- unsupported package semantics.

The system must **detect** and **surface** these boundaries, not merely fail mysteriously.

---

## 6. Execution classes

Every rule and subsystem in v26 must be assigned an execution class.

### Class A — keystroke-critical
- exact or tightly bounded
- must respect strict latency budget
- safe on every edit

Examples:
- lexical rules,
- many exact structural rules,
- cheap semantic checks with local dependencies

### Class B — debounce background
- deterministic but heavier
- runs after short idle delay
- may use chunk and semantic cache

Examples:
- semantic cross-reference checks,
- some structure rules requiring local graph context

### Class C — build-coupled
- requires compile logs, generated artefacts, or project-wide build state
- never part of the always-on keystroke-critical path
- triggered on save/build/request

Examples:
- LAY/PAGE subset,
- overfull box analysis,
- font/substitution build diagnostics

### Class D — optional heuristic
- style/NLP/ML/confidence-weighted
- advisory or weighted
- separate budget and UX surface

Examples:
- passive voice,
- sentence style,
- ML-backed ambiguous TYPO rules

This classification must exist both in code and in public docs.

---

## 7. v26 workstreams

## WS0 — Truth-surface freeze (mandatory pre-phase)

### Goal
Create one canonical project facts surface and eliminate repo drift.

### Deliverables
- `project_facts_v26.yaml`
- generator script
- CI spec-drift check
- proof taxonomy export
- support matrix export
- release metadata generator

### Repository impact
Create:
- `governance/project_facts.yaml`
- `scripts/generate_project_facts.py`
- `scripts/check_repo_facts.py`
- `docs/SUPPORT_MATRIX.md`
- `docs/PROOF_TAXONOMY.md`

### Acceptance criteria
- README, docs, changelog, rules overview, planner, and release notes derive from canonical facts
- CI fails on mismatch
- rule counts/proof counts/workflow counts are reconciled

---

## WS1 — Compile-log integration

### Goal
Promote compile-log analysis from auxiliary parser to first-class build-coupled subsystem.

### Deliverables
- formal compile-log ingestion contract
- build-profile object
- first high-value LAY/PAGE pack
- save/build/request execution path
- compile-log fixture corpus

### Initial supported diagnostics
- overfull/underfull boxes
- rerun warnings
- unresolved references/citations where log evidence exists
- font substitution / missing glyph warnings
- selected float/layout warnings

### Repository impact
Refactor:
- `latex-parse/src/log_parser.ml`
- `latex-parse/src/file_context.ml`
- `latex-parse/src/validators_l3_file.ml`
Add:
- `latex-parse/src/build_profile.ml`
- `latex-parse/src/build_artifact_state.ml`
- `proofs/BuildLog/`
- `corpora/build_logs/`

### Acceptance criteria
- Class C path exists and is isolated from keystroke-critical latency budget
- compile-log rules are surfaced distinctly in output
- build-coupled fixtures pass in CI
- theorem/documented contract exists for supported log-derived facts

---

## WS2 — Bounded user macro registry

### Goal
Support a safe, provable subset of user-defined commands.

### Supported forms
- `\newcommand`
- `\renewcommand`
- `\providecommand`

### Restrictions
- fixed bounded arity
- no catcode changes
- no recursive expansion beyond safe fuel
- no delimited-argument tricks
- explicit cycle detection
- unsupported constructs must be diagnosed, not silently ignored

### Deliverables
- macro registry data structure
- definition/use dependency edges
- expansion semantics for supported subset
- unsupported-subset diagnostics
- theorem suite: determinism, termination, cycle detection correctness

### Repository impact
Add/refactor:
- `latex-parse/src/user_macro_registry.ml`
- `core/l1_expander/user_macro_contract.ml`
- `proofs/Expansion/UserMacro*.v`
- macro regression corpus

### Acceptance criteria
- real-world bounded `\newcommand` subset works
- unsupported macro constructs are surfaced cleanly
- proofs hold for the supported subset
- incremental invalidation includes def-use dependencies

---

## WS3 — Project graph foundation

### Goal
Move from document analysis to project analysis.

### Scope
- `\input`
- `\include`
- include graph
- cycle detection
- per-file cache + global semantic projection
- project-local path resolution

### Explicitly not in first cut
- arbitrary external preprocessors
- full generated-file orchestration
- broad package ecosystem modelling
- cloud/workspace sync semantics

### Deliverables
- project manifest/state object
- include graph resolver
- global labels/refs projection
- project cache invalidation layer
- project-level CLI mode

### Repository impact
Add:
- `latex-parse/src/project_graph.ml`
- `latex-parse/src/project_state.ml`
- `latex-parse/src/include_resolver.ml`
- `latex-parse/src/project_semantics.ml`
- `proofs/Project/`
- multi-file corpus suites

### Acceptance criteria
- multi-file single-workspace projects lint coherently
- cross-file labels/refs work
- cycles are diagnosed
- project mode does not regress single-file mode

---

## WS4 — Hybrid invalidation

### Goal
Evolve beyond paragraph-only invalidation without discarding chunk-store simplicity.

### Model
- cache/storage unit: paragraph chunk
- syntactic invalidation unit: CST/AST span or environment span
- semantic invalidation unit: dependency edge set
- project invalidation unit: include/build graph edge

### Dependencies to track
- labels ↔ refs
- counters ↔ section/float environments
- user macro defs ↔ use sites
- bibliography keys ↔ cites
- include edges
- build artefacts ↔ source triggers

### Repository impact
Refactor/add:
- `latex-parse/src/chunk_store.ml`
- `latex-parse/src/edf_scheduler.ml`
- `latex-parse/src/dependency_graph.ml`
- `latex-parse/src/invalidation.ml`
- proofs for locality and damage bounds

### Acceptance criteria
- fewer false whole-source fallbacks
- measured cache-hit improvement on multi-file and macro-heavy projects
- proven unaffected-region preservation where applicable

---

## WS5 — Partial-document and editing semantics

### Goal
Give the editor path a formal semantics for incomplete source states.

### Deliverables
- partial CST/AST with holes
- error-recovery semantics
- bounded damage model
- unaffected-region trust surface
- repair monotonicity statements

### Repository impact
Add:
- `latex-parse/src/partial_cst.ml`
- `latex-parse/src/error_recovery.ml`
- `proofs/Editing/`
- edit-sequence corpus

### Acceptance criteria
- formal distinction between complete and partial document states
- diagnostics carry confidence/trust class under incomplete parse
- local edits do not semantically poison unrelated regions beyond a documented bound

---

## WS6 — Testing hardening

### Goal
Raise confidence that behaviour and proofs remain meaningful under change.

### Deliverables
- mutation testing on core families
- grammar-aware fuzzing
- binary reader fuzzing
- long-run edit stress suite
- differential checks where meaningful

### Acceptance criteria
- mutation score baseline recorded
- fuzzing in CI/nightly
- long-run performance and allocator stability metrics tracked

---

## 8. What v26 explicitly does not do

- full catcode tracking
- unrestricted `\def`
- general TeX conditionals
- full Beamer semantics
- live ML inference in the hot path
- full collaboration platform
- institutional admin layer
- marketplace / extension ecosystem

Any proposal that effectively smuggles these into v26 is out of scope.

---

## 9. Proof architecture for v26

v26 must make the proof taxonomy explicit in both docs and code.

### Required classes
- formal_faithful
- formal_conservative
- statistical_validated

### Required metadata fields
Each rule/spec entry must expose:
- `proof_class`
- `execution_class`
- `support_scope`
- `artifact_dependencies`
- `project_mode_required`

### Additional proof targets
- bounded user macro theorems
- project-graph invariants
- partial-document/local-damage theorems
- stronger contracts for conservative L3/file rules

---

## 10. Performance policy for v26

The v25 performance surplus is a resource, not a trophy.

### Rule
v26 may spend some of the current headroom, but:
- must not collapse Class A responsiveness,
- must isolate Class C work from the hot path,
- must publish separate budgets by execution class.

### Suggested budgets
- Class A p95: remain comfortably sub-millisecond for typical edit windows
- Class B: debounce background budget, separately reported
- Class C: build/save budget, not conflated with edit latency
- Class D: optional/advisory budget

---

## 11. Release slicing

### v26.0
- truth-surface freeze
- support matrix
- proof taxonomy surfaced
- compile-log alpha
- bounded macro registry v1
- initial hybrid invalidation foundation
- testing hardening baseline

### v26.1
- multi-file foundation
- global project semantic projection
- stronger conservative-proof architecture
- expanded compile-log pack

### v26.2
- optional Beamer pilot
- richer UX/explanations
- batch/orchestration improvements
- only then consider gRPC if demand warrants it

---

## 12. Timeline

### Phase 0 (2 weeks)
- WS0 only: truth-surface freeze and CI

### Phase 1 (4 weeks)
- WS1 compile-log
- WS6 testing hardening starts

### Phase 2 (5 weeks)
- WS2 bounded macro registry
- initial dependency edges

### Phase 3 (4 weeks)
- WS3 project graph foundation
- WS4 hybrid invalidation first cut

### Phase 4 (3 weeks)
- WS5 partial-document semantics initial implementation
- release hardening

Total initial v26.0 cycle: ~18 weeks.

---

## 13. Exit criteria for v26.0

v26.0 only ships if all are true:
- canonical facts file drives public counts
- support matrix exists and is public
- proof taxonomy is explicit
- compile-log subsystem works as Class C
- bounded user macro subset is real and documented
- no proof regressions
- no uncontrolled hot-path regressions
- mutation/fuzz/stress infrastructure is live
