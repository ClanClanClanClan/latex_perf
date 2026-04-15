# LaTeX Perfectionist v27 — Repo-exact master specification

Version: v27-draft-repo-exact  
Status: platform-roadmap  
Dependency: v26 substrate must be complete first

---

## 1. Executive objective

v27 is the release family that turns the verified LaTeX project system
into an **editorial and collaboration platform**.

The governing theme is:

> Build the platform layer above the verified core without diluting the support contract.

v27 therefore focuses on:
1. stronger compilation guarantees over LP-Core projects,
2. richer LP-Extended project semantics,
3. lossless CST/rewrite infrastructure,
4. tracked changes, waivers, comments, and review workflows,
5. collaboration/session architecture,
6. institutional deployment and auditing features.

---

## 2. Why v27 exists

The end-state goal is not merely a linter that is faster and more verified than alternatives.
The end-state goal is a platform suitable for:
- perfectionist authors,
- editors,
- institutions,
- review workflows,
- collaborative LaTeX authoring.

v27 exists to provide the missing layers:
- editorial operating system,
- collaboration model,
- policy/waiver model,
- stronger project/build guarantees,
- product-grade platform contracts.

---

## 3. Preconditions from v26

v27 must not start in earnest unless v26 has shipped:
- canonical facts
- support matrix
- explicit proof taxonomy
- bounded macro registry
- project graph foundation
- hybrid invalidation
- initial partial-document semantics
- compile-log first-class subsystem

If these are not done, v27 should slip rather than build on sand.

---

## 4. v27 product contract

### 4.1 Identity
v27 is the first release that can plausibly claim to be:
- a verified LaTeX project platform,
- suitable for editorial workflows,
- extensible at the platform layer,
- collaboration-capable within the supported-language contract.

### 4.2 Public claim after v27
The strongest responsible claim after v27 should be:

> “LaTeX Perfectionist v27 provides a verified core authoring platform for LP-Core projects, bounded LP-Extended projects, formal rule enforcement, project-aware compilation guarantees for the supported profile, and editorial/collaboration workflows above that verified core.”

This is still not “full LaTeX”. It is a stronger and more defensible claim.

---

## 5. v27 workstreams

## WS7 — Concrete syntax tree and rewrite substrate

### Goal
Introduce a lossless representation that supports:
- exact formatting preservation,
- stable node identity,
- policy rewrites,
- semantic fixes,
- review anchors,
- source-map precision.

### Deliverables
- CST layer
- CST↔AST mapping
- stable IDs
- rewrite engine
- round-trip preservation properties
- fix-preservation framework over CST edits

### Acceptance criteria
- no-loss round-trip for supported syntax
- fixes can target CST nodes rather than fragile spans
- comments/whitespace preserved by design

---

## WS8 — Stronger compilation guarantee stack

### Goal
Move from “verified analysis + build-coupled checks” toward a true project compilation contract.

### Deliverables
- engine profile semantics
- supported toolchain profile semantics
- build-pass convergence/bounded-pass contract
- project compile theorem for LP-Core profile
- explicit downgrade path for LP-Extended and LP-Foreign

### Acceptance criteria
- theorem stack documented and partially mechanised
- project compile guarantee exists for the supported profile subset

---

## WS9 — Editorial policy system

### Goal
Make the platform useful for editors and institutions, not just authors.

### Deliverables
- named house-style profiles
- waiver/exception model
- scope-bound suppression with audit trail
- issue ownership/review states
- batch editorial reports
- policy explanation and rationale links

### Acceptance criteria
- journal/thesis/house profiles work
- waivers are auditable and scoped
- reports can be exported for editorial use

---

## WS10 — Collaboration and review

### Goal
Build the platform layer needed to compete with collaborative LaTeX environments.

### Deliverables
- comments/review threads
- tracked changes model
- accept/reject pipeline
- review snapshots/history
- stable anchors backed by CST/project graph
- merge/rebase semantics compatible with supported project states

### Acceptance criteria
- comments survive local edits within documented stability bounds
- tracked changes operate on CST/project structures, not raw text only
- review workflows are deterministic under supported conditions

---

## WS11 — Platform roles, permissions, and deployment

### Goal
Enable institutional/editorial use.

### Deliverables
- project permissions
- roles
- audit logs
- deployment profiles
- backup/restore and provenance for collaborative state
- admin-level support matrix

### Acceptance criteria
- platform state is auditable
- project access control is explicit
- deployment modes are documented and supportable

---

## WS12 — Extension plane and foreign contracts

### Goal
Create a principled extension model instead of uncontrolled feature creep.

### Deliverables
- extension API
- foreign-contract boundary
- explicit support downgrade semantics
- package/tooling contracts for LP-Extended
- extension metadata and risk classification

### Acceptance criteria
- unsupported/foreign features enter through explicit contracts
- extension behaviour cannot silently claim stronger guarantees than allowed

---

## 6. What v27 still does not do

Even v27 should not promise:
- full TeX generality,
- arbitrary catcode semantics,
- unrestricted shell-escape workflows,
- universal package semantics,
- total proof of all external binary/tooling layers.

The support contract remains explicit and bounded.

---

## 7. Proof architecture for v27

### Required new proof families
- CST round-trip and rewrite preservation
- partial-document anchor stability
- tracked-change merge preservation (bounded)
- project compile theorem fragments
- waiver scoping correctness
- extension-boundary correctness

### Conservative-proof refinement
v27 should reduce the appearance of vacuity by:
- contract-testing extractors,
- proving decision layers above extracted metadata,
- classifying every conservative dependency explicitly.

---

## 8. Platform execution model

v27 must preserve the execution class architecture:

- Class A: authoring-critical
- Class B: debounce background
- Class C: build/project coupled
- Class D: advisory/style/heuristic
- Class E (new): collaboration/editorial state propagation

Class E must never silently contaminate the semantics of LP-Core document state.

---

## 9. Timeline

### Phase 1 (6 weeks)
- CST design and prototype
- support taxonomy integration into collaboration/editorial planning

### Phase 2 (6 weeks)
- rewrite substrate
- editorial policy/waiver model
- stronger compile theorem fragments

### Phase 3 (8 weeks)
- collaboration comments/tracked changes
- review/history
- anchor stability

### Phase 4 (6 weeks)
- roles/permissions/deployment profiles
- extension contracts
- release hardening

Total indicative v27 cycle: ~26 weeks after v26 substrate completion.

---

## 10. Exit criteria for v27

v27 only ships if:
- CST round-trip is real for supported syntax
- tracked changes/comment anchors are stable enough for declared workflows
- editorial waivers/policies are auditable
- stronger compile guarantee exists for LP-Core project profile
- support matrix explicitly covers collaboration/editorial features
- no regression in proof taxonomy honesty
