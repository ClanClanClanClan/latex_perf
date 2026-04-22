# v26.2 — Partial Parsing, Rewrite Substrate, Compile-Guarantee Stack

**Status:** design doc (v3, audited twice). Commit as part of PR A0.
**Authoritative sources:** `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §5 / §7 / §16.3; `specs/v26/V26_REPO_EXACT_MASTER_SPEC.md`; `specs/v27/V27_REPO_EXACT_MASTER_SPEC.md` (for scope boundary).
**Target tag:** `v26.2.0`; two optional alpha intermediates (§4.3).
**Realistic calendar:** 5–6 weeks single-contributor; **3.5 weeks with two-contributor parallel tracks**; shorter possible only at the cost of review depth.

---

## Companion documents (all authored as part of PR A0)

- [`docs/v26_2/USER_PERSONAS.md`](../../docs/v26_2/USER_PERSONAS.md) — three target users; anchors scope decisions.
- [`docs/v26_2/ROLLBACK_DRILL.md`](../../docs/v26_2/ROLLBACK_DRILL.md) — concrete procedures for v26.2.1 hotfix, apply-fixes corruption recovery, release.yml failure.
- [`docs/v26_2/COMMUNICATION_PLAN.md`](../../docs/v26_2/COMMUNICATION_PLAN.md) — alpha announcements, release page templates, post-tag check procedure.
- [`docs/v26_2/FIX_STYLE_GUIDE.md`](../../docs/v26_2/FIX_STYLE_GUIDE.md) — style guide for rule authors adding `fix` suggestions.
- [`docs/v26_2/CORPUS_LICENSING.md`](../../docs/v26_2/CORPUS_LICENSING.md) — licensing + curation policy for new corpora.

ADRs land separately, one per §2 decision, under `docs/v26_2/adr/ADR-00N-*.md`. Each ADR uses the standard format: Context · Decision · Consequences · Status. The ADRs are written during PR A0 alongside this plan.

## 0. PREREQUISITES (non-negotiable)

This plan starts after ALL of these:

1. **PR #247 merges** (round 10–12 CI gate additions).
2. **v26.1.0 dry-run succeeds:** `bash scripts/release.sh 26.1.0 --dry-run` exits 0.
3. **v26.1.0 tagged + pushed:** tag + GitHub release workflow succeeds (SBOM, Cosign sign, Docker push all green).
4. **Release observability confirmed:** release.yml workflow actually published artefacts — don't assume; verify manually.

```bash
git checkout main && git pull
python3 scripts/tools/pre_release_check.py         # must PASS
bash scripts/release.sh 26.1.0 --dry-run           # first — no side effects
bash scripts/release.sh 26.1.0                     # bumps version + tags
git push origin main && git push origin v26.1.0
# Then: verify https://github.com/.../releases/tag/v26.1.0 has artefacts.
# If release.yml fails silently, v26.1.0 "tag" is incomplete.
```

**Contingency:** if `pre_release_check` fails, DO NOT tag. Fix the failing gate first. If `release.yml` fails post-tag, file an issue; do not proceed to v26.2 work until artefacts are published (users can't install a broken tag).

**If v26.1.1 hotfix becomes necessary:** re-base this plan on main-after-hotfix. The prerequisite `main = v26.1.0-or-later` still holds; nothing in v26.2's PRs conflicts with typical hotfix scope.

Rationale: gates are ratcheted to v26.1-complete state; every v26.2 commit compares against a tagged baseline. Without the tag, governance version drifts and regression ratchets have no anchor.

---

## 1. What v26.1 shipped (concrete checklist)

- §4 Language contract: SOLID, runtime-gated
- §6 E0–E3 editing proofs: SOLID, bound to runtime types (Partial_cst.trust_zone, Parser_l2.located_node, validator_meta)
- §8 Compile-log integration: shipped, `log_context.ml` facade added P1.7
- §9 Hybrid invalidation: `invalidation.ml` + `dependency_graph.ml` + `semantic_edges.ml`, proofs in `DependencyInvalidation.v`
- §10 Validator DAG: 660 contracts, family capability edges, conflict suppression wired
- §11/§11.2 Execution classes + per-class scheduling: runtime-enforced
- §12 Support matrix: memo §12.1 path, drift-gated
- §15 Defects 1–5: all fixed
- §16.1 v26.0 MUST-SHIP: evidence_scoring + edf_scheduler rewrites, all runtime modules
- §16.2 v26.1 MUST-SHIP: include graph + dependency graph + ProjectSemantics.v + DependencyInvalidation.v

**Memo §16.3 deferred to v26.2:** lossless CST, partial-doc/hole semantics, damage containment theorems, stable IDs/spans, rewrite engine v1.

**Memo §5 compilation-guarantee stack:** memo is ambiguous about timing (§5.3 defines T0–T7; §16.3 doesn't list them; v27 WS8 claims them). My decision (§2.7 below): **ship scaffolding + hypothesis-parametric proofs in v26.2**; v27 WS8 discharges the hypotheses with a real toolchain model.

---

## 2. Architectural decisions (locked before coding)

### 2.1 `core/l2_parser/` vs `latex-parse/src/`

**Decision: ship under `latex-parse/src/` with alias modules at memo-prescribed paths.**

Trade-off acknowledged: memo prescribes `core/l2_parser/`; we don't have that directory. Options were:
- **A** (reorg to `core/`): new dune library, many dune edits, real risk of merge conflict with in-flight v26.1 work. 1 full day of build plumbing for zero user-visible value.
- **B** (alias pattern): 5-line `.ml` + `.mli` wrapper; pattern we've used successfully for `macro_subset`, `invalidation_engine`, `log_context`.

Chose B. Technical-debt flag: memo paths remain "canonical prose, aliased runtime". v27 CST-substrate work could revisit.

### 2.2 `aux_state` vs existing `build_artifact_state`

**Decision: distinct modules, both retained.**

- `build_artifact_state.ml` (v26.0, 30 LOC): thread-local wrapper over `Build_profile.t`; holds a parsed log context.
- `aux_state.ml` (v26.2, NEW): reads and parses the `.aux` FILE on disk — cross-references (`\newlabel`, `\bibcite`, counters, `\@LN`).

**Scope correction from v2 plan:** .aux parsing is **multi-day work, not a thin wrapper**. The pdflatex `.aux` format has ~20 macro shapes. Estimated 1.5 days for a conservative parser that handles the common 80% and bails safely on the rest.

### 2.3 Four graphs

**Decision correction (from v3 audit): there are FOUR graphs in the runtime, not three. Documented in `docs/FOUR_GRAPHS.md`.**

- `Validator_dag` (v26.0, `validator_dag.ml`): rule dependency + conflict DAG.
- `project_graph.ml` (v26.1): include graph of `.tex` files (tex→tex via `\input`, `\include`).
- `dependency_graph.ml` (v26.1): semantic chunk dependencies for invalidation.
- `build_graph.ml` (v26.2, NEW): **build-pipeline** dependencies (tex→aux, tex→bbl, bib→bbl, tex→pdf).

Distinct edge types, distinct consumers. Unified-graph refactor is a v27 consideration.

### 2.4 Coq-level shape of "hypothesis-parametric" proofs (T6/T7)

**Decision: use `Section` + `Variable` pattern.**

```coq
Section Compile_progress.
  Variable project : Type.
  Variable profile : Type.
  Variable bounded_build_terminates_for : project -> profile -> Prop.
  Variable T0_parser_accepts : project -> Prop.
  Variable T1_expansion_admissible : project -> Prop.
  (* ... T2-T5 ... *)
  Variable compilation_succeeds : project -> profile -> Prop.

  (* Model rule of combination: all conditions + termination -> success *)
  Hypothesis compile_progress_rule :
    forall p pf,
      T0_parser_accepts p ->
      T1_expansion_admissible p ->
      T2_project_closed p ->
      T3_profile_compatible p pf ->
      T4_semantic_coherent p ->
      T5_rule_safe p ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.

  Theorem compile_progress_under_bound :
    forall p pf,
      T0_parser_accepts p ->
      ... (all of T0-T5) ... ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.
  Proof. intros. apply compile_progress_rule; assumption. Qed.
End Compile_progress.
```

After `End Compile_progress`, the theorem becomes universally-quantified over the Variables:

```coq
compile_progress_under_bound :
  forall project profile (bounded : project -> profile -> Prop)
         (T0 : project -> Prop) ... (compile_rule : ... -> compilation_succeeds p pf),
  forall p pf, T0 p -> T1 p -> ... -> bounded p pf -> compilation_succeeds p pf.
```

**Zero `Axiom` / `Parameter` declarations** — `admit-audit` and `anti-axiom` gates still pass. The `Hypothesis` is scoped to the Section; after `End`, it becomes a universally-quantified parameter. This is idiomatic Coq and distinct from a global axiom.

Callers of this theorem (v27 WS8) instantiate the Variables/Hypothesis with a concrete model of the LaTeX toolchain.

**Concrete instantiation sketch (for v27 WS8 to implement):**

```coq
(* v27 WS8 writes this against a specific toolchain model: *)
Require Import CompileProgress.

Module PdflatexModel.
  Inductive project := mk_project (files : list tex_file) (root : tex_file).
  Definition profile := Pdflatex.
  Definition bounded_build_terminates_for (p : project) (pf : profile)
    : Prop := exists n, pdflatex_pass_count p <= n.
  (* ... instantiate T0..T5 predicates concretely ... *)
  Lemma instantiated_progress : forall p pf,
    ...concrete conditions... -> compilation_succeeds p pf.
  Proof.
    intros. apply compile_progress_under_bound; eauto.
  Qed.
End PdflatexModel.
```

v26.2 ships the SECTION-PARAMETRIC theorem; v27 WS8 ships the MODULE that instantiates it.

**Gate verification:** before shipping, confirm `anti-axiom` gate (banning `Parameter` / `Axiom`) does NOT fire on Section-quantified Variables. Test with a minimal Coq file; if gate misfires, adjust the regex BEFORE committing the proof.

### 2.5 CST round-trip semantics

**Decision: two-level round-trip promise, with explicit input-validity bounds.**

**Input-validity precondition (UNIVERSAL claims require):** `s` is a valid UTF-8 string of length ≤ `Sys.max_string_length`. The theorem does NOT cover bit-flipped binary garbage; `Cst.of_source` on invalid UTF-8 returns `Error BadEncoding`.

- **Byte-lossless (UNIVERSAL under precondition):** for any valid UTF-8 input `s`, `Cst.to_source (Cst.of_source s) = Ok s` — as bytes. Achieved by using `Unparsed { text; span; reason }` nodes as a fallback for any span the structured parser rejects.
- **Structure-lossless (SUBSET):** for documents in the declared subset (§2.6), the CST is fully structured — every token/group/env is a typed node, `Unparsed` nodes are absent.
- **Empty input:** `Cst.of_source ""` returns `Ok (Document [])`, `Cst.to_source` returns `""`. Edge case tested.

This is strictly stronger than my v2 plan said. It means:
- Users who feed arbitrary LaTeX through `Cst.of_source` + `Cst.to_source` get their bytes back (no data loss ever).
- The structured-CST subset promise is a SEPARATE claim: within the subset, edits target typed nodes, not fragile spans.
- `\verb` / `\lstlisting` / catcode-mutation regions become `Unparsed` — still round-trippable, but rewrites can't target them structurally.

### 2.6 CST subset for structured round-trip

**In scope for v26.2 structured CST:**
- UTF-8 source (multi-byte CODEPOINTS, not byte-only)
- Standard catcode regime (no mid-document `\catcode` in body)
- Balanced groups, environments, math modes (inline + display)
- Comments (full-line + end-of-line), whitespace preserved byte-exact
- `\newcommand` / `\renewcommand` / `\providecommand` macro definitions
- Cross-references, labels, refs

**Out of scope for structured CST (fall back to `Unparsed`):**
- `\verb` / `\verb*` / `\lstlisting` / `fancyvrb` blocks
- `\begin{comment}` ... `\end{comment}` (verbatim-family)
- Arbitrary `\def` with non-standard catcode specs
- `\catcode` declarations in body
- `\newenvironment` custom environments (out of scope for structured CST; body becomes `Unparsed`)
- BOM handling (document excludes BOM input)
- Mixed encodings (UTF-8 only)

Line endings: preserved byte-exact (CRLF / LF passes through unchanged).

**`\input` / `\include` expansion policy:** v26.2 CST does NOT inline included files. `\input{sub}` is kept as a structured token; cross-file analysis happens at the `project_model` layer, not the CST layer. Rationale: CST preserves source of a single file; project-level semantics are orthogonal.

### 2.7 Compile-guarantee stack timing

**Decision: ship A-track scaffolding + T0–T5 mechanized wrappers + T6/T7 hypothesis-parametric proofs in v26.2.** v27 WS8 discharges the T6/T7 hypotheses against a toolchain model.

Alternative rejected: defer all compile-guarantee work to v27. Reason: the runtime modules (project_model, build_graph, aux_state, compile_contract) are standalone valuable for v26.2 users running multi-file projects; they don't need v27's toolchain model.

### 2.8a `--apply-fixes` safety semantics

**Decision** (promoted from v4 audit): `--apply-fixes` MUST ship with these guards or not ship at all:

1. **Backup before write.** `doc.tex` → `doc.tex.bak-<timestamp>` first. CLI prints the backup path.
2. **Atomic per-file writes.** `doc.tex.tmp` + fsync + rename. No partial writes on crash.
3. **Multi-file all-or-nothing.** Staging dir + atomic batch rename. Either all succeed or none do.
4. **Refuse on conflict.** Overlapping `Cst_edit.edit` → fail with listing. No silent merge.
5. **Refuse on parse failure.** Re-parse after rewrite; abort + restore on parse failure.

Rationale: P2 industrial-writer persona explicitly cannot tolerate silent corruption. Details in [ROLLBACK_DRILL.md](../../docs/v26_2/ROLLBACK_DRILL.md).

### 2.8b Granularity of `--apply-fixes`

**Decision** (promoted from v4 audit): v26.2 ships `--apply-fixes` as all-or-nothing only. `--apply-fixes-for RULE-ID` deferred to v26.3. Rationale: P1/P2 users want bulk application; P3 library users wrap the rewrite engine directly and don't need CLI granularity. Adding the flag later is additive; removing it would be breaking.

### 2.8 CST generation strategy — **actual dependency audit**

**Decision: post-process Parser_l2's located_node output + source slicing.**

**But FIRST audit Parser_l2** to confirm it records enough information for CST reconstruction. Specifically verify:
- `located_node` records accurate `loc.offset` for every token (grep `Parser_l2.located_node`)
- Comment positions preserved OR source has comment regex-scannable
- Whitespace positions recoverable from offset diffs

**If Parser_l2 is inadequate**, fallback: add a lightweight lex pass in `Cst_of_ast.ml` that re-tokenizes the source with comment/whitespace preservation. Cost: ~0.5 day extra.

This audit is a **prerequisite of PR B1**; if the audit fails, B1 scope grows by 0.5 day.

---

## 3. PR sequence

Seven PRs + alpha tags. Per-PR: memo mapping, backout plan, acceptance criteria.

### 3.1 Track A — Compile-guarantee stack

#### PR A0 — Decisions + ADRs + plan commit (0.5 day, pure docs)

**Files:**
- `specs/v26/V26_2_PLAN.md` (THIS document)
- `docs/ARCHITECTURAL_DECISIONS.md` — ADR-style record of §2.1–§2.8 decisions
- `docs/THREE_GRAPHS.md` — project_graph / dependency_graph / build_graph disambiguation

**Memo mapping:** prerequisite for §5, §16.3.
**Backout:** docs-only; safe to revert.

#### PR A1 — Compile-stack specs (0.5 day)

**Files:**
- `specs/v26/compilation_guarantee_stack.md` — T0–T7 with PRECISE preconditions, Coq-level signature sketch per §2.4
- `specs/v26/compilation_profiles.yaml` — engine/toolchain profile metadata
- `docs/COMPILATION_GUARANTEE.md` — user-facing summary
- Update `check_memo_files.py` PATH_ALIASES (remove entries that now resolve directly)

**Memo mapping:** §5.5 "new specs".
**Backout:** docs + yaml; no runtime impact.

#### PR A2 — Compile-stack runtime scaffold (3.5 days)

**Files:**
- `latex-parse/src/project_model.{ml,mli}` — typed project
- `latex-parse/src/build_graph.{ml,mli}` — build-pipeline graph (distinct from project/dep graphs; see §2.3)
- `latex-parse/src/aux_state.{ml,mli}` — **.aux file PARSER** (multi-day work per §2.2 — not a wrapper). **Verification requirement:** parser must succeed on at least 3 real `.aux` files produced by running pdflatex on documents from `corpora/`, not just synthetic fixtures. Scope: pdflatex-only for v26.2; xelatex/lualatex deferred to v26.3. Related aux-family files (`.toc`, `.lof`, `.lot`, `.idx`, `.glg`) are explicitly out of scope.
- `latex-parse/src/compile_contract.{ml,mli}` — glue module; `check_ready_to_compile` runs T0–T5 at runtime
- `corpora/compile_contract/` — 5+ sample projects: simple, multi-file, with-bib, with-missing-ref, with-cycle
- Unit tests: `test_project_model.ml`, `test_build_graph.ml`, `test_aux_state.ml`, `test_compile_contract.ml`
- **End-to-end integration test:** `test_compile_contract_e2e.ml` — parse corpus project → build project_model → check compile_contract → assert expected result
- Update `check_memo_files.py` PATH_ALIASES for the new memo-prescribed paths

**Memo mapping:** §5.5 "new runtime modules".
**Backout:** all modules additive; can revert wholesale. CLI doesn't require them.

**Split recommendation (from v4 audit):** this PR is large (4 new modules, 4 test modules, corpus, integration test). Consider splitting:
- **A2a:** `project_model` + `build_graph` + their tests (~1.5d)
- **A2b:** `aux_state` + `compile_contract` + integration test + corpus (~2d)

Splitting reduces review burden and lets A2a merge while A2b's .aux-parser work is still in progress. If time pressure forces a single PR, document that choice was deliberate.

#### PR A3 — Compile-stack proofs + v26.2.0-alpha1 tag (4.5 days)

**Files:**
- `proofs/ProjectClosure.v` (T2)
- `proofs/BuildProfileSound.v` (T3)
- `proofs/CompileProgress.v` (T6) — hypothesis-parametric per §2.4
- `proofs/CompileWellFormed.v` (T7) — hypothesis-parametric
- Wrapper proofs: `proofs/T0_wrapper.v` (parser_accept via ParserSound.v), `T1_wrapper.v` (via UserExpand.v), `T4_wrapper.v` (via LabelsUnique.v + ProjectSemantics.v), `T5_wrapper.v` (via per-rule QED chain + explicit gap-documentation)
- `proofs/ADMISSIBILITY_MAP.md` — lists which hypotheses T6/T7 rely on; entry-point for v27 WS8 discharge
- `_CoqProject` update
- **Alpha tag: `v26.2.0-alpha1`** after A3 merges — users can test compile_contract pipeline while B-track proceeds.

**Memo mapping:** §5.3 (T0–T7), §5.5 (new proofs).
**Backout per proof:** each file independent. Can land T0/T1/T2/T3/T4/T5 wrappers without T6/T7; graceful degradation.

---

### 3.2 Track B — Lossless CST + rewrite

#### PR B0.5 — Parser_l2 capability audit (0.5 day)

**Purpose:** verify §2.8 prerequisite. Pure investigation PR.

**Files:**
- `docs/PARSER_L2_AUDIT.md` — what Parser_l2 records, what's missing for CST generation, recommended strategy (post-process-only vs. post-process + lightweight lex).

**Backout:** docs-only.

#### PR B1 — Lossless CST foundation (3.5 days, scaled for audit outcome)

**Files:**
- `latex-parse/src/cst.{ml,mli}` — CST type (per §2.5: `Unparsed` variant included for byte-lossless fallback)
- `latex-parse/src/stable_spans.{ml,mli}` — extends `Node_id` with shift-on-edit semantics
- `latex-parse/src/cst_of_ast.{ml,mli}` — AST → CST conversion (post-process strategy per §2.8)
- `core/l2_parser/cst.{ml,mli}` — alias for memo path
- **Perf test:** `test_cst_perf.ml` — measure `Cst.of_source` on a large (10MB) LaTeX file; ratchet ceiling at 100ms (vs. current parser ~30ms)
- Unit tests: `test_cst.ml`, `test_cst_of_ast.ml`, `test_stable_spans.ml`

**Memo mapping:** §16.3 "lossless CST foundation", "stable IDs/spans".
**Backout:** additive; nothing consumes CST yet.

#### PR B2 — CST round-trip + corpus (3 days, with fallback)

**Files:**
- `proofs/CSTRoundTrip.v` — **byte-lossless for arbitrary input** (via Unparsed fallback); **structure-lossless for declared subset** (§2.6)
- `corpora/roundtrip/` — curated from existing `corpora/lint/` + `corpora/perf/` + synthetic edge cases (100+ files)
- `latex-parse/src/test_cst_roundtrip.ml` — byte-lossless check for every corpus file; structure-lossless check for the declared-subset files
- `docs/CST_ROUNDTRIP_SCOPE.md` — explicit subset documentation

**Memo mapping:** §16.3 via CST foundation; §7 partial-doc semantics complementary.
**Risk:** HIGH. Round-trip proofs are where "lossless CST" projects classically fail.
**Fallback plan (preregistered):** if Coq proof stalls past 3 days:
- **B2a (mandatory):** runtime byte-lossless test on corpus ships in B2.
- **B2b (deferred):** `CSTRoundTrip.v` becomes v26.3 scope; docs note the structure-lossless claim is corpus-tested but not Coq-proved in v26.2.
Proceed with B3 regardless — rewrite engine doesn't require the Coq proof, only the runtime guarantee.

#### PR B3 — Rewrite engine v1 + v26.2.0-alpha2 tag (3 days)

**Files:**
- `latex-parse/src/rewrite_engine.{ml,mli}`
- `latex-parse/src/cst_edit.{ml,mli}` — edit algebra with conflict detection
- `proofs/RewritePreservesCST.v` — structural well-formedness preserved
- `proofs/RewritePreservesSemantics.v` — local-only semantic preservation (whitespace edits in whitespace regions preserve token stream)
- `latex-parse/src/validators_common.ml`: add optional `fix : Cst_edit.edit option` field to `result` (additive, labels preserved)
- `latex-parse/src/validators_cli.ml`: add `--apply-fixes` flag
- 3+ existing rules produce `fix` suggestions: STRUCT-001 (insert documentclass), TYPO-002 (`--`→`–`), TYPO-003 (`---`→`—`)
- **Fuzz test:** `test_rewrite_fuzz.ml` — random edit lists applied to random CSTs; assert no corruption or conflict-detection bugs
- E2E integration test: `test_rule_fix_integration.ml` — validator → fixes → rewrite → parse-verify
- **Alpha tag: `v26.2.0-alpha2`** after B3 merges.

**Memo mapping:** §16.3 "rewrite engine v1".
**Risk:** moderate (new API surface that ships to users).

---

### 3.3 PR C — v26.2.0 final tag + documentation consolidation (1 day)

**Files:**
- `governance/project_facts.yaml` regenerate (theorem count, proof class totals)
- `CHANGELOG.md` — full `[v26.2.0]` entry, replacing the `-alpha1/-alpha2` working sections
- `README.md`, `docs/index.md`, `docs/PROOFS.md`, `docs/PROOF_GUIDE.md`, `docs/PROOF_CLASSES.md`, `docs/SUPPORT_MATRIX.md` + `.yaml`, `specs/README.md`, `specs/rules/README.md` — count refresh + new-module mentions
- **`docs/MIGRATION_v26.1_to_v26.2.md`** (NEW) — user-facing migration guide
- **`docs/ARCHITECTURE_DIAGRAM.md`** (NEW) — diagram showing project_model / build_graph / aux_state / compile_contract / CST / rewrite_engine
- **`docs/PROOF_RELATIONSHIPS.md`** (NEW) — T0–T7 stack with arrows to existing proofs (ParserSound, UserExpand, ExecutionClasses, ProjectSemantics, LabelsUnique, per-rule chain)
- **Differential test run** (HARD BLOCK on tag): run v26.1 and v26.2 over `corpora/regression/`, diff outputs; only the new `fix` field may differ. ANY other field diff (rule fired/not-fired, severity, count, message) is a regression and blocks the tag. No exceptions without explicit changelog justification per diffing rule.
- `scripts/release.sh 26.2.0` — tag

**Backout per tag:** if the tag exposes a critical bug within 24h, cut `v26.2.1` hotfix; no attempt to unwind the tag.

---

## 4. Timeline + parallelism

### 4.1 Dependencies

```
v26.1.0 tag (prereq)
   ↓
  A0  (decisions)
   ↓
  A1 (specs)       B0.5 (parser audit)
   ↓                ↓
  A2 (runtime)    B1 (CST)
   ↓                ↓
  A3 (proofs)     B2 (round-trip)
   +              ↓
  [alpha1]       B3 (rewrite)
                  +
                  [alpha2]
   ↓                ↓
   └──────► C (v26.2.0 final)
```

### 4.2 Calendar estimates

Engineering days below include self-review + CI wait; external review cycles overlap (typically 1–2 days per PR, absorbed into the NEXT PR's engineering time).

| PR | Eng. days | Critical path? |
|---|---|---|
| A0 | 0.5 | yes |
| A1 | 0.5 | yes |
| A2 | 3.5 | yes |
| A3 | 4.5 | yes |
| B0.5 | 0.5 | (parallel) |
| B1 | 3.5 | yes (B-path) |
| B2 | 3.0 | yes (B-path) |
| B3 | 3.0 | yes (B-path) |
| C | 1.0 | yes |

**Single contributor serial:** 0.5+0.5+3.5+4.5+0.5+3.5+3.0+3.0+1.0 = **20 days** (4 weeks)
**Two contributors parallel:** critical path = A-track (9 days) vs B-track (10.5 days) + C(1) = **~11.5 days** (2.5 weeks). Realistic with review cycle overhead: **3.5 weeks**.

### 4.3 Alpha releases (value-add for user feedback)

- **v26.2.0-alpha1:** after A3 merges. Ships compile_contract pipeline; users with multi-file projects can test.
- **v26.2.0-alpha2:** after B3 merges. Ships CST + rewrite engine; early adopters can exercise `--apply-fixes`.
- **v26.2.0:** after C merges. Final.

Alpha tags cost ~0.5 day each (lightweight governance regen + changelog note). High value for catching integration issues before final.

---

## 5. Per-PR governance checklist + explicit acceptance criteria

### 5.1 Universal checklist (every PR)

- [ ] `pre_release_check.py --allow-dirty --skip-build` passes before opening
- [ ] Governance regenerated if rule/proof counts change (`scripts/tools/generate_project_facts.py`)
- [ ] Contracts regenerated if family edges change (`scripts/tools/generate_rule_contracts.py`)
- [ ] `CHANGELOG.md` updated in the `[v26.2.0-alpha]` working section
- [ ] New `.mli` files: every `val` has ocamldoc comment (gate enforces)
- [ ] New proofs: added to `_CoqProject`; anti-tautology + proof-substance gates pass
- [ ] New rules: FAMILY-NNN format (gate enforces)
- [ ] New YAML: parse + schema check
- [ ] `check_perf_ratchet` PASSES on unit-tests CI run
- [ ] All 13 existing gates + build + tests green
- [ ] `check_memo_files.py` PATH_ALIASES updated to reflect new memo-resolving paths
- [ ] Reviewer assigned before opening (at minimum: tech-lead; Coq PRs need a second reviewer)

### 5.2 Per-PR specific acceptance criteria

- **A0:** plan + ADRs + four-graphs doc committed; no code; no broken doc-refs.
- **A1:** `compilation_guarantee_stack.md` + profiles yaml + user-facing doc; memo-files gate resolves both new paths directly.
- **A2 (or A2a+A2b):** 4 runtime modules + unit tests + 5+ corpus projects + E2E test `test_compile_contract_e2e.ml`; `.aux` parser verified against ≥3 real pdflatex outputs.
- **A3:** 4 new proofs + 4 wrappers + `ADMISSIBILITY_MAP.md`; anti-axiom gate passes on Section pattern (canary test required); wrapper proofs cite existing theorems correctly.
- **B0.5:** `PARSER_L2_AUDIT.md` committed with pass/fail on 3 objective criteria: (1) `located_node.offset` accurate per position, (2) comment spans recoverable, (3) whitespace positions recoverable.
- **B1:** CST type + `cst_of_ast` + stable_spans; perf test at 10MB source ≤ 100ms; type reviewed by a second contributor before merge.
- **B2:** runtime round-trip test passes on 100+ corpus files; Coq proof either lands OR B2b deferral is formally signed-off in CHANGELOG.
- **B3:** rewrite_engine + 3 exemplar rules with `fix` suggestions (style-guided per [FIX_STYLE_GUIDE.md](../../docs/v26_2/FIX_STYLE_GUIDE.md)); fuzz test 10,000 random edit lists without corruption; E2E test (validator→fixes→apply→parse) passes; `--apply-fixes` safety semantics (§2.8a) all implemented + unit-tested.
- **C:** all alpha content consolidated; MIGRATION + ARCHITECTURE + PROOF_RELATIONSHIPS docs merged; differential test passes (HARD BLOCK); release.yml succeeds post-tag (verify artefacts); ROLLBACK_DRILL.md scenarios tested on a fork before tag; COMMUNICATION_PLAN templates used for the published release page.

---

## 6. Testing strategy

### 6.1 Layers

- **Unit tests** per module (existing pattern)
- **End-to-end integration tests** per PR where the module touches a pipeline: A2 (`test_compile_contract_e2e.ml`), B3 (`test_rule_fix_integration.ml`)
- **Perf tests** with ratchet: existing `test_l2_gate.ml` + `check_perf_ratchet.py`; NEW `test_cst_perf.ml` in B1
- **Fuzz tests**: NEW `test_rewrite_fuzz.ml` in B3 (10,000 random edit lists, deterministic seed)
- **Corpus tests**: NEW `corpora/compile_contract/` (A2), `corpora/roundtrip/` (B2)
- **Differential tests**: v26.1 vs v26.2 on `corpora/regression/` — gate PR C
- **Security / threat model** (NEW in v4 audit): `--apply-fixes` consumes rewrite text from rule suggestions which flow through validator code. Document a threat model: rule-supplied fix text is considered TRUSTED (authored by us in-tree); user source is UNTRUSTED but read-only. The rewrite engine must NOT execute arbitrary input as code (no `Scanf.sscanf` into `Obj.magic`, no shell-out).

### 6.2 Differential testing details

Purpose: ensure v26.2 produces IDENTICAL validator output to v26.1 on the same source (except new fix suggestions).

```bash
# In PR C release-gate script:
python3 scripts/tools/run_differential_test.py \
  --baseline-tag v26.1.0 --new-ref HEAD \
  --corpus corpora/regression/ \
  --expected-diff-keys "fix"  # only this key may differ
```

If any non-fix field differs between tags, it's a regression. Requires building this tool (not currently in the plan's scripts); ~0.5 day added to C.

### 6.3 Alpha-release smoke testing

Each alpha tag:
- `v26.2.0-alpha1`: run full test suite + compile_contract e2e on 3 real-user projects (if we have any)
- `v26.2.0-alpha2`: run `--apply-fixes` on those same 3 projects; verify output still compiles

---

## 7. Risk register

| # | Risk | Likelihood | Impact | Mitigation | Backout |
|---|---|---|---|---|---|
| R1 | CSTRoundTrip.v Coq proof intractable | Med | Hi | Pre-registered B2a/B2b split | Ship runtime-only; defer Coq proof |
| R2 | T6/T7 Section pattern triggers anti-axiom gate | Low | Hi | §2.4 verified: Hypothesis ≠ Parameter | Reformulate as explicit arg |
| R3 | Parser_l2 audit reveals CST-gen gap | Med | Med | B0.5 audit PR before B1 code | Add 0.5d for lightweight lex pass |
| R4 | CST type API commitment wrong | Low-Med | Hi | Architecture-review comment required on B1 | v26.3 breaking change (last resort) |
| R5 | aux_state parser incomplete on corpus | Med | Med | pdflatex-only explicit scope; xelatex/lualatex deferred | Doc limitation |
| R6 | Proof-ci time exceeds 15-min budget | Med | Low | Existing proof-farm sharding | Skip shards on PRs |
| R7 | Merge conflict between tracks (CHANGELOG/governance) | Low | Low | Per-PR rebase cadence; CHANGELOG section structure | Merge manually |
| R8 | Coq 8.18 → Rocq 9 forced mid-project | Low | Med | Lock 8.18 in opam | Upgrade all proofs at once |
| R9 | API-compat break in ad hoc PR | Low | Hi | `Validators.result` add-only; new modules new API | Reject PR |
| R10 | CI flake blocks merge | Med | Low | Meta-gate catches gate-script bugs; known flakes documented | Rerun |
| R11 | Single contributor burnout on 6-week plan | Med | Med | Alpha tags give visible progress | Redistribute PRs |
| R12 | v26.1.0 critical bug post-tag | Low | Hi | Fast-cut v26.1.1 hotfix; v26.2 proceeds on main | Hotfix branch |
| R13 | PR A0 decisions contested in review | Med | Med | Circulate §2 decisions to likely reviewers BEFORE opening A0; collect objections async | Rework A0 |
| R14 | CI build time balloons with new modules/proofs | Med | Low | Monitor proof-ci elapsed; shard via existing proof-farm if >20min | Split _CoqProject |
| R15 | Release-tag rollback needed (v26.2.0 critical bug) | Low | Hi | v26.2.1 hotfix; tag is never "unpublished", only superseded | Cut v26.2.1 quickly |
| R16 | Coq Section/Variable pattern trips anti-axiom gate | Low | Med | Pre-verified in §2.4; small canary proof tests the gate | Adjust regex |
| R17 | Alpha adopters report breakage between alpha1 and alpha2 | Med | Low | Alpha tags are explicitly "for testing"; document no-SLA | Document in release notes |
| R18 | Single Coq reviewer bottleneck | Med | Med | Identify 2nd reviewer early; rotate per PR | Accept slower merges |
| R19 | Corpus `.aux` test fails because pdflatex isn't in CI | Med | Low | Check-in pre-generated .aux files; skip if pdflatex missing | Generate once, commit |
| R20 | v26.2 main drifts under hotfixes to v26.1.x | Low | Med | Rebase cadence on v26.2 branches; explicit re-basing clause | Rebase |

---

## 8. API stability commitment (v26.2 is additive over v26.1)

- No public function signature changes.
- No rule IDs renamed or removed.
- No Coq theorem statements weakened.
- `Validators.result` gains `fix : Cst_edit.edit option` field — in OCaml, adding a record field is source-compatible ONLY IF existing callers use label-based construction (`{ id; severity; message; count }`) without exhaustiveness-required patterns.

  **Verification required in PR B3:** before merging the field addition, run
  ```
  grep -rn "match .* with" latex-parse/ | grep -v test_ | \
    awk '/{ id *=|{ severity *=/' | head
  ```
  Any exhaustive pattern match on `result` that would break with a new field MUST be refactored to use `_` wildcard or explicitly ignore `fix`. If none found, the additive claim holds. If found, either refactor those call sites OR retract the additive claim (would force v26.2 to be a minor-major bump).

- New modules are new public API surface (`Cst`, `Cst_edit`, `Rewrite_engine`, `Project_model`, `Build_graph`, `Aux_state`, `Compile_contract`, `Stable_spans`).
- Memo-alias modules in `core/l2_parser/` are re-exports; same API as canonical `latex-parse/src/` modules.

**Deprecations and breaking changes are v27 scope.**

---

## 9. Scope-saving note for v27

By shipping v26.2 as planned:
- **v27 WS7 (CST substrate) deliverables:** CST layer ✓, CST↔AST mapping ✓, stable IDs ✓, rewrite engine ✓, round-trip preservation ✓ (runtime + Coq-if-B2-lands), fix-preservation framework ✓. **Effectively delivered by v26.2.**
- **v27 WS8 (stronger compile-guarantee stack) deliverables:** engine profile semantics ✓, toolchain profile semantics ✓, theorem stack documented and partially mechanised ✓, project compile guarantee ✓ (hypothesis-parametric). **Effectively delivered by v26.2.**

v27 focus then reduces to WS9 (editorial policy), WS10 (collaboration), WS11 (platform/deployment), WS12 (extension plane).

---

## 10. Deferrals

### Deferred to v26.3 (explicit)

- xelatex / lualatex .aux parser variants
- Full `CSTRoundTrip.v` coverage of `\verb`, catcode mutations, `\lstlisting`
- Automatic conflict-aware rewrite merging
- Rolling `fix` suggestions for all 660 rules (v26.2 has ~3 exemplars)
- `specs/v26/partial_document_semantics.yaml` (memo §7; prose doc ships in v26.2)

### Deferred to v27 (per memo §17)

- WS9 Editorial policy system
- WS10 Collaboration platform
- WS11 Deployment / permissions
- WS12 Extension plane + foreign contracts
- Discharge of T6/T7 hypotheses with real toolchain model (WS8 refinement)

### Out of v26.x entirely

- gRPC interface (memo §10 "only if demand warrants")
- Runtime observability / SLOs (deployment concern, not library concern)
- Coq extraction for full runtime-binding verification (requires CST surgery to have a richer target)

---

## 11. Process decisions (pre-filled, override if needed)

v3 left these as open questions; v4 fills in default answers. Override if project reality differs.

- **Branch strategy:** feature-branch-per-PR, merge-commit into main. Matches #241–#247 history. No long-lived v26.2 branch.
- **Reviewer assignment:** each PR's reviewer TBD at open-time; Coq PRs (A3, B2, B3) require 2 reviewers minimum. Explicit rule: author cannot self-merge Coq work.
- **RC tag?** No — ship alpha1 (after A3), alpha2 (after B3), then final. Skipping rc keeps the cadence lean.
- **Alpha adoption tracking:** monitor GitHub Issues tagged `v26.2-alpha-feedback`. If zero external feedback after 1 week of alpha1, ship alpha2 + final on schedule. No active solicitation — per [COMMUNICATION_PLAN.md](../../docs/v26_2/COMMUNICATION_PLAN.md) silence policy.
- **Change-management approval:** this plan needs tech-lead sign-off before PR A0 opens. Sign-off = an inline comment on PR A0 draft or a short approval commit to the repo.
- **Plan-file splitting:** done in v4 — §6 testing + §7 risks stay in-plan; personas, rollback, communications, style, corpus split into `docs/v26_2/`.
- **Licensing of new files:** new OCaml modules inherit repo's MIT license (already in `LICENSE`). No per-file copyright headers required (matches existing convention).
- **i18n for fix messages:** English-only in v26.2. Locale deferred per [USER_PERSONAS.md](../../docs/v26_2/USER_PERSONAS.md).
- **Metrics/telemetry:** none in v26.2 code. Deploy-time concern.
- **Docs organisation:** flat `docs/` stays for now; `docs/v26_2/` groups release-specific docs. Not yet refactoring to `docs/by-layer/`.

---

## 12. First concrete action

Open **PR A0**: commit this plan + ADRs + three-graphs doc. Pure docs. 4 hours.

After PR #247 merges and v26.1.0 is tagged:

```
git checkout main && git pull
git checkout -b v26.2/a0-decisions
# Files already in place from this planning session:
#   specs/v26/V26_2_PLAN.md
# Create:
#   docs/ARCHITECTURAL_DECISIONS.md
#   docs/THREE_GRAPHS.md
python3 scripts/tools/pre_release_check.py --allow-dirty --skip-build
git commit -m "docs(v26.2): PR A0 — architectural decisions + plan"
git push -u origin v26.2/a0-decisions
gh pr create --title "docs(v26.2): PR A0 — decisions + plan" \
  --body "..."
```

---

## 13. v26.3 preview (horizon)

After v26.2.0 ships:
- Extended aux_state parsers (xelatex, lualatex)
- `CSTRoundTrip.v` full proof (lift deferral from B2b)
- Rolling fix coverage for more rules
- Rewrite conflict-aware merge
- partial_document_semantics.yaml

v26.3 is a smaller, more incremental release than v26.1 / v26.2. Estimated 2-3 weeks.

v27 follows: editorial / collaboration / platform. Entirely new product.
