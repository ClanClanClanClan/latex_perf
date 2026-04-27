# V27 WS8 — Discharge T6 / T7 against `proofs/PdflatexModel.v`

**Status:** draft, 2026-04-27. Successor to `V26_4_PLAN.md` §5
commitment + `proofs/ADMISSIBILITY_MAP.md` "v27 WS8 discharge
checklist".
**Scope:** flip the last two `HYPOTHESIS-PARAMETRIC` entries in
`ADMISSIBILITY_MAP.md` (T6 `compile_progress_rule` and T7
`output_wellformed_rule`) to `DISCHARGED`, producing an unconditional
`PdflatexModel.pdflatex_compile_safe` theorem with `Qed`.
**Cadence:** **multi-session** (this is genuine multi-week formal-
verification work — see `V27_REPO_EXACT_MASTER_SPEC.md` §9 timeline,
WS8 in Phase 2). Memory carries state across sessions per the
project's auto-memory convention; each session ships a tagged
release if practical.

## 0. Pre-conditions (verified 2026-04-27 on `main` `7b9a766`)

- `v26.4.0` tagged; cycle PRs #281–#284 merged.
- 17/17 pre-release gates PASS.
- 1,291 theorems / 161 .v files / 0 admits / 0 axioms.
- `proofs/ADMISSIBILITY_MAP.md` has only T6 + T7 still
  `HYPOTHESIS-PARAMETRIC`; CSTRoundTrip / RewritePreservesCST /
  RewritePreservesSemantics all unconditionally discharged in
  v26.3/v26.3.1/v26.4.
- `proofs/CompileProgress.v` (135 lines, T6 Section) and
  `proofs/CompileWellFormed.v` (97 lines, T7 Section) are stable
  per `docs/v26_2/adr/ADR-004-hypothesis-parametric-t6-t7.md` and
  exporters' tests.
- T0–T5 wrappers exist (`T0_wrapper.v`, `T1_wrapper.v`,
  `ProjectClosure.v`, `BuildProfileSound.v`, `T4_wrapper.v`,
  `T5_wrapper.v`); each provides at least the trivial discharge
  witness, several have substantive supporting theorems.

## 1. Multi-session roadmap

The discharge decomposes into six numbered stages. Each stage is
sized to fit a single working session and lands a tagged release
when its content is closed. Memory at each session boundary
captures: (a) what's done, (b) what's next, (c) what local
state-of-mind is needed to resume.

### Stage 1 (THIS cycle, target tag v26.5.0)

**Deliverables:**
- `specs/v27/V27_WS8_PLAN.md` — this file.
- `proofs/PdflatexModel.v` — carriers + T0–T5 predicate
  instantiations + invocation of `CompileProgress.Section` and
  `CompileWellFormed.Section` with concrete arguments.
  Section closure still leaves `compile_progress_rule` and
  `output_wellformed_rule` as `Hypothesis` arguments, so the
  Stage 1 top-level theorems are **PARAMETRIC ONLY in those two
  hypotheses** — strictly stronger than the upstream Section's
  parametric form.
- `proofs/ADMISSIBILITY_MAP.md` annotations updated: T6 and T7
  entries note "Stage 1 scaffolded in v26.5.0 / `PdflatexModel.v`;
  full discharge in v27.0.0 final".
- `_CoqProject` registers the new file.
- 0 admits / 0 axioms maintained.
- Stage 1 fits in a single session.

### Stage 2 (next session, target tag v27.0.0-alpha1)

**Deliverables:**
- `proofs/PdflatexModel.v` extended with a concrete pass-iteration
  model:
  - `Record pdflatex_pass_state := { pass_count : nat; aux_state :
    aux_image; log_state : log_image; converged : bool }`.
  - `Definition pdflatex_step : pdflatex_pass_state ->
    pdflatex_pass_state` — one pass.
  - `Theorem pdflatex_pass_count_bounded :
      forall s, exists k, k <= 5 /\
      pdflatex_pass_state_after_k_steps s k = converged_state`.
  This is the `bounded_build_terminates_for` discharge content.
- T6 stage-2 progress: PdflatexModel exposes `pdflatex_bounded_terminates`
  as a Qed-proved lemma; the parametric `compile_progress_rule` from
  Stage 1 starts taking concrete shape.

### Stage 3 (T6 capstone, target tag v27.0.0-alpha2)

**Deliverables:**
- `Lemma pdflatex_compile_progress_rule_proof :
    forall p pf, T0_accepts p -> ... -> bounded_terminates p pf ->
    compilation_succeeds p pf.`
  Proof: induction on `pass_count`. Each pass either advances
  (`converged := false`) or stops (`converged := true`); at
  convergence, T5 (rule safety) + T0–T4 imply no fatal error
  surfaces in the log image; therefore `compilation_succeeds`
  (defined in Stage 2 as `clean_exit /\ no_fatal_in_log`) holds.
- Apply this lemma to discharge `compile_progress_rule`.
- ADMISSIBILITY_MAP: T6 flipped to `DISCHARGED`.

### Stage 4 (artefact wellformedness predicates, target tag v27.0.0-alpha3)

**Deliverables:**
- `Inductive pdf_artefact := mk_pdf { pdf_objects : list pdf_object;
    pdf_xref : list nat; pdf_trailer : trailer_record }.`
- `Definition valid_pdf_graph : pdf_artefact -> Prop` — every object
  reference resolves; `xref` and `trailer` are mutually consistent.
- `Definition log_artefact := list nat.`
- `Definition log_no_fatal : log_artefact -> Prop` — no fatal-marker
  byte sequence appears.
- `Definition produces : pdflatex_project -> pdflatex_profile ->
    pdflatex_artefact -> Prop` — concrete tying to the pdflatex_step
    model from Stage 2.

### Stage 5 (T7 capstone, target tag v27.0.0-alpha4)

**Deliverables:**
- `Lemma pdflatex_output_wellformed_rule_proof :
    forall p pf out,
      pdflatex_T6_compile_succeeds p pf ->
      produces p pf out ->
      output_format_well_formed out.`
  Proof: case-split on `out`'s artefact tag (PDF / LOG); for PDF,
  Stage 4's xref/trailer consistency invariants are preserved by
  pdflatex_step; for LOG, no fatal markers (Stage 3 conclusion).
- Apply this lemma to discharge `output_wellformed_rule`.
- ADMISSIBILITY_MAP: T7 flipped to `DISCHARGED`.

### Stage 6 (capstone + release, target tag v27.0.0)

**Deliverables:**
- `Theorem pdflatex_compile_safe :
    forall p pf,
      project_well_typed p ->
      profile_supported pf ->
      exists out,
        produces p pf out /\
        compilation_succeeds p pf /\
        output_format_well_formed out.`
  Final unconditional theorem. Closes the entire compile-guarantee
  stack.
- `proofs/ADMISSIBILITY_MAP.md`: every `HYPOTHESIS-PARAMETRIC`
  annotation removed; v27 WS8 discharge checklist all checked.
- `docs/COMPILATION_GUARANTEE.md`: "v27 scope" boxes flipped to
  "now proved for pdflatex".
- `CHANGELOG.md`: `[v27.0.0]` entry lists the unconditional
  theorems and any bounded-pass constants used.
- Tag v27.0.0.

## 2. Carriers + their instantiations

Per `proofs/CompileProgress.v::Section Compile_progress` and
`proofs/CompileWellFormed.v::Section Output_wellformed`, the
Section parameters and their PdflatexModel instantiations are:

| Section variable | PdflatexModel instantiation | Defined in |
|---|---|---|
| `Project : Type` | `pdflatex_project` (alias of `ProjectClosure.build_graph`) | Stage 1 |
| `Profile : Type` | `pdflatex_profile` (record bundling `engine` + `list feature`) | Stage 1 |
| `Artefact : Type` | `pdflatex_artefact` (sum of `pdf_artefact + log_artefact`) | Stage 4 |
| `T0_accepts` | `T0_wrapper.parser_accepts` (already trivial Qed in v26.2) | Stage 1 |
| `T1_admissible` | `T1_wrapper.expansion_admissible` (already Qed) | Stage 1 |
| `T2_closed` | `ProjectClosure.project_closed` | Stage 1 |
| `T3_compatible` | `BuildProfileSound.profile_admits` | Stage 1 |
| `T4_coherent` | `T4_wrapper.labels_unique` | Stage 1 |
| `T5_safe` | `T5_wrapper.rule_safe_predicate` | Stage 1 |
| `bounded_build_terminates_for` | `pdflatex_bounded_terminates` (proved in Stage 2) | Stage 2 |
| `compilation_succeeds` | `pdflatex_clean_exit /\ pdflatex_log_no_fatal` | Stage 2 |
| `compile_progress_rule` | discharged as `pdflatex_compile_progress_rule_proof` | **Stage 3** |
| `T6_compile_succeeds` | `pdflatex_compile_succeeds` (= compilation_succeeds) | Stage 4 |
| `produces` | `pdflatex_produces` (concrete tying to `pdflatex_step`) | Stage 4 |
| `output_format_well_formed` | `valid_pdf_graph \/ log_no_fatal` | Stage 4 |
| `output_wellformed_rule` | discharged as `pdflatex_output_wellformed_rule_proof` | **Stage 5** |

## 3. Memory protocol

Each stage's session ends by writing a memory entry describing:

1. **What's done** — concrete file:line markers for the new
   theorems and definitions, with each Qed listed.
2. **What's next** — the next stage's first concrete action.
3. **Local state-of-mind** — proof obligations open, notation
   choices made, any pitfalls encountered (e.g., dependent-type
   issues, opam install flakes that affected the build).
4. **Verification numbers** — theorem count delta, gate state.

Stage 1's memory entry is written at the end of THIS session.
Stages 2–6 each open with reading the memory + their predecessor's
entry, and close with their own entry.

The cross-session continuity rule:

> Memory carries state. Sessions are stateless. Each session's
> first concrete action is `git pull origin main && dune build &&
> read proofs/ADMISSIBILITY_MAP.md && read this plan file +
> v27_ws8_status.md`.

## 4. ADMISSIBILITY_MAP discharge checklist (replicated for tracking)

Per `proofs/ADMISSIBILITY_MAP.md` v27 WS8 section:

- [ ] `proofs/PdflatexModel.v` created — Stage 1
- [ ] `pdflatex_project / profile / artefact` types defined —
      Stages 1 + 4
- [ ] Each T0–T5 predicate instantiated — Stage 1
- [ ] `bounded_build_terminates_for := pdflatex_passes_bounded`
      proved — Stage 2
- [ ] `compile_progress_rule` discharged as theorem — **Stage 3**
- [ ] `output_format_well_formed := valid_pdf_graph` defined —
      Stage 4
- [ ] `output_wellformed_rule` discharged — **Stage 5**
- [ ] `pdflatex_compile_safe` shipped with Qed — Stage 6
- [ ] `proofs/ADMISSIBILITY_MAP.md` updated — Stage 6
- [ ] `docs/COMPILATION_GUARANTEE.md` updated — Stage 6
- [ ] `CHANGELOG.md` `[v27.0.0]` entry — Stage 6

## 5. Acceptance criteria for v27.0.0 (the WS8 capstone)

- All 17 pre-release gates green (no new gate; the existing
  proof-ci gate covers the new theorems).
- 0 admits / 0 axioms maintained (hard gate).
- `proofs/ADMISSIBILITY_MAP.md` contains zero `HYPOTHESIS-PARAMETRIC`
  annotations.
- `pdflatex_compile_safe` is a Qed-closed theorem with a
  fully-named hypothesis-free signature.
- `docs/COMPILATION_GUARANTEE.md` mentions "unconditional for
  pdflatex".
- Theorem count is ≥ 1,400 (estimated +110 from Stages 2–6
  combined; Stage 1 alone adds ~30).
- Differential test 0 diffs (no runtime change).

## 6. First concrete action — Stage 1, this session

This file is being created on branch `v26.5/cycle`. The next commit
on that branch is `proofs/PdflatexModel.v` Stage 1. After it lands,
the cycle continues with rolling fix producers (§7) and ends at the
v26.5.0 release-bump PR.

## 7. Stage-1 cycle byproduct: small fix-producer batch

While Stage 1 is the headline of the v26.5.0 cycle, the cycle also
ships a small rolling-fix-producer batch (3–5 rules) — primarily
the §1.3 leftover candidates from `V26_4_PLAN.md` that turned out
tractable. Per the established pattern, fix producers are bounded
incremental work and don't compete with the WS8 staging.
