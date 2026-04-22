# Compilation guarantee theorem stack (v26.2 + v27 WS8)

**Status:** v26.2 ships hypothesis-parametric T0–T7 scaffolding; v27 WS8 discharges hypotheses with a concrete toolchain model.
**Authoritative:** memo `REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §5.
**Companion ADR:** [ADR-004](../../docs/v26_2/adr/ADR-004-hypothesis-parametric-t6-t7.md), [ADR-007](../../docs/v26_2/adr/ADR-007-compile-stack-ships-in-v26-2.md).

---

## 1. What this stack claims

> For projects in `LP-Core(engine, profile)`, if parsing succeeds, all
> required artefacts resolve, macro registration is accepted, the
> project DAG is closed, and all Error-level rules pass, then compilation
> succeeds under the selected build profile and yields a well-formed
> output artefact.

This is not one theorem — it's a **stack of eight**, each guarding a
specific step of the compile pipeline. Individually each is simpler; the
composition is the project's compile contract.

---

## 2. The eight theorems

### T0 — Parser acceptance

**Informal:** If source is in `LP-Core`, `Parser_l2.parse` accepts and produces an AST.

**Coq shape** (v26.2, wrapper around existing `ParserSound.v`):
```coq
Theorem T0_parser_accepts :
  forall (s : string),
    in_lp_core s -> exists ast, Parser_l2.parse s = Ok ast.
```

**v26.2 wrapper file:** `proofs/T0_wrapper.v`.
**Status:** mechanized (reuses existing `ParserSound.v`).

### T1 — Expansion admissibility

**Informal:** For admissible user and built-in macros, expansion terminates and preserves language admissibility.

**Coq shape** (v26.2 wrapper around existing `UserExpand.v`):
```coq
Theorem T1_expansion_admissible :
  forall (doc : document) (registry : User_macro_registry.t),
    all_macros_in_subset registry ->
    acyclic_registry registry ->
    exists doc', expand doc registry = Ok doc'.
```

**v26.2 wrapper file:** `proofs/T1_wrapper.v`.
**Status:** mechanized (reuses `UserExpand.v` termination + `UserMacroRegistrySound.v`).

### T2 — Project closure

**Informal:** The project include/build graph is finite, acyclic where required, and all required assets resolve.

**Coq shape** (v26.2, extends existing `ProjectSemantics.v`):
```coq
Theorem T2_project_closed :
  forall (p : project),
    project_well_formed p ->
    acyclic_project p ->
    (forall f, included_from p f -> In f p.(proj_files)).
```

**v26.2 file:** `proofs/ProjectClosure.v`.
**Status:** new mechanization, extends `ProjectSemantics.v`.

### T3 — Build profile admissibility

**Informal:** The selected engine/toolchain profile is compatible with the project's declared features.

**Coq shape** (v26.2):
```coq
Theorem T3_profile_compatible :
  forall (p : project) (prof : profile),
    decidable_feature_support prof p.(declared_features) = true ->
    profile_admits p prof.
```

**v26.2 file:** `proofs/BuildProfileSound.v`.
**Status:** new; decidability is the load-bearing content.

### T4 — Semantic state coherence

**Informal:** Global semantic state over project files is consistent — labels, refs, counters, bibliography, float metadata, etc.

**Coq shape** (v26.2, wrapper around `LabelsUnique.v` + `ProjectSemantics.v`):
```coq
Theorem T4_semantic_coherent :
  forall (p : project),
    T2_project_closed p ->
    labels_globally_unique p /\
    refs_resolve_within p /\
    counters_consistent p /\
    bib_entries_resolve p.
```

**v26.2 wrapper file:** `proofs/T4_wrapper.v`.
**Status:** labels + refs mechanized; counters + bib are
hypothesis-parametric in v26.2, discharged in v27 WS8.

### T5 — Rule safety

**Informal:** If no Error-level rule fires within its proof class / contract class, no statically detectable violation remains inside the contract.

**Coq shape** (v26.2 wrapper around per-rule QED chain):
```coq
Theorem T5_rule_safe :
  forall (p : project) (rules : list rule_t),
    all_error_rules_pass p rules ->
    no_static_violation p.
```

**v26.2 wrapper file:** `proofs/T5_wrapper.v`.
**Status:** mechanized where per-rule proofs exist
(see `proofs/generated/`); gaps documented in `proofs/T5_wrapper.v`
header for rules with only family-level proofs.

### T6 — Compilation progress

**Informal:** Given T0–T5 and bounded build assumptions, the project compiles without fatal errors.

**Coq shape** (v26.2, hypothesis-parametric per ADR-004):
```coq
Section Compile_progress.
  Variable bounded_build_terminates_for : project -> profile -> Prop.
  Hypothesis compile_progress_rule :
    forall p pf,
      T0_accepts p -> T1_admissible p -> T2_closed p ->
      T3_compatible p pf -> T4_coherent p -> T5_safe p ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.

  Theorem T6_compile_progress_under_bound :
    forall p pf,
      T0_accepts p -> T1_admissible p -> T2_closed p ->
      T3_compatible p pf -> T4_coherent p -> T5_safe p ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.
  Proof. intros; apply compile_progress_rule; assumption. Qed.
End Compile_progress.
```

**v26.2 file:** `proofs/CompileProgress.v`.
**Status:** hypothesis-parametric. v27 WS8 instantiates
`bounded_build_terminates_for` and `compile_progress_rule` against a
concrete toolchain model (e.g. `Module PdflatexModel`).

### T7 — Output well-formedness

**Informal:** Produced artefacts satisfy the subset's output contract — valid PDF graph, no missing refs within scope, etc.

**Coq shape** (v26.2, hypothesis-parametric per ADR-004):
```coq
Section Output_wellformed.
  Variable output_format_well_formed : artefact -> Prop.
  Hypothesis output_wellformed_rule :
    forall p pf out,
      compilation_succeeds p pf ->
      produces p pf out ->
      output_format_well_formed out.

  Theorem T7_output_wellformed :
    forall p pf out,
      T6_compile_progress_under_bound p pf ->
      produces p pf out ->
      output_format_well_formed out.
End Output_wellformed.
```

**v26.2 file:** `proofs/CompileWellFormed.v`.
**Status:** hypothesis-parametric. v27 WS8 discharges `output_format_well_formed` against PDF / DVI / PS artefact validators.

---

## 3. Runtime counterpart

Each theorem has a runtime checker in `latex-parse/src/compile_contract.ml`:

```ocaml
val check_ready_to_compile :
  Project_model.t -> Build_profile.t -> ready_check_result

type ready_check_result =
  | Ready
  | NotReady of reason list

type reason =
  | T0_parse_fails of string
  | T1_expansion_fails of string
  | T2_project_not_closed of cycle_or_missing
  | T3_profile_incompatible of string
  | T4_semantic_incoherent of string
  | T5_rule_violations of rule_id list
```

T6/T7 are proof-only at runtime (they say "if everything else holds, compile
succeeds"). Callers don't check T6/T7 at runtime — they check T0–T5 via
`check_ready_to_compile`, invoke the toolchain, and trust T6/T7 to match
the toolchain's behaviour per the v27 WS8 instantiation.

---

## 4. v27 WS8 discharge path

v27 WS8 writes a concrete toolchain model:

```coq
Module PdflatexModel.
  Definition profile := Pdflatex.
  Definition project := ...
  Definition bounded_build_terminates_for (p : project) (pf : profile)
    : Prop := pdflatex_pass_count_bounded p.
  Lemma bounded_pass_count_holds : forall p pf, ... .
  Definition compile_progress_rule : ... := ... .
  Definition output_format_well_formed (out : artefact) : Prop :=
    valid_pdf out.
End PdflatexModel.
```

`PdflatexModel` instantiates the Section Variables from v26.2's
`CompileProgress.v` and `CompileWellFormed.v`, producing concrete
theorems:

```coq
Theorem pdflatex_compile_progress :
  forall p, ... -> compilation_succeeds p Pdflatex.
```

---

## 5. What's NOT covered

- **LP-Extended** (best-effort contract tier): only T0–T5 run; T6/T7 skip.
- **LP-Foreign** (out of contract): all theorems skip; runtime can't make claims.
- **Engine-specific output contracts for xelatex / lualatex:** v27+ scope.
- **Bibliography semantics beyond \bibliography \cite / \newlabel from .aux:** v27 WS8 refinement.
- **Non-deterministic toolchain behaviour** (e.g. pdflatex with different `\write18` settings): out of scope.

---

## 6. References

- Memo §5 — full informal specification of T0–T7.
- ADR-004 — hypothesis-parametric pattern rationale.
- ADR-007 — why v26.2 scaffolding vs v27-only.
- `specs/v26/compilation_profiles.yaml` — machine-readable profile metadata.
- `docs/COMPILATION_GUARANTEE.md` — user-facing summary.
- `proofs/ADMISSIBILITY_MAP.md` — (created in PR A3) maps every
  hypothesis T6/T7 rely on to v27 WS8 discharge tasks.
