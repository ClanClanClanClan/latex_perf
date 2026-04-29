# V27_T5_WIRING_PLAN — Substantive T5 wiring against per-rule QEDs

**Goal:** Replace the `pdflatex_T5_safe (_ : pdflatex_project) := True`
placeholder in `proofs/PdflatexModel.v` with a Section closure of
`T5_wrapper.T5_rule_safe` over a concrete pdflatex `rule_id` /
`rule_passes` / `no_static_violation` instantiation, threading the
per-rule QED chain in `proofs/generated/` as the substantive content.

**Tag target:** v27.0.x or v27.1.x (single-digit alpha cycle).

**Scope estimate:** 4–6 sessions across stages.

## Why this is non-trivial

`T5_wrapper` is a Coq `Section` parametric in:
- `Variable rule_id : Type` — abstract identifier type
- `Variable rule_passes : rule_id -> Prop` — "this rule passes"
- `Variable no_static_violation : list rule_id -> Prop` — meta predicate
- `Hypothesis rule_safety_rule : forall rules, all_error_rules_pass rules -> no_static_violation rules`

To wire substantively from `pdflatex_project`, we must:
1. Pick a concrete `rule_id`. Two natural choices:
   (a) `rule_id := string` (FAMILY-NNN names from `rule_contracts.yaml`),
   (b) `rule_id := nat` (rule index into the catalogue).
2. Define `pdflatex_rule_passes : pdflatex_project -> rule_id -> Prop`
   tying back to the per-rule soundness QEDs in `proofs/generated/`.
3. Define `pdflatex_no_static_violation : pdflatex_project ->
   list rule_id -> Prop` capturing "for the project, every rule in
   the list yields no Error-level violation".
4. Discharge `rule_safety_rule` for these instantiations.

The challenge is wiring step (2) — the per-rule QEDs in
`proofs/generated/*.v` each prove rule-specific soundness against a
particular AST/CST shape. Lifting that to a single
`pdflatex_rule_passes p r` predicate requires a map from `rule_id`
to per-rule soundness witness.

## Stage decomposition

### Stage 1 — Pick the carrier
**Branch:** `v27.0/T5-stage1-rule-id-carrier`

- Decide `rule_id` representation. **Recommendation:** `rule_id :=
  string` (matches the FAMILY-NNN format already in
  `specs/rules/rule_contracts.yaml`).
- Add a `proofs/T5_concrete.v` file with:
  - `Definition rule_id : Type := string.`
  - `Definition pdflatex_rule_passes_pred (p : build_graph) (r : rule_id) :
     Prop := True.` (Stage 1 placeholder; refined later)
  - `Definition pdflatex_no_static_violation_pred (p : build_graph)
     (rs : list rule_id) : Prop := True.` (Stage 1 placeholder)
- Stage 1 zero-admit witness.
- Update `_CoqProject` to register `proofs/T5_concrete.v`.

**Acceptance:** `dune build proofs` green; the new file compiles
with placeholder predicates.

### Stage 2 — Discharge `rule_safety_rule` against placeholders
**Branch:** `v27.0/T5-stage2-rule-safety-rule`

Apply `T5_wrapper.T5_rule_safe` Section closure with the Stage-1
placeholders. Discharge `rule_safety_rule` trivially (since
`no_static_violation_pred := True`):

```coq
Lemma pdflatex_rule_safety_rule_proof :
  forall (p : build_graph) (rules : list rule_id),
    (forall r, In r rules -> pdflatex_rule_passes_pred p r) ->
    pdflatex_no_static_violation_pred p rules.
Proof. intros p rules _. exact I. Qed.
```

**Acceptance:** Section closure produces a `pdflatex_T5_safe_v2`
theorem; placeholder proof closes; build green.

### Stage 3 — Refine `pdflatex_rule_passes_pred` to per-rule QED reference
**Branch:** `v27.0/T5-stage3-rule-passes`

For each `string` matching a FAMILY-NNN rule that has a per-rule
soundness QED in `proofs/generated/`, link the predicate to the
generated theorem. Pattern:

```coq
Definition pdflatex_rule_passes_pred (p : build_graph) (r : rule_id) : Prop :=
  match r with
  | "TYPO-001"%string => TYPO_001_sound_some_concrete_premise p
  | "TYPO-002"%string => TYPO_002_sound_some_concrete_premise p
  ...  (* one per rule with a generated QED *)
  | _ => True  (* unknown rule passes vacuously *)
  end.
```

**Acceptance:** the predicate type-checks, the per-rule QEDs are
referenced, build green.

### Stage 4 — Refine `pdflatex_no_static_violation_pred`
**Branch:** `v27.0/T5-stage4-no-violation`

Strengthen `no_static_violation_pred` to claim "no rule in `rules`
fires on `p`":

```coq
Definition pdflatex_no_static_violation_pred (p : build_graph)
    (rules : list rule_id) : Prop :=
  forall r, In r rules -> ~ rule_fires_on_project r p.
```

Where `rule_fires_on_project` is defined to mirror the runtime
validator's "this rule emits an Error-level finding on the project".

**Acceptance:** the new predicate is meaningful (not True), and
`pdflatex_rule_safety_rule_proof` still discharges (now with real
content following from per-rule QEDs).

### Stage 5 — Wire into PdflatexModel.v
**Branch:** `v27.0/T5-stage5-wire-into-capstone`

In `proofs/PdflatexModel.v`:
- Replace `pdflatex_T5_safe (_ : pdflatex_project) := True` with
  the Stage-4 wired form.
- Replace `pdflatex_T5_safe_holds := I` with a real
  Qed proof using `pdflatex_rule_safety_rule_proof`.
- Update `pdflatex_compile_safe` capstone proof: T5 hypothesis
  discharge now needs a witness for "all rules pass" — supply via
  `pdflatex_T5_safe_holds`.

**Acceptance:**
- `dune build` green.
- `Print Assumptions pdflatex_compile_safe` still "Closed under the
  global context".
- `Print Assumptions pdflatex_T5_safe_holds` Closed.
- Differential test 0 diffs vs predecessor tag.

### Stage 6 — Release-bump + tag
**Branch:** `v27.0/T5-release-bump`

Bump version, regenerate facts, add CHANGELOG entry. Tag the
resulting release.

## Multi-session memory protocol

Each stage ends by writing a memory entry under
`~/.claude/.../memory/v27_T5_status.md`:
1. **What's done** — file:line markers for new theorems; each Qed.
2. **What's next** — the next stage's first concrete action.
3. **State-of-mind** — proof obligations open; pitfalls; type
   surprises (e.g. string equality decidability requirements).
4. **Verification numbers** — theorem count delta, gate state.

## Acceptance criteria for the capstone (state at v27.0.2)

- [x] `proofs/T5_concrete.v` exists; Section closure applied (PR #313
  scaffold, #314 closure, #315 catalogue-parametric).
- [x] `pdflatex_T5_safe (p : pdflatex_project)` is substantive
  (universal-over-catalogue, not `True`); `pdflatex_T5_safe_holds`
  Qed-proves it via `T5_concrete.pdflatex_T5_safe_stage2` (PR #317).
- [x] `pdflatex_compile_safe` proof still goes through (T5 hypothesis
  discharge via `apply pdflatex_T5_safe_holds`).
- [x] All `Print Assumptions` Closed under the global context
  (verified for: `pdflatex_compile_safe`, `pdflatex_T5_safe`,
  `pdflatex_T5_safe_holds`, `pdflatex_T5_safe_stage2`,
  `pdflatex_rule_safety_rule_proof`, `pdflatex_T5_safe_proved`,
  `pdflatex_T5_safe_for_full_catalogue`).
- [x] CHANGELOG entry under `[v27.0.2]` lists the 5-stage T5 cycle
  + architectural note (PR #318).
- [x] `proofs/ADMISSIBILITY_MAP.md` T5 entry flipped from
  "WS8 discharge: no new work" to "DISCHARGED in v27.0.2" with
  detailed STATUS callout (PR #318).
