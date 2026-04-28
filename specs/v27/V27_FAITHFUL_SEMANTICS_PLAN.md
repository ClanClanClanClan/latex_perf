# V27_FAITHFUL_SEMANTICS_PLAN — Faithful operational pdflatex semantics

**Goal:** Replace the abstract `pdflatex_step` (counter-bounded
iteration that doesn't model real aux/log evolution) in
`proofs/PdflatexModel.v` with an operational semantics that
processes a token stream, evolves real aux/log state, and emits
fatal markers per pdflatex's actual error model.

**Tag target:** v27.1.0 (major refinement of the WS8 capstone proof).

**Scope estimate:** 6–8 sessions across stages.

## Why this matters

The current `pdflatex_compile_safe` is unconditional under the
abstract pass-iteration model — but the model's faithfulness to real
pdflatex behavior is undefended. The user-facing claim "pdflatex
will compile this project successfully" rests on whether our model
mirrors pdflatex's actual aux/log evolution and convergence behavior.

The faithful semantics has two pillars:
1. **Token-driven aux/log evolution** — each token category (text,
   command, math, label-def, label-ref, environment, etc.) has a
   defined effect on aux state and log state.
2. **Convergence under bounded label/ref counts** — repeated passes
   converge once aux state stabilizes (the standard pdflatex 2-pass
   then "no rerun needed" termination).

## Stage decomposition

### Stage 1 — Token model
**Branch:** `v27.1/faithful-stage1-token-model`

Define a Coq mirror of the existing `Parser_l2` token categorization,
sufficient for aux/log effects. Likely:

```coq
Inductive pdflatex_token :=
  | Tok_text     (bytes : list nat)
  | Tok_command  (name : list nat) (args : list (list nat))
  | Tok_math     (body : list nat)
  | Tok_label_def (name : list nat)        (* \label{name} *)
  | Tok_label_ref (name : list nat)        (* \ref{name} *)
  | Tok_env_begin (name : list nat)
  | Tok_env_end   (name : list nat)
  | Tok_other.

Fixpoint tokenize (input : list nat) : list pdflatex_token := ...
```

Use the existing `RewritePreservesCST` byte-filter tokenizer as a
starting point (Coq side, not OCaml runtime).

**Acceptance:** `tokenize` defined, exhaustive over input, Qed
lemma `tokenize_preserves_byte_count`.

### Stage 2 — Aux state evolution
**Branch:** `v27.1/faithful-stage2-aux-step`

Refine `aux_state := list (label_def + ref_use)` with concrete
shape. Define:

```coq
Record aux_state := mk_aux {
  defined_labels : list (list nat);   (* names defined so far *)
  used_refs      : list (list nat);   (* names referenced *)
}.

Definition aux_step_token (s : aux_state) (t : pdflatex_token) : aux_state :=
  match t with
  | Tok_label_def n => mk_aux (n :: s.(defined_labels)) s.(used_refs)
  | Tok_label_ref n => mk_aux s.(defined_labels) (n :: s.(used_refs))
  | _ => s
  end.

Fixpoint aux_step_pass (s : aux_state) (toks : list pdflatex_token) : aux_state :=
  match toks with
  | [] => s
  | t :: rest => aux_step_pass (aux_step_token s t) rest
  end.
```

Aux state convergence: a pass `aux_step_pass` is idempotent once the
defined_labels set stabilizes.

**Acceptance:** `aux_step_pass` Fixpoint defined; `aux_step_token`
type-checks; idempotence lemma `aux_pass_stable_after_2`.

### Stage 3 — Log state evolution + fatal-marker emission
**Branch:** `v27.1/faithful-stage3-log-step`

Define:

```coq
Definition log_step_token (s : log_state) (t : pdflatex_token)
                          (aux : aux_state) : log_state :=
  match t with
  | Tok_label_ref n =>
      if In_dec _ n aux.(defined_labels) then s
      else (* emit "Reference \\?? on page ?? undefined" warning *)
           append_warning s n
  | _ => s
  end.
```

Connect `log_no_fatal` to "no fatal-marker substring in the
log_step_pass output". The existing `fatal_markers` list (from
v27.0.1) extends the byte detection.

**Acceptance:** log emission proves `log_no_fatal` for clean (all
labels defined) projects; counter-example case (undefined label
emits warning, not fatal — fatal is only for catastrophic errors).

### Stage 4 — `pdflatex_pass_step` operational pass
**Branch:** `v27.1/faithful-stage4-pass-step`

Combine: one pass of pdflatex tokenizes the input, evolves both aux
and log state, and updates `converged` based on whether aux state
changed.

```coq
Definition pdflatex_pass_step (s : pdflatex_pass_state)
                               (input : list nat) : pdflatex_pass_state :=
  let toks := tokenize input in
  let new_aux := aux_step_pass s.(aux_state_v2) toks in
  let new_log := log_step_pass s.(log_state) toks new_aux in
  mk_pdflatex_pass_state
    (S s.(pass_count))
    new_aux
    new_log
    (aux_eq s.(aux_state_v2) new_aux).
```

The `converged` flag is now MEANINGFUL — it's true iff the aux
state didn't change this pass.

**Acceptance:** `pdflatex_pass_step` defined; convergence happens
when aux state stabilizes; preserves `log_no_fatal` invariant.

### Stage 5 — Convergence theorem
**Branch:** `v27.1/faithful-stage5-convergence`

Prove: under bounded label/ref counts (defined ≤ N labels, ≤ N
references, where N is finite), `iterate_pass_step` converges in
at most 2 passes.

```coq
Theorem pdflatex_pass_converges_bounded :
  forall (input : list nat) (s0 : pdflatex_pass_state),
    bounded_labels input ->
    exists k, k <= 2 /\
              (iterate_pass_step s0 k input).(converged) = true.
```

This replaces the abstract counter-bound with a real convergence
result.

**Acceptance:** convergence theorem Qed; `bounded_labels` predicate
defined; theorem instantiates the WS8 `pdflatex_bounded_terminates`
universal.

### Stage 6 — Re-prove WS8 capstone
**Branch:** `v27.1/faithful-stage6-recapstone`

Update `proofs/PdflatexModel.v` to use the Stage-1–5 faithful
semantics. Re-prove:
- `pdflatex_compile_progress_rule_proof` against the new
  `compilation_succeeds`.
- `pdflatex_output_wellformed_rule_proof` against the new
  `produces` (artefact = (canonical_pdf, log) computed from the
  faithful pass).
- `pdflatex_compile_safe` capstone with the faithful inputs.

**Acceptance:**
- `Print Assumptions pdflatex_compile_safe` still Closed under the
  global context.
- 0 admits, 0 axioms.
- Differential 0 diffs vs predecessor tag.

### Stage 7 — Release-bump v27.1.0
**Branch:** `v27.1/release-bump`

Bump version, CHANGELOG `[v27.1.0]` entry.

## Multi-session memory protocol

`~/.claude/.../memory/v27_faithful_status.md` carries cross-session
state per the WS8 template.

## Acceptance criteria for the capstone

- [ ] `tokenize` Coq mirror of `Parser_l2` defined.
- [ ] Aux-state evolution defined; idempotence after stabilization.
- [ ] Log-state evolution defined; fatal markers emitted faithfully.
- [ ] `pdflatex_pass_step` operational; `converged` flag meaningful.
- [ ] Convergence theorem (≤ 2 passes for bounded labels) Qed.
- [ ] WS8 capstone re-proved against faithful semantics.
- [ ] All `Print Assumptions` Closed.
- [ ] CHANGELOG `[v27.1.0]` entry.
- [ ] Tag v27.1.0 on main.
