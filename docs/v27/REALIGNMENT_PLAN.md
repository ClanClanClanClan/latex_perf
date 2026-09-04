# Realignment plan — back to the actual goal (v2)

> **Status:** proposal, rewritten 2026-09-04 after the first draft was refuted
> on three structural points. Every number is measured at `main` and sourced.
> v1 is preserved in git history; §7 records what changed and why.

## 1. The goal

`ROADMAP.md:49` — *"A LaTeX document COMPILES if and only if our verified
parser says it will (READY) — as long as it stays within the
non-Turing-complete decidable subset (LP-Core, expandable) — AND it can be
provably checked against a user-defined policy without compiling."*

Five delivery clauses: soundness · **real-time** · the **widest decidable
subset** · a **clearly-labelled heuristic tier** · a **policy substrate** —
on a Coq backbone.

**Metric:** *proven-verdict coverage at ZERO false-READY.*

⚠ The biconditional is not achievable and the ROADMAP concedes it
(`ROADMAP.md:427`). The achievable claim is **one-directional soundness over
LP-Core** — READY ⇒ compiles — with completeness as a measured quality, not a
theorem. The plan targets that.

## 2. Measured position

Published in `PROJECT_STATE.md` §1 (generated, diffed by CI):

| | sample 1 (tuned) | sample 2 (**virgin**) |
|---|---|---|
| correct verdicts | 197/199 = 99.0% | **177/200 = 88.5%** |
| **proven coverage (LP-Core)** | **84/200 = 42.0%** | **76/200 = 38.0%** |
| certified, any tier | 167/200 = 83.5% | 156/200 = 78.0% |
| uncertified ("heuristic") READYs | 17 | 13 |
| **certified FALSE-READY** | 0 | **9** (5 LP-Core) |

## 3. The five facts that decide the plan

**F1 — The model cannot express a single real failure.** Across both samples,
31 documents fail pdflatex. Classified by first error:

| share | class |
|---|---|
| 58.1% | counter/command collision (`\c@`, `\theH`, `\AddToDocumentProperties`) |
| 12.9% | undefined control sequence |
| 9.7% | math-mode violation (PAR-IN-MATH) |
| 6.5% | epstopdf figure missing |
| 6.5% | stray primitive (`\or`) |
| 3.2% | cleveref override |

`body_token` has four constructors (`PdflatexModel.v:127-131`) and a document
can be model-fatal **only** via a dangling build edge (T2) or an unadmitted
feature (T3). **Expressible today: 0 of 31 = 0.0%.** Every fatal we catch, we
catch with the *unproven heuristic belt*.

**F2 — In production the model has ONE fatal channel, not two.**
`Build_graph.of_project` adds every node unconditionally and
`graph_of_build_graph` discards the `exists` bit, so `project_closed_b` is
vacuously true; `declared_features` is always `[]`. Certification therefore
reduces to four features behind ~ten substring guards.

**F3 — Adequacy is not statable, and would be false.** There is no formal
engine model: 0 `Axiom`/`Parameter`/`Hypothesis`/`Admitted` across 76 `.v`
files; the only "engine" is a 4-constructor tag indexing an 8×4 table. Writing
`engine_fatal` requires either an axiom (breaks the required
`Print Assumptions … Closed` gate) or a TeX interpreter in Coq. As stated,
*engine-fatal ⇒ model-fatal* unfolds to *model-fatal ⇒ model-fatal*. And the
five LP-Core false-READYs are each provably model-fatal-free, so the statement
is false at the current abstraction.

**F4 — The metric has two independent legs.** Coverage =
`LP-Core ∧ certified ∧ compiles`. Closing all 9 false-READYs moves coverage
**76/200 → 76/200**: false-READY work satisfies the *constraint*, never the
numerator. They need separate programmes.

**F5 — Subset extension moves the numerator, not accuracy.**
`compile_contract.ml:170` is `| (LP_Core | LP_Extended), _ ->` — the tier is
not consulted, so E-track buys zero accuracy. But the metric is *coverage*,
and E1 raises the LP-Core ceiling ~38.9% → ~57.6%. v1 excluded E-track using
an accuracy argument against a coverage metric: a category error, now
reversed.

## 4. Plan

### Phase A — Say only what is true (S, days)

- **A1** Gate the Coq citation on LP-Core. `print_model_connected_verdict`
  takes the tier; today an LP-Foreign document can print it (measured).
- **A2** Certification channel `PROVEN` / `HEURISTIC` beside the verdict.
  Exit codes unchanged so all 82 fixtures survive. The three states already
  exist internally; `ROADMAP.md:334` already specifies them.
- **A3** Stop printing "compiles" for what is a premise-check. Given F1/F2 the
  honest string names the premises verified (T2 closure, T3 features), not a
  compilation guarantee. *Relabelling without this is not honesty.*
- Already shipped: publishing the metric and both samples, and labelling the
  constructed governance numbers.

### Phase B — The constraint leg: zero false-READY

- **B1** epstopdf detector — OPEN-047, 2 of the 9, cheapest reduction. **M**
- **B2** Triage the remaining 7 against §3's class table: each becomes either
  a detector (heuristic belt) or a model widening (Phase D). **M**
- **B3** Keep the belt honest. C-41 (the tier filter silencing the whole
  compile-blocking belt) is fixed; the class is "a change that silently
  re-parameterises another subsystem". **done**

### Phase C — The coverage leg: grow the numerator

Ranked by measured gain per unit effort.

- **C1** **T4-nodup inapplicability — the cheapest coverage gain in the repo.**
  17 documents on sample 1 (10 LP-Core) are READY but *uncertified* because
  the `nodup` premise is unmet — duplicate `\label`s, which pdflatex merely
  warns about and OPEN-008 already ruled harmless. Align the premise with that
  decision and up to +5pp lands immediately. **S-M**
- **C2** Residual over-rejection among LP-Core documents (14 on sample 2).
  **M**
- **C3** E-track E1, benign `\def` admission — the ceiling item, reinstated.
  **L**

### Phase D — Make "proven" mean something

Not adequacy (F3). In dependency order:

- **D1** `model_fatal_iff` — a characterisation theorem turning F1/F2 from
  prose into `Qed`, with `vm_compute`d counterexamples keyed to arXiv ids.
  Cheap, and it makes the weakness *provable* rather than asserted. **S**
- **D2** Resurrect the dead T2 channel: stop discarding `exists`, put
  `\includegraphics` targets in the build graph. Reuses `edge_token` /
  `node_known_b` / `project_closed`, which are already proved — zero new
  capstone obligations, catches 2 of the 9. **S-M**
- **D3** Widen `body_token` along §3's ranking, each constructor with an
  extraction-faithfulness lemma. The 58% counter-collision class needs
  declaration state in the model; that is the real frontier. **L-XL,
  incremental, measured against F1's table after each step.**
- **D4** `DetectComplete.v` — ground the subset boundary. Meaningful only
  after A1 makes the verdict depend on the tier. **L**
- **D5** Q-ENGINE. The alias
  (`xelatex_compile_safe := pdflatex_compile_safe`) is not the defect — no
  runtime path can select a non-pdflatex engine, so scope the claim in docs
  and defer the proof. **S** (was over-sized in v1)

### Phase E — The second conjunct: policy

- **E1** `--policy` must be able to **fail**. It returns exit 0
  unconditionally, so no submission pipeline can gate on it. Cheapest
  product-relevant fix in the repo. **S**
- **E2** Make features compose — `--compile-check` and `--policy` are
  mutually-exclusive arms of a 24-way exact-argv match. This is an argv
  rewrite touching every subcommand, not a flag. **M** (under-sized in v1)
- **E3** Additive `require`/`forbid` DSL over the project closure, using the
  subtractive half's existing admit-free Coq proof as the template. **M-L**
  ⚠ Do **not** implement G2 by merging `editorial_policy.apply` into the
  compile path — measured, it manufactures false-READYs.

### Phase F — Real-time

- **F1** Instrument the three uninstrumented budgeted stages. The
  gate-aiming half already shipped. **S**
- **F2** Readiness-path regression gate — the #565-#572 run added ~3 closure
  walks and ~4 invocations with nothing watching. **S**
- **F3** `rules` at 284 ms against a 30 ms budget @300 KB. Architectural. **L**
- **F4** Warm session / LSP. Without it the per-keystroke promise has no
  delivery vehicle and users pay cold process cost. **L**

### Phase G — The rule side (best value/effort in the repo)

1. i18n gated golden suite **silently skipped** (missing dune dep) — one line;
   355→366 PASS. It is the only live assertion of language gating. **S**
2. **L3-006 registered twice** — every document ships duplicate findings. **S**
3. **CHAR-004** catalogued `Reserved`, fires in production, duplicates
   ENC-008 at a different severity. **S**
4. Relabel the **fake mutation metric** (it greps for the rule id; no
   mutation, 30% floor). **S**
5. **Language gating is dead** — 46 rules carry a `languages` list, `run_all`
   never filters. **M**
6. 49 STYLE rules are Class D and never run by default; 30 TYPO rules
   (incl. Error-severity TYPO-006) sit behind an undocumented env var. **M**
7. `compile_blocking_ids` overstates the belt ~3× — 24 of 36 ids can never
   reach the Error severity T5 requires. Correct the list or the docs. **S**
8. Proof posture: prove rules against the **shipped** code, or stop calling
   803 one-line instantiations soundness proofs. **XL**

### Cross-cutting

- **Every release grades a virgin sample.** Sample 1 is burned: every fix in
  the #565-#572 run was tuned against it.
- **Published numbers are measured, never constructed** (C-40), enforced by
  `check_doc_consistency.py`.
- **Adversarialize compositions *and* re-parameterisations** — C-36 (two new
  changes composing) and C-41 (a new change silently re-parameterising an old
  subsystem).
- Use the `OPEN-nnn` ledger ids. Do not open a parallel backlog.

## 5. Order of execution

**A1-A3 → B1 → C1 → D1/D2 → E1** is the first working set: it stops the false
claims, removes the cheapest false-READY, takes the cheapest coverage gain,
makes the model's weakness provable, and gives the policy channel a verdict.
Phases F and G are independent and can run whenever capacity exists; G has the
best value-to-effort ratio in the repo.

## 6. What this plan refuses

- **Adequacy as stated** — not statable, and false at the current abstraction.
- **More heuristic detectors merely to reduce over-rejection.** That work is
  done (58→2 in-sample) and is not the constraint.
- **Calling the verdict "proven" while F1 holds.** Until D3 moves the 0-of-31,
  the certificate's contribution to fatal detection on real documents is zero,
  and the shipped string must say so.

## 7. What changed from v1, and why

| v1 | v2 | reason |
|---|---|---|
| Phase 2.1 = prove adequacy | deleted; replaced by D1-D3 | not statable (no engine model); false as stated (5 LP-Core counterexamples) |
| Phase 1 = certification predicate, own phase, M | folded into A2 | measured: moves coverage 76/200 → 76/200 — a relabel |
| §5 excluded the E-track | reinstated as C3 | category error: an accuracy argument against a coverage metric |
| "the model has two fatal channels" | one (F2) | `exists` discarded at the graph boundary; T2 is vacuous in production |
| Phase 0.3/0.4 pending | already shipped | landed in the doc-reconciliation PR |
| multi-engine = L | S (D5) | no runtime path selects an engine; the alias is unexercisable |
| 24-way argv = flag fix | M (E2) | it is a parser rewrite |
| "language gating is over-rejection" | corrected in G5 | false against this plan's own definition |
| no failure-class measurement | §3 F1 table | the number that decides the whole verification programme, previously unmeasured |
