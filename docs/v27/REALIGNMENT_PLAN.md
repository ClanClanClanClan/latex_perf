# Realignment plan — back to the actual goal

> **Status:** proposal, 2026-09-04. Written after an 8-PR run that improved
> heuristic precision and reported it as the North Star. Every number below is
> measured at `main = 11e2fe0a` and sourced; where a claim is inherited from a
> document rather than measured, it says so.

## 0. The goal, restated (ROADMAP.md:49)

> A LaTeX document COMPILES **if and only if** our verified parser says it will
> (READY) — as long as it stays within the **non-Turing-complete decidable
> subset** (LP-Core, expandable) — **AND** it can be **provably checked against
> a user-defined policy without compiling**.

Delivered with (1) verdict soundness, (2) **real-time** as-you-type, (3) the
**widest decidable subset** we can prove, (4) a **clearly-labelled heuristic
tier**, (5) a **policy substrate** — on a Coq backbone.

Success metric: **proven-verdict coverage at ZERO false-READY.**

## 1. Where we actually are (measured)

| dimension | measured | source |
|---|---|---|
| verdict correctness, tuned sample | 197/199 = 99.0%, false-READY 0 | `results.json` |
| verdict correctness, **virgin** sample | **177/200 = 88.5%, false-READY 9 (4.5%)** | `results_sample2.json` |
| of those 9 false-READYs | **all print MODEL-READY; 5 are LP-Core** | this session |
| **defensible proven coverage** | **84/200 = 42.0%** | LP-Core ∧ certified ∧ compiles |
| conjunct 2 (policy) | **0%** — no additive predicate exists | `editorial_policy.ml` |
| per-keystroke `rules` @300 KB | **284 ms vs 30 ms budget (9.5×)** | Track R record |
| style rules running by default | 548 of 643 published as shipped | rule registry |

Three structural facts that decide the plan:

1. **The capstone cannot express the failures we see.** `body_token` has four
   constructors; a document is fatal in the model *only* via a dangling build
   edge (T2) or an unadmitted feature (T3). `pdflatex_T1_admissible` discards
   its argument and is proved for every project. `compile_safe_of_source`
   quantifies over **any** byte list with **no tier side-condition**. So
   "fatal-free in the model" is near-vacuous against real LaTeX.
2. **The runtime never reads the tier.** `print_model_connected_verdict` takes
   `~src` and `proj` only; the Coq citation prints unconditionally. An
   LP-Foreign document can print it (measured: one did).
3. **Subset extension does not move accuracy.** `compile_contract.ml:157-183`
   rejects only LP-Foreign; LP-Core and LP-Extended share one verdict path.
   The E-track raises the *honest-label ceiling*, not the answer.

## 2. Why the previous four steps were wrong

| my step | verdict |
|---|---|
| put proven coverage in the banner | **prerequisite, not a step** — moves the metric by zero |
| autopsy the 9 certified false-READYs | **wrong grain** — 9 anecdotes; the structural fact is that the model sees only 2 failure causes |
| aim the perf gate at a budgeted stage | **right, under-scoped** — 3 of 5 stages uninstrumented; no serving surface exists at all |
| start `DetectComplete.v` | **right, mis-ordered** — grounding a classifier the verdict never consults |

Missed entirely: the **policy half of the goal**, the **style-rule defects**,
the **governance fabrications**, **multi-engine soundness**, and the
**adequacy theorem** that is the real content of "provably".

## 3. The plan

### Phase 0 — Stop publishing claims we cannot support (all S; days)

0.1 **Gate the Coq citation on LP-Core.** `print_model_connected_verdict` takes
the tier; outside LP-Core it prints certification without the theorem name.
*Moves:* removes a false claim from every LP-Extended/Foreign run.

0.2 **Surface the certification channel.** Keep the exit-code contract
(`READY`/`NOT-READY`) so all 81 fixtures survive; add
`PROVEN` / `HEURISTIC` beside it. The three states already exist internally.
*Moves:* makes the North-Star metric computable from a normal run.

0.3 **Publish both samples and the proven number.** The generated block carries
42.0% proven, the heuristic remainder, and sample-2 next to sample-1. The word
"North Star" attaches to proven coverage, never to a raw false-READY rate.

0.4 **Delete or measure the fabricated governance numbers.**
`per_rule_soundness_count: 643` is a catalogue headcount; `formal_faithful: 637`
is a generator default; "mutation coverage 95.3%" performs no mutation; the
i18n headline is three hardcoded integers. Each is measured or removed.

0.5 **README honesty pass** — 1,543 theorems / 643 soundness proofs, restated
against what the proofs constrain.

### Phase 1 — Make certification mean something (M)

1.1 **Define the certification predicate** and implement it:
certify **iff** LP-Core ∧ model-applicable ∧ every compile-blocking detector
passes. Everything else is heuristic-READY.

1.2 **Re-measure both samples under it.** This is the new baseline and the
first honest North-Star number.

1.3 **Trie the 9 certified false-READYs against it.** Those that survive are
the real work: they are LP-Core documents the model cannot see. Each becomes
either a model widening (Phase 2) or a detector with a fixture.

### Phase 2 — The verification content (L–XL; this is the heart)

2.1 **Adequacy.** State and prove the missing link: for LP-Core documents, if
the engine would fatal then the model fatals. If a full theorem is out of
reach, widen `body_token` so the observed failure classes are *representable*,
and prove extraction faithfulness per addition. Without this, "provably
compiles" is a statement about an abstraction, not a document.

2.2 **`DetectComplete.v`** — ground the subset boundary. Now meaningful,
because after 0.1 the verdict depends on the tier.

2.3 **Q-ENGINE** — stop aliasing `xelatex_compile_safe := pdflatex_compile_safe`.
Either prove per engine or scope the claim to pdflatex in code and docs.

### Phase 3 — The second half of the goal (M–L)

3.1 **Make `--policy` able to fail.** It returns exit 0 unconditionally; no
submission pipeline can gate on it. This is the cheapest product-relevant fix
in the repo.

3.2 **Make features compose.** The 24-way exact-argv match prevents
`--compile-check` and `--policy` in one run. A publisher needs both.

3.3 **Additive `require`/`forbid` DSL over the project closure**, with the
subtractive half's existing admit-free Coq proof as the template.
⚠ Do **not** implement G2 by merging `editorial_policy.apply` into the compile
path — measured, that would manufacture false-READYs.

### Phase 4 — Real-time (M–L)

4.1 Instrument the three uninstrumented budgeted stages; point the required
gate at a budgeted stage at the budgeted size.
4.2 Add a readiness-path regression gate — this run added ~3 closure walks and
~4 invocations with nothing watching.
4.3 Then the architecture: `rules` at 284 ms against a 30 ms budget.
4.4 Then the serving surface (warm session / LSP). Today users pay cold
process cost, so the per-keystroke promise has no delivery vehicle.

### Phase 5 — The style/writing side (mostly S, best value/effort in the repo)

Ranked by harm × 1/effort, all confirmed at `main`:
1. i18n gated golden suite **silently skipped** (missing dune dep) — one line; 355→366 PASS.
2. **L3-006 registered twice** — every document ships duplicate findings.
3. **CHAR-004** catalogued Reserved but firing, duplicating ENC-008.
4. Relabel the **fake mutation metric**.
5. **Language gating is dead** — 46 rules carry a `languages` list; `run_all` never filters, so locale rules fire on every document. *This is over-rejection.*
6. 49 STYLE rules are Class D and never run by default.
7. 30 TYPO rules (incl. Error-severity TYPO-006) reachable only via an undocumented env var.
8. Proof posture: prove rules against the **shipped** code or stop calling them proofs.

### Cross-cutting discipline

- **Every release grades a virgin sample.** Sample 1 is burned for soundness
  claims: every fix in this run was tuned against it.
- **Published numbers are measured, never constructed** — the C-39 rule, made
  structural: a generator that returns a literal is a bug.
- **A sweep prompt that restates a protocol must quote the implementation.**

## 4. Ordering rationale

Phase 0 first because every later number is uninterpretable until the dial is
honest, and because it removes false claims from shipped output today.
Phase 1 before Phase 2 because it tells us which false-READYs are structural.
Phase 3 is parallelisable and is the only phase that touches the half of the
product with no coverage at all. Phases 4 and 5 are independent and can run
whenever capacity exists; Phase 5 has the best value-to-effort ratio in the repo.

## 5. What this plan explicitly does **not** do

- It does not pursue E-track subset extension for accuracy: measured, it buys
  none. It may still be pursued to raise the honest-label ceiling — *after*
  0.1–0.3 make that ceiling visible.
- It does not add heuristic detectors to reduce over-rejection. That work is
  done (58→2 in-sample) and is no longer the constraint.
