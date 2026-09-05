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

**F1 — The model cannot express a single real failure.** ⚠ **Numbers corrected
2026-09-05 (C-45); the substance survives.** Across both samples, **28**
documents fail pdflatex — not 31. The 31 was right when written and went stale
three commits later: OPEN-053 re-graded with pdflatex's default shell-escape
and the whole **epstopdf class disappeared** (it was a `-no-shell-escape`
artefact — exactly what C-42 predicted), taking 2 documents with it, and a
third row was stranded by the sticky-`ungraded` defect. Regenerated from the
artefacts:

| share | n | class |
|---|---|---|
| 64.3% | 18 | counter/command collision (`\c@`, `\theH`, `\AddToDocumentProperties`) |
| 14.3% | 4 | undefined control sequence |
| 10.7% | 3 | math-mode violation (PAR-IN-MATH) |
| 7.1% | 2 | stray primitive / brace (`\or`, `\caption@ydblarg`) |
| 3.6% | 1 | cleveref override |

`body_token` has four constructors (`PdflatexModel.v:127-131`) and a document
can be model-fatal only via a dangling build edge or an unadmitted feature.

⚠ **"Expressible today: 0 of 31 = 0.0%" was literally false and is restated.**
**3 of the 28 are model-REJECTED** — but all three for **causally unrelated**
reasons, so the claim holds in substance and only in substance:

- `2506.17361v1` — model says closure + feature; real cause `! Undefined
  control sequence \tabu@cleanup` (OPEN-031). Unrelated.
- `2507.07981v1` — model says closure; real cause `! Argument of
  \caption@ydblarg has an extra }`. Unrelated.
- `2507.10358v1` — model says `japanese_cjk not admitted by pdflatex`; the
  document contains **zero CJK characters**. The trigger is ONE stray
  **fullwidth comma U+FF0C** on line 210 of an otherwise-English paper, which
  `has_raw_cjk` matches via the U+FF00–FFEF block. **Verified causally**:
  replacing it with an ASCII comma leaves the failure byte-identical
  (`! Missing $ inserted`, rc 1 on all three passes). Coincidence, not
  detection.

So the honest statement is **0 of 28 causally expressible, with 3 accidental
rejections** — the same "right for the wrong reason" pattern OPEN-006 found in
T2. Every fatal we actually catch, we catch with the *unproven heuristic belt*.

**F2 — The model's fatal channels are narrow, but NOT vacuous.** ⚠ v2 first
claimed `project_closed_b` was structurally unreachable; **that is refuted by
this repo's own committed data** — it fires on `2507.09165v1`
(`results_sample2.json`). What is true: `Build_graph.of_project` adds every
node unconditionally and `graph_of_build_graph` discards the `exists` bit, so
the *dangling-edge* sub-channel is dead, while the acyclicity/topological-order
sub-channel still fires. `declared_features` is always `[]`, so T3 reduces to
four body features behind ~ten substring guards. Certification is therefore
narrow — but "vacuous" was an overstatement, and D2 is rescoped accordingly.

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

### Phase A — Say only what is true (S) ✅ SHIPPED

Re-ordered and re-scoped after review; v1's ordering (A1→A2→A3) was wrong.

- **A0** Commit the metric's PRODUCER. The artefacts were committed without
  one, so changing a verdict string would have frozen the published number
  while every gate stayed green. `gen_proven_coverage.py`, provenance-stamped,
  parsing the frozen token only. **Blocking prerequisite, not an afterthought.**
- **A3 first** — the string. It no longer cites a compile theorem; it names
  what was verified (build-graph closure, engine-feature admissibility) and
  says it is NOT a compilation guarantee. ⚠ It must contain **no bare
  `T<digit>` and no `XXX-999` token**: `diff_real_roots.py` scrapes reasons
  over the whole buffer, so naming the obligations by number would record a
  blocking reason for every READY document.
- **A1′ — tier is a FIELD, not a gate.** The certificate is wrong on a few
  percent of certified papers, and restricting to LP-Core does not reliably
  help — the direction differs between samples (C-43 corrected the stale
  5.0%/5.7% pair and withdrew the general claim built on it; the live figures
  are generated into PROJECT_STATE, not restated). Gating the citation on a
  tier therefore buys no honesty. The tier is printed as
  information, sourced from `Compile_contract.classification_view` — the same
  comment-blanked view the contract classifies, because sourcing it from the
  raw view is precisely C-41.
- **A2 last** — states owned by `Compile_evidence.verdict_state`. Exit codes
  unchanged, so all fixtures survive. ⚠ **Superseded by C1 (2026-09-04): the
  vocabulary is now TWO states, `PREMISE-CERTIFIED` / `PREMISE-REJECTED`.**
  Phase A shipped three because it preserved the existing decider's shape; C1
  established that the middle state (`PREMISE-INAPPLICABLE`, "only the
  duplicate-label obligation is unmet") corresponds to no hypothesis of the
  capstone, and retired it. Verdicts are bit-identical either way. No token contains "proven": while a certified LP-Core document can
  fail pdflatex, such a token would be false on a measurable population.
- **Metric renamed** to *premise-certified coverage* in the generated block.
- ⚠ The published LP-Core numbers moved (84→90, 76→79) **because the tier is
  now taken from the view the contract classifies, not the raw banner** — a
  measurement-source correction, NOT progress.

### Phase B — The constraint leg: zero false-READY

- ~~**B1** epstopdf detector — OPEN-047~~ ❌ **REFUTED before implementation
  (C-42).** The fatal came from the `-no-shell-escape` flag OUR harness passed:
  restricted shell-escape is the pdflatex DEFAULT, `repstopdf` is allowlisted,
  and 19 of the 22 matching frame papers compile in the real world. The
  detector would have shipped at 13.6% precision / 0% causal. Fixed at the
  oracle instead (OPEN-053): **false-READY 9 → 7, correctness 179/200 =
  89.5%**. The constraint leg now has 7 documents, not 9.
- **B2** Triage the remaining 7 against §3's class table: each becomes either
  a detector (heuristic belt) or a model widening (Phase D). **M**
- **B3** Keep the belt honest. C-41 (the tier filter silencing the whole
  compile-blocking belt) is fixed; the class is "a change that silently
  re-parameterises another subsystem". **done**

### Phase C — The coverage leg: grow the numerator

Ranked by measured gain per unit effort.

- **C1** ✅ **SHIPPED 2026-09-04. T4-nodup inapplicability — the cheapest
  coverage gain in the repo.** 17 documents on sample 1 (10 LP-Core) and 16 on
  sample 2 (8 LP-Core) were READY but *uncertified* because the `nodup` premise
  was unmet.

  ⚠ **The justification originally written here was WRONG and must not be
  reused.** It read "duplicate `\label`s, which pdflatex merely warns about and
  OPEN-008 already ruled harmless" — C-43 refuted exactly that: a duplicate
  `\label` IS fatal when the key is read as a number, and the failure never
  converges. Compile-safety was never the right argument.

  The correct argument is **proof-neutrality**: `pdflatex_compile_safe` takes
  `project_well_typed` (T2) and `profile_supported` (T3) and NOTHING else;
  `CompileGuaranteeBridge` discharged the nodup obligation and then discarded
  it (bound as `_Hcoh`). Certification was being withheld on a premise the
  theorem does not consume. Dropping it from the *certification* predicate
  weakens nothing that was ever proved — and the ANTI-TAUT-OK note now at
  `PdflatexModel.v:907` records the same over-quantification one level up.

  Shipped as an additive Coq change (`project_wf_dec_compile`,
  `project_wf_dec_factors` by `reflexivity`, `project_wf_dec_compile_sound`,
  `project_wf_dec_compile_safe_modulo_label_uniqueness`) with the original
  corollary re-derived, so no existing consumer weakened and the extract did
  not change. **Zero verdicts moved** — the retired branch already returned
  READY. **S-M**
- **C2** Residual over-rejection among LP-Core documents (14 on sample 2).
  **M**
- **C3** E-track E1, benign `\def` admission — the ceiling item, reinstated.
  **L**

### Phase D — Make "proven" mean something

Not adequacy (F3). In dependency order:

- **D1** `model_fatal_iff` — a characterisation theorem turning F1/F2 from
  prose into `Qed`, with `vm_compute`d counterexamples keyed to arXiv ids.
  Cheap, and it makes the weakness *provable* rather than asserted. **S**
- **D2** Restore the *dangling-edge* sub-channel (not the whole of T2, which
  already fires — see F2): stop discarding `exists`, put `\includegraphics`
  targets in the build graph. Reuses `edge_token` / `node_known_b` /
  `project_closed`, already proved — zero new capstone obligations, catches 2
  of the 9. **S-M**
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

1. **i18n gated golden suite silently skipped — MECHANICALLY CONFIRMED, VALUE
   REFUTED.** Skipped since 2026-04-07: `latex-parse/src/dune` lists 12 golden
   yamls as deps and `i18n_qa_gated_golden.yaml` is not among them, so
   `test_golden_corpus` prints `[golden] SKIP i18n_qa_gated` and exits 0. The
   one-line dep does take 355 → 366 PASS. ⚠ But **73 of the 79 assertions it
   adds are vacuous** — not one forbidden rule id fires even with gating
   switched off — and it is **not** "the only live assertion of language
   gating". So enable it to stop CI silently skipping a suite, but do not
   count it as gating coverage. **S** 
2. ✅ **SHIPPED 2026-09-05. L3-006 registered twice — MERGED, not deleted.**
   ⚠ Two claims in the original item are corrected. (a) "every document ships
   duplicate findings" is an overstatement: the two registrations are not the
   same check — the L1 copy keys on `\usepackage` + the `\l_pkg_x:N` colon
   form, the L2 copy on `\newcommand` + `\l_name_tl` — so only a document
   carrying **both** shapes got two indistinguishable warnings (measured: 2
   findings before, 1 after). (b) **Neither copy could simply be deleted**, as
   I first assumed. The catalogue entry AND the unit tests in
   `test_validators_expl3.ml` / `test_validators_l5_expl3_tikz.ml` assert the
   PACKAGE-clash semantics including a count of 2 on multiple matches, while
   the golden fixture `corpora/lint/l5_expl3_tikz/l3_006.tex` exercises the
   `\newcommand` one. Deleting the L1 registration built clean and broke 4
   assertions in 2 suites — caught only by running the full suite. Both checks
   are now MERGED under one id, emitting one finding whose count is the number
   of colliding variable occurrences, with a message that finally describes
   what it checks (the old one said "clobbers package macro name" on a rule
   keyed to `\newcommand`). Variable matching widened to `\[lg]_NAME_SUFFIX`,
   which subsumes both forms and so cannot double-count.
   ⚠ Honest sizing: the duplicate was near-unobservable in the wild — the
   L1-only shape has **zero** natural incidence across 2,961 corpus papers and
   `\ExplSyntaxOn` appears in only 2 of 600. The value here is the GATE, not
   the rescued findings.
   ⚠ **Nothing gated rule-id uniqueness, and two source scans missed the
   duplicate**: an id regex of `[A-Z]{2,8}-\d{3}` does not match `L3-006`
   (letter+digit prefix), and a same-file registration scan misses cross-file
   registries like `Validators_l1_expl3`. Now asserted at RUNTIME over
   `Validators.get_rules ()` (exported for this), with a registered kill-test:
   exit 1 with the duplicate, exit 0 without. Also found: 8 sibling L1 rules
   are dead code — see OPEN-057. **S**

3. **CHAR-004 vs ENC-008 — (a) and (b) confirmed, (c) BACKWARDS.** CHAR-004 is
   catalogued `Reserved` (`rules_v3.yaml:70-77`) and does fire in production
   (`validators_l1_expl3.ml:419` → `rules_enc_char_spc` → default `get_rules`).
   ⚠ **But it does NOT duplicate ENC-008, and CHAR-004 is the SOUNDER of the
   two.** ENC-008 omits the UTF-8 continuation-byte check that CHAR-004 has, so
   **4 of its 5 fires across all 2,961 papers are false positives** on legacy
   8-bit encodings, where CHAR-004 correctly abstains. **Deleting "the Reserved
   duplicate" would delete the correct detector.** The real fix is the reverse:
   give ENC-008 the continuation-byte guard (`validators_l0.ml:708-718`, using
   the validated form at `validators_l1_expl3.ml:22-33`). Tracked as OPEN-059.
   **S**
4. **The "mutation" metric — CONFIRMED, and worse than stated.** It is a
   literal quoted-substring grep over `test_*.ml`; it mutates nothing and the
   floor is 0.30. Proved decisively: a scratch tree whose only "test" file is
   an **OCaml comment listing rule ids** scores 100.0% and PASSes. It currently
   publishes *"covered: 522/548 (95.3%)"* under a job titled **Mutation
   Baseline**. ⚠ Two corrections: `mutation` is **not** a required check
   (verified against live branch protection), and the file must **not** be
   renamed — `check_memo_files.py` (in required `spec-drift`) maps the memo
   path to it. Fix is a pure relabel of the docstring and output strings.
   Tracked as OPEN-060. **S**
5. **Language gating is dead — CONFIRMED, and it is the largest user-visible
   defect in Phase G.** Exactly **46** rules carry a non-empty `languages`
   list. `filter_by_language` (`validators.ml:710`) has exactly ONE caller,
   `run_all_for_language`, whose only four callers in the whole repo are
   **tests**. Every production entry point iterates `get_rules ()` unfiltered.
   ⚠ **Measured on 939 real papers: 625 (66.6%) receive at least one finding
   from a rule tagged for a language the document is not in** — 908 findings,
   35.0% of everything those 46 rules emit. Worst single offender: `LANG-003`
   "Mixed French/English punctuation spacing", firing on **552 of 939
   (58.8%)**.
   ⚠ **Do NOT apply the obvious fix.** Routing `run_all` through
   `filter_by_language ... (Language_detect.detect_language src)` flips **25
   golden `expect` entries in 3 suites**, puts 129 `run_all`-routed assertions
   at risk, and costs the required `smoke-cli` producer-coverage gate 21
   rules' triggers. The detector is also too weak to carry it: the locale
   suite's own JA-001/KO-001 fixtures detect as `en`, JA-002's as `zh`.
   Minimal correct fix: gate only on an EXPLICIT `babel`/`polyglossia`
   declaration and leave the byte heuristic non-gating. Tracked as OPEN-061.
   **M**
6. **Class D / env-gated TYPO — both counts right, both qualifiers WRONG.**
   49 STYLE rules are Class D (confirmed, `rule_contracts.yaml`: B 432, A 162,
   D 49, C 17) and 30 TYPO rules are env-gated (confirmed). ⚠ But Class-D rules
   are **not** "never run by default" — they execute in the default **FIX**
   path via `run_all_with_class_d` (measured: `STYLE-015` rewrites `a.  b` →
   `a. b` with no env var and no flag); they are excluded only from the default
   LINT path. ⚠ And the env var is **not undocumented** — it appears in 8
   places including a tracked ROADMAP deferral. ⚠ The 30 gated TYPO rules are
   **not** the 30 the P3 comment says graduated (that promotion is real and
   verified behaviourally) — they are a different 30, gated for a **measured**
   reason: they fire on 98.4% of real papers, and `TYPO-023` (Error-severity,
   which the plan missed alongside TYPO-006) silently corrupts rendered output.
   **Recommendation: do NOT un-gate. Correct the claim.** **S**
7. ✅ **SHIPPED 2026-09-05. `compile_blocking_ids` overstates the belt ~3×.**
   **CONFIRMED exactly by independent measurement**: the list holds 36 ids and
   precisely **24** can never reach `Error`, so the effective T5 belt is **12**
   (`DELIM-001/002/003/004`, `ENC-001/002/005/006/009/012/014`, `PRT-001`).
   ⚠ **"Correct the list or the docs" is a false choice — correcting the LIST
   would re-open C-41.** The same list is what `_filter_by_tier` uses to keep a
   rule alive under LP-Foreign, and zero contracts carry `Any_tier`, so pruning
   the 24 silences them on any document the raw-view classifier calls foreign.
   The docs were the defect: `COMPILATION_GUARANTEE.md` published **"36"** and
   **"37"** in adjacent lines, and still described the set as "a fixed prefix
   filter" though it became an explicit id list in v27.1.63. All three
   corrected, and the dual role is now documented at the definition so nobody
   "cleans it up".
   ⚠ Spun out: **OPEN-058** — the fast kernel executes all 36 in the
   keystroke path when only 12 can affect the verdict. **S**
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
