# LaTeX Perfectionist — Master Roadmap (v3)

> **Status:** authoritative planning document (single source of truth for the compile-guarantee **and** policy-enforcement program). **v3 = the MAXIMALIST synthesis**: it folds in two deep audits (the maximal-vision audit + the maximal real-time-engine audit) on top of the v2 adversarial strategy audit. **v3's thesis: nothing is "out of scope for being hard."** The soundness invariants (G1/G2 below) make maximal-everything PROVABLE and INCREMENTALLY buildable, so the former "reduce scope / accept the residual" posture is reversed into a decidable, incremental, ranked program. Grounded synthesis of the per-track reconstructions plus the maintainer's project memory, corrected against `governance/project_facts.yaml`, `specs/v27/FIX_PRODUCER_LEDGER.md`, `docs/COMPILATION_GUARANTEE.md`, and the live worktree.
>
> **v3 discriminator (keep this so the scope-cut bias cannot reappear):** distinguish a **ZERO-VALUE skip** (skip because there is provably nothing to gain — e.g. re-proving a byte-identical capstone, V4) from a **LAZY scope-cut** (defer a decidable, valuable workstream by mislabelling it "impossible/XL" — e.g. the old V1). Zero-value skips stay skipped; lazy scope-cuts are RECLASSIFIED in-scope. Every "out of scope" claim below must name which of the two it is.
> **Version-of-record:** `dune-project` = **v27.1.60** on the checked-out tree. Tags **`v27.1.58` and `v27.1.59` are tagged on `origin/main`** (both real, pushed). **v27.1.60 = PR #498** (structural-fatal compile-gate, green) on worktree branch `feat/v27160-sound-compile-gate` (`/private/tmp/wt-sound`) — pending user merge/tag.
> **Merge model:** user merges each green PR; I tag. Serialize version bumps (label-conflict/rebase hell otherwise). CI flakes to auto-rerun: rust-proxy, format, xxh-selfcheck, schema (rest-schema ~15min).

---

## 0. Why not just run pdflatex? (the strategic wedge)

Running `pdflatex` gives **ground truth** — but only the answer to "did *this* toolchain, *this* time, produce a PDF." It is **batch**, **after-the-fact**, and **cryptically localized**. A bare yes/no *without* compiling, taken alone, is **weak**: Overleaf, arXiv, and `latexmk` already return that for any document in ~1–3s, and our own 13.7s @ 316KB baseline is *slower* than just compiling. So "we can tell you it compiles without compiling" is **not** the product. It is table stakes.

**The wedge is the *combination* a compiler structurally cannot provide:**

1. **REAL-TIME / incremental.** Sub-second, as-you-type. A compiler is inherently batch — it cannot run per keystroke. Our verified kernel can.
2. **PRECISE, LOCALIZED, EXPLAINED diagnosis + safe fix.** pdflatex says "it failed" cryptically, often at the *wrong* line. We say exactly **what**, **where**, and **why**, and can **suggest or apply a proven-safe fix**. This is arguably the *stronger* wedge — it leverages the whole 660-rule engine + `--explain` + **167** fix-producers + **124** candidates, none of which a compiler has.
3. **MACHINE-CHECKED TRUST.** A READY that is *provably never wrong in the safe direction*, so a high-stakes or automated consumer can **rely on it without re-compiling**. The value here is **trust-for-automation**. No competitor has it: texlab / ChkTeX / lacheck are heuristic; Overleaf just runs the compiler.
4. **POLICY BEYOND COMPILABILITY.** A compiler only checks "does it compile." Our rule engine also checks "does this respect **this editor's template / house style / submission policy**" — provably, at scale, localized, **without a per-submission compile.**

### Consumer segments

- **(A) Interactive AUTHORS** — real-time diagnose + localize + fix, across *all* their documents.
- **(B) EDITORS / PUBLISHERS** — scalable template-, style-, and compile-conformance enforcement **without per-submission compiles**, with trust + precise localization. **This is the flagship monetizable application** — e.g. an editor uploads a required template and every submission is provably checked against it.
- **(C) automated PIPELINES / other tools** — a *verified substrate* to build on.

### Honest limits (do not over-index on "prove everything")

The **proof** covers only **LP-Core** — a subset that most real papers do not *fully* live in (measured: **38.9% LP-Core** roots). So the proof is the **trust backbone for segments B and C**, but for segment **A** the daily value is **SPEED + LOCALIZATION + FIX + COVERAGE across ALL documents** (a clearly-labelled proven tier *and* a clearly-labelled heuristic tier).

**⚠ v3 CORRECTION (do not re-read this as "don't bother proving").** The honest limit is only that *today's proven tier is 38.9%* — it is **NOT** that the frontier is fixed. Under G1 the semantic tier is decidable and incrementally buildable, so the proven numerator is a **lever to be pushed to the empirical knee**, not a ceiling to accept. What *would* be strategically wrong is trading away speed/localization/fix/coverage-across-all-docs **for** proving — the two are complementary, not a zero-sum. The scope discriminator: **maximise the proven frontier as far as the observatory shows marginal coverage** (never a preset N), keep the heuristic tier for the rest, and skip only the ZERO-VALUE proofs (V4).

**Positioning:** *ONE verified document-understanding engine* — compile-prediction **+** policy-enforcement **+** localization **+** fix **+** trust — **not** "compile-guarantee vs. a legacy linter." The linter is not a legacy side-show being retired; user-defined, provably-checked rules are **core to segment B** (see Track P).

---

## 1. North Star & Principles

### The core promise
> **A LaTeX document COMPILES if and only if our verified parser says it will (READY) — as long as it stays within the non-Turing-complete decidable subset (LP-Core, expandable) — AND it can be provably checked against a user-defined policy without compiling.**

Delivered (1) with **verdict SOUNDNESS**, (2) in **REAL-TIME** as-you-type, (3) over the **WIDEST decidable subset** we can prove, (4) with a **clearly-labelled HEURISTIC tier** for the rest, and (5) as a **policy substrate** editors can rely on — all on a **FORMALLY-VERIFIED (Coq)** backbone.

### North-Star METRIC (the one number that means success)

> **Proven-verdict coverage at ZERO false-READY on a committed corpus** =
> (real papers that get a *proven* verdict matching pdflatex, with **zero false-READY**) / (all real papers).

Current banner (65-doc committed differential corpus, pdfTeX / TeX Live 2026): **35/65 = 53.8% proven-correct READY, at 8 false-READY (all in the documented allowlist).** **Target:** grow the numerator (E-track subset extension + V1 modelling) while driving false-READY **allowlist → 0**, on a *hash-manifested, version-controlled* corpus (S0/S4), and (for the flagship) parameterize the promise by **engine + TeX-Live year**.

Every near-term move below states its **delta on THIS metric**. Producer counts, theorem counts, and proof-file counts are **infrastructure health, not the success metric** — do not confuse activity for coverage.

### Principles (non-negotiable)

**The two v3 KEYSTONES** — the soundness invariants that make *maximal-everything* provable (why we can chase full coverage AND full policy AND stay sound):

- **G1 — Catalogue one-directional authoritativeness.** Undefined-cs / undefined-env / missing-package are **DECIDABLE** against a base+package **`ProvidesCatalogue`** (a Coq finite map: cs/env → `{kernel|package|class}`, with mode `{text|math|both}` + arity). Emit proven-NOT-READY for an unresolved control sequence **ONLY** when it resolves to nothing in the catalogue **AND** the document declares no out-of-catalogue package **AND** no user `\def`/`\newcommand` that could define it. Under that **side-condition, an INCOMPLETE catalogue can only SHRINK the proven-NOT-READY set — it can NEVER manufacture a false-READY.** **Over-listing is the ONLY hazard** (a claimed cs that is not actually provided ⇒ a spurious READY): an auditable curation *soundness-duty*, enforced exactly like `extension_contract`'s `over_claims=false` clamp + a differential test. ⇒ **the semantic tier is decidable, sound, and INCREMENTALLY buildable.** This is the invariant that turns the old "8 residual false-READYs are impossible" into "8 measure UNBUILT CATALOGUE."

- **G2 — Policy firewall.** Publisher/venue/house-style rules live in a channel **DISJOINT** from the compile-READY verdict. A venue rule only ever **ADDS a conservative NOT-READY** ("violates house style"); it can **NEVER manufacture a READY** ⇒ it structurally **cannot introduce the cardinal false-READY**, and it sidesteps the abandoned "promote advisory lint to a compile gate" trap (Principle 3). Policy is additive-toward-rejection by construction, so the entire policy plane (Track P) is sound *for free* w.r.t. the compile guarantee.

The pre-existing principles (each still non-negotiable):

1. **SOUNDNESS IS PARAMOUNT.** The cardinal bug is a **false-READY**: we certify "provably compiles", pdflatex fails (e.g. `$a^b^c$`). It breaks the guarantee. A **false-NOT-READY** (over-rejection) is merely conservative and acceptable. Every design choice resolves ties toward NOT-READY. **Monitored exception:** the double-script detector's fixed 4096-frame array "bails safely" on extreme nesting; a bail is conservative toward false-READY (the dangerous direction) — so it is a monitored risk that **must demote to NOT-READY on bail** (hardening DONE this PR, see §5), not a free pass.

2. **ANY-UNMODELLED-CS ⇒ NOT-READY-NEVER-READY-BY-ABSENCE.** If the engine encounters a control sequence, environment, package, or feature it does not model, the *only* sound verdict is NOT-READY (or the heuristic LIKELY tier). READY may never be reached by silent absence of a check. This is the load-bearing invariant behind every extension (see V-CAT).

3. **Precise dedicated compile-gate detectors OVER advisory-lint-rule promotion.** Promoting the ~641 lint rules to compile gates was **TRIED and ABANDONED** — they over-reject real compiling papers (MATH-047: 34/44; MATH-077/PKG-004 comment/verbatim-blind; CMD-016 ignores `\renewcommand` order). *Advisory linting ≠ compile-gate precision.* Any subset-widening must be a **dedicated precise detector, differentially fuzzed vs real pdflatex** (`compile_blocking_promotion_finding.md`). (This is about **compile** gates only — it does **not** demote the rule engine, which is first-class for policy; see Track P.)

4. **Differential-fuzz-vs-real-pdflatex is the STANDING gate, not a one-off.** Confidence comes from running BOTH `--compile-check` and real `pdflatex`, building a confusion matrix, and failing **only on a NEW false-READY** outside the documented `KNOWN_FALSE_READY` allowlist (`scripts/tools/diff_compile_check.sh`). **Every deterministic-structural item (S3, S5, future detectors, the whole E-track) must pass this gate before shipping.** It needs **local pdflatex** — CI has no TeX — so it is a **local / pre-release gate** (S0 wires it into the release gate as a hard-fail on new false-READY where pdflatex is present).

5. **Honest-scope docs.** READY = "no runtime precondition we check is violated + the extracted project passes the proven premise-check", **NOT** "your exact bytes are certified to compile" (`docs/COMPILATION_GUARANTEE.md`). `--compile-check` is an honest **fail-first readiness pre-check**, not a total compile certificate. LaTeX is Turing-complete ⇒ a total compile-decision is **provably impossible**; we only claim decidability over LP-Core, for a **defined READY oracle** (S-ORACLE) under a **pinned engine + TeX-Live year**.

6. **The LP-Core / LP-Extended / LP-Foreign boundary** is the citable scope of the guarantee. It is a **total, deterministic, Coq-proven** classifier (`classify_lp_core_sound`, Qed, 0 admits). "Latex-epsilon" = LP-Core.

7. **The over-rejection real-paper safety scan (found-and-fixed, not a clean sheet).** Any new gate must show **0 over-rejection** on the user's real-paper corpus (**6,396–6,899 compiling root papers**, free ground truth). Honest history: the v27.1.60 double-script detector's precision scan (1,218 real published papers) initially produced **4 false-NOT-READY regressions on genuinely-compiling papers** — all confirmed compiling by pdflatex, all **FIXED** (commit `b3bf23f1`: compute `find_math_ranges` on a comment/verbatim/url-BLANKED copy so a commented unbalanced `$$`/`$` can't spill a fake math range; plus a `\ref`-alias moving-arg skip). **Final state: 0 over-rejection on the scanned corpus** — earned, not assumed. (The structural `&` gate was separately dropped precisely because it over-rejected **107 real roots**.)

8. **fast == full parity.** The fast readiness kernel must be **verdict-identical** to the full path (`test_fast_readiness_parity.ml`, wired into `runtest`, 473 corpus + 150 real papers → 0 divergences). The v27.1.60 structural gate is a **pure function of source** ⇒ fast==full trivially.

9. **STANDING PERFORMANCE BUDGET.** Every detector-adding item (Track S / E) and every serving change (Track R) states and defends a latency budget on the R-baseline size bands; a detector that regresses the budget is not shippable without an explicit ADR (see the acceptance clauses in R and each S/E item).

### Hard-won safety guardrails (each cost a real bug — do not relearn)

- **Control-word-glue corruption.** A fix emitting a *bare* control word (`·`→`\cdot`, `->`→`\rightarrow`, …) yields `$a\cdotb$` — an undefined control word / compile error — when the next byte is a letter. It passed *every* idempotence / UTF-8 / convergence gate; only *output inspection* caught it. Mitigated by `Validators_common.control_word_repl` + the permanent multi-variant `scripts/tools/check_producer_coverage.py` gate.
- **The 46% producer-coverage gap.** **69 of 150 producers (~46%) were NEVER corpus-triggered** — so "differential 0-diff + convergence" is *not* full-surface safety. `check_producer_coverage.py` now applies EVERY `produces_fix:true` rule to a registered adversarial trigger (`specs/v27/producer_triggers.json`), asserting applied + valid-UTF-8 + idempotent + golden-match. **This gap is a V-TRUSTED-BASE target, not a footnote.**
- **Offset-on-length-changing-transform corruption (STYLE-033).** Match the **ORIGINAL** source; never emit edits at offsets computed on a length-changing transform. Prose-changing rules are **candidates, never auto-fixes** (SPC-018). **This is why fixing compile issues is mostly review-gated candidates, not silent auto-fix** (see Track P).
- **Coq nat-pow Qed-blowup.** A Peano-`nat` `2^k` constant forces the kernel to reduce `2^30` to a ~10⁹-unary numeral at `Qed` → multi-minute hang (bit v27.1.58). Fixed by an **abstract opaque `fold_left_cons_eq` rewrite** (`coq_nat_pow_qed_blowup.md`). *This class of bug lives in the trusted glue, not the proof — see V-TRUSTED-BASE.*
- **Squash-merge drops late commits / stacked-PR trap.** A squash of a base PR strands later commits (v27.1.5 = 11 producers stranded, recovered via cherry-pick). Serialize; keep a recovery plan (`feedback_squash_merge_drops_late_commits.md`).

### Operational notes
- **External-worktree discipline:** file-editing agents MUST use `isolation:'worktree'` branched from **main**. Verify agents must inspect the **build's** worktree (`path_match`), not the main tree.
- **Dropbox CloudStorage FS is pathologically slow** for git — use partial commits `git commit -- <pathspec>`; clear stale `.git/index.lock`.

---

## 2. Where We Are

### Shipped milestones (compile-readiness flagship)

| Version | Delivered | Grounding |
|---|---|---|
| **v27.1.53** (#490) | `--compile-check` READY/NOT-READY verdict; T0/T5 de-stubbed | `validators_cli.ml`, `dab9673e` |
| **v27.1.54–56** | Premise-decision bridge **extracted + executed**: `project_wf_dec` decides T2/T3/T4; `project_wf_dec_compile_safe` (Qed, Closed); hand mirror removed → MODEL-CONNECTED | `proofs/CompileGuaranteeBridge.v` |
| **v27.1.57** (#495) | **LP-Core subset boundary certified** — tier DECISION is Coq-extracted `LanguageContract.classify` governed by `classify_lp_core_sound` (Qed); only `Unsupported_feature.detect` stays trusted (adversarially certified) | HEAD `36b1dc3c` |
| **v27.1.58** (#496) | **Verified bytes→body_token front-end** — Coq-modelled, Qed-proved, 0-admit/0-axiom scanners, extracted + executed at runtime; capstone `compile_safe_of_source` (Print Assumptions Closed). (Bit the Coq nat-pow Qed-blowup; fixed via abstract fold rewrite.) | `proofs/BodyTokenFrontEnd.v` |
| **v27.1.59** (#497, **tagged on origin/main**) | **Fast compile-readiness kernel** — `check_ready_to_compile ~fast`: parses **once**, runs only the compile-blocking rules (`DELIM-`/`ENC-`/`PRT-`); verdict-identical to full path on 623 docs; parity gate wired | `compile_contract.ml`, tag `v27.1.59` |
| **v27.1.60** (**PR #498, green, IN FLIGHT**, `f0f8cbcd`) | **Precise structural-fatal compile-gate** (`compile_gate_checks.ml`, **632 lines**): comment/verbatim/context-aware detectors firing **iff pdflatex genuinely fails** — (1) double super/subscript in math, (2) no `\documentclass`, (3) `\usepackage` after `\begin{document}`. Pure function of source ⇒ byte-identical fast/full. **Misplaced-`&` DELIBERATELY DROPPED** (over-rejected 107 real roots). Precision regressions found-and-fixed (`b3bf23f1`). **Plus 3 hardening items** (bail⇒demote, `is_compile_blocking` single-source, roadmap fact-checker — see §5). | `feat/v27160-sound-compile-gate` |

### Formal backbone state (Coq)
- **178 proof files total** = **63 core + 114 generated + 1 ML** (plus **7 archived** `.disabled` files, tracked separately) (`governance/project_facts.yaml`). **NO `Admitted`, NO `Axiom`** in active proofs (only archived `.disabled` files carry them).
- **Capstone** `PdflatexModel.pdflatex_compile_safe` — **Qed, unconditional, Print Assumptions Closed**; `xelatex`/`lualatex` aliases are **the same proof object** (⚠ this is exactly the multi-engine soundness gap — see S-ENGINE).
- Front-end gap #1 **CLOSED** (v27.1.58); premise bridge **extracted+executed** (v27.1.54-56); LP-Core boundary **certified** (v27.1.57).
- **Faithful pdflatex semantics** (Tier-3, v27.1.29-32): `LexerFaithfulStep.v` + `FaithfulWS8Bridge.v` — tokenize/aux/log/pass, ≤2-pass convergence; all Qed, Closed. **⚠ shipped ADDITIVELY** (bridge, capstone byte-identical) — NOT the plan's re-proof (see V4, now ADR-accepted by default).
- **ML span-extractor asset:** `proofs/ML/SpanExtractorSound.v` proves `v2_span_extractor_sound` (Qed) over the trained v2 byte-classifier `ml/checkpoints_v2/best_model.pt` (**F1=0.9799, precision 0.975, recall 0.9849**), covering 8 ambiguous TYPO rules — prior art / substrate for Track H **and the H1 span extractor already exists**.
- **T5 catalogue scaffold:** parametric `rule_passes` + **114 generated per-family proof files**.
- `theorem_count_reported: 1543`; `per_rule_soundness_count: 643`.

### Coverage numbers
- **Rule catalogue:** 660 total / 17 reserved / **643 non-reserved / 643 shipped** (`governance/project_facts.yaml`, internally consistent).
- **Fix producers (Bucket A):** **167 (~25%) — SETTLED, authoritative** (`FIX_PRODUCER_LEDGER.md`, `SHIPPED_VERSIONS`). Decomposition: 70 (L1+ via `mk_result_with_fix`) + 47 (L0 via `with_fix`/`fix_of`) + the remainder across families. **Bucket A = 466 rules; 167 shipped / 299 pending.** **⚠ Do NOT "correct" 167 down to 70** — the 70-count is only the `_with_fix_exempt`-grep subset (verbatim-hardened L1+), not the producer total (see C-DR1). **Cadence commitment:** ≥10 new Bucket-A producers per patch release (`FIX_PRODUCER_LEDGER.md:781`) — actual recent cadence ~1/patch (audit-depth over throughput).
- **Review-only candidates (Bucket C):** **124** distinct rule-ids (`mk_result_with_candidates`, matches backlog header).
- **Diagnose-only:** 402 (family-partitioned; "rest non-candidate-able" is a per-family assertion, not individually re-audited).
- **LP-Core split (real papers, roots):** **38.9% LP-Core / 60.2% LP-Extended / 0.9% LP-Foreign** (16,193 `.tex`, 6,899 roots). **97.4% of ~96k real `\def` are BENIGN** — the E1 opportunity. **The ~60% LP-Extended majority is the addressable market for H1** (heuristic, non-proven, actionable NOW). **⚠ PROVENANCE CAVEAT:** these three percentages rest on an UNTRACKED/absent `bench_classify` driver — **commit the classify driver FIRST (Observatory OBS0) before quoting the 38.9/60.2/0.9 split as a versioned commitment** (R-corpus / R-corpus-representativeness). Until committed, treat them as measured-but-unpinned.

### Honest current scope of the guarantee
`--compile-check` runs **T0 (parse + LP-Foreign classify) + T2 (source closure) + T3 (feature/engine compat) + T4 (aux label uniqueness) + T5 (37 DELIM/ENC/PRT Error rules) + the v27.1.60 structural-fatal gate**, with **T1 (macro expansion) a deliberate conservative no-op**. Scoped to **LP-Core**, **pdflatex only** (see S-ENGINE), for the READY oracle defined in S-ORACLE.

Measured soundness residual on the **65-doc differential confusion matrix** (v27.1.60, `diff_compile_check.sh` at scale, pdfTeX / TeX Live 2026):
- **35 true-READY / 20 true-NOT-READY / 8 false-READY / 2 false-NOT-READY** (total 65).
- The v27.1.60 structural-fatal gate closed the prior **10 → 8** false-READY residual — `fail_double_subscript` and `fail_no_documentclass` are now correctly NOT-READY (and `fail_missing_begin_document` is caught by T0, so it is not a false-READY either — a stale allowlist entry to prune).

All **8** residual false-READYs need macro/package-universe modelling or full expansion (0 new beyond the documented `KNOWN_FALSE_READY` allowlist, whose 8 real entries ARE this count), and the gate holds **0 over-rejection on the scanned real-root corpus**. See `docs/COMPILATION_GUARANTEE.md` for the enumerated residual.

---

## 3. Tracks

Tracks: **S** (verdict soundness — incl. **S6/S7** zero-catalogue residual-shrinkers), **S0/S-ENGINE/S-ORACLE/SEC/H-BACKSTOP** (verification infrastructure & scope), **OBS** (Coverage Observatory — measure, don't assume), **V / V-CAT / V-TRUSTED-BASE / V-PRIORITY** (formal verification, incl. **V1-Catalogue** flagship + **VP1 `DetectComplete.v`** #1 priority), **R** (**v3 maximal real-time engine** — SLO + sound-incremental + budget + two-channel), **E** (subset extension), **H** (heuristic tier), **P** (policy / rule engine, incl. the **`.lprules` DSL P4**), **C** (the shared rule-execution substrate). Effort scale S/M/L/XL. **Every S/E detector-adding item and every R item carries the standing performance-budget clause (Principle 9); every check declares a `latency_class` (R-CHANNEL).**

### Track S — Verdict Soundness

**Rationale.** Directly serves the cardinal promise: eliminate every false-READY, over the widest possible sound subset, without introducing over-rejection.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **S0** | **Verification infrastructure (NEAR-TERM BLOCKER)** | NOT STARTED | M | local pdflatex | **Commit `bench_classify` + `ampfuzz` + a hash-manifested, redistributable over-rejection corpus** (kill the untracked-scratch dependency, R-corpus). **Wire `diff_compile_check.sh` into the release gate** — hard-fail on any NEW false-READY where pdflatex is present. **Pin + assert `pdflatex --version`** (engine + TeX-Live year). **Emit the confusion matrix as committed machine-readable JSON.** This blocks credible S2/S4/E-track numbers. Budget clause: harness run bounded + sandboxed (SEC). |
| **S1** | Ship v27.1.60 structural gate to main | IN FLIGHT (`f0f8cbcd`, PR #498 green) | S | green CI + user merge; local `diff_compile_check.sh` | PR merged, tag v27.1.60 pushed; `diff_compile_check.sh` = 8 known / 0 new false-READY; `test_compile_gate.ml` passes; fast==full parity green. **Δ North-Star: closes the `$a^b^c$`-class holes (10→8 false-READY), 0 over-rejection.** |
| **S2** | **GENERATIVE grammar-directed coverage — the STANDING gate (BLOCKING infra)** | PARTIAL (mechanism exists; generator not automated) | L | S0; local pdflatex; `diff_compile_check.sh` | **Enumerate EVERY detector decision-branch × EVERY LP-Core construct class**, including the missing deterministic-FATAL classes: **`\left..\right]` mismatch, extra alignment tab, "Dimension too large", `\verb`-newline, `\end{document}` in an open group**. Generator emits structurally-perturbed LaTeX; report every `cc=READY ∧ pdflatex=FAILS`; each new class fixed OR moved to `KNOWN_FALSE_READY` with written justification; 0 NEW false-READY over ≥N-thousand fuzzed docs. **This is BLOCKING infra that every deterministic-structural item (S3/S5/E-track/every future detector) must pass — it is the standing gate, NOT a leaf.** Local/pre-release (CI has no TeX). |
| **S3** | Misplaced-`&` gate via strict LP-Core scoping | DROPPED, but shippable EARLIER/INDEPENDENTLY of E1 via direction (b) | M | LP-Core classifier; alignment-env stack model; **decoupled from E1 if (b)**; must pass S2 | fires on genuine misplaced `&` in strict LP-Core docs; **0 over-rejection** on the 6,396-paper corpus; differential fixture passing S2. Carving alignment-shortcut `\def` macros into LP-Extended (direction (b)) makes `&` soundly gate-able for strict LP-Core *without* over-rejecting `\def`-alignment papers → S3 is **not** permanently blocked on E1. |
| **S4** | Deepen differential validation vs real pdflatex at scale | PARTIAL (65-doc matrix + 6,396 over-reject pass) | M | **S0 (corpus + JSON matrix)**; local pdflatex | harness over full real-paper tree; confusion matrix published as committed JSON in `COMPILATION_GUARANTEE.md`; 0 NEW false-READY; over-rejection reported per LP-tier and **per engine + TeX-Live year**. **Δ North-Star: turns 35/65 into a reproducible versioned commitment.** |
| **S5** | Finish T0–T5 as TOTAL checks over the real parse | PARTIAL (T1 no-op; T4 aux-gated) | L | catalogue for mode/macro state; `User_macro_registry`; must pass S2 | T1 catches math-only-in-text + illegal `\newcommand` param-count on the 2 residual fixtures without over-rejecting; T4 does source-only duplicate-label detection; documented totality. **NB: the two concrete residual-shrinkers below (S6/S7) are pulled out of S5 as standalone, ZERO-catalogue wins — do them NOW, do NOT defer to a heuristic tier.** |
| **S6** | **Prove `illegal_param_number_sound` — drop residual 8→7 NOW** | NOT STARTED (**ZERO deps**) | S | `User_macro_registry` (already extracts arity + walks `#1..#9`) | `#n` with `n` > declared arity ⇒ pdflatex "Illegal parameter number in definition of …". The registry already extracts a macro's declared arity and scans its body's `#`-params, so this is a pure source-decidable check with **no catalogue and no expansion**. Prove `illegal_param_number_sound` (Qed); wire as a structural-fatal detector; passes S2. **Closes `fail_newcommand_wrong_args` → residual 8→7. Δ North-Star: +1 proven-NOT-READY, 0 over-rejection.** |
| **S7** | **Prove `math_mode_leak_sound` — drop residual 7→6 NOW** | NOT STARTED (needs only the catalogue mode-bit) | S | V1-Catalogue mode-bit `{text|math|both}` for a *small* seed set of math-only cs (`\alpha`, `\beta`, …) | a catalogued math-only control sequence used outside any math range ⇒ pdflatex "! Missing $ inserted". Needs ONLY the mode-bit column of `ProvidesCatalogue` for a tiny math-only seed set (not the full catalogue), composed with `find_math_ranges`. Prove `math_mode_leak_sound` (Qed); passes S2. **Closes `fail_math_in_text` → residual 7→6. Δ North-Star: +1 proven-NOT-READY, 0 over-rejection.** **This proves the mode-bit half of `ProvidesCatalogue` is load-bearing and seeds V1-Catalogue.** |

### Track S-ORACLE — Define what READY *means*

**Rationale.** Soundness is only meaningful against a *defined* oracle. The audit found the roadmap had **0 mentions of bibtex/biber/bbl** and no crisp READY definition.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **SO1** | Precise READY oracle + documented false-READY classes | NOT STARTED | S–M | S0 | Define READY = **clean single-pass `pdflatex` with no LaTeX Error** (pinned engine + TeX-Live year). Document the false-READY CLASSES the single-pass oracle admits: **(i) multi-pass / aux / bbl staleness** (`\ref`/`\cite` resolved only on a 2nd pass), **(ii) recoverable-but-wrong** (`\ref` renders `??`, duplicate `\label`, overfull `\hbox`). Add a **bib / biber-dependency probe** (a doc that needs `\bibliography`+bibtex/biber and a fresh `.bbl` is only READY relative to that having run). These classes feed S2 and the H-BACKSTOP. |

### Track S-ENGINE — Multi-engine scope (invisible false-READY risk)

**Rationale.** `xe_compile_safe` / `lua_compile_safe` are **literal `:=` aliases** of `pdflatex_compile_safe` (same proof object), but `feature_compatible` **IS** engine-sensitive and `of_root` **defaults to `Pdflatex`** with a **pdflatex-only** differential. A **lualatex user can therefore get an invisible false-READY**.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **SE1** | Resolve multi-engine scope | OPEN decision (Q-ENGINE) | L (option A) / S (option B) | S0 | **Option A:** add real per-engine capstones + per-engine differential rows + thread `engine` through `of_root`, and make the North-Star promise **engine + TeX-Live-year parameterized**. **Option B (ADR):** scope the guarantee to **pdflatex-only**, **DELETE the alias-as-guarantee claim** for xe/lua, and gate/emit NOT-READY-or-heuristic for non-pdflatex engines. Either way the "aliases are the same proof" line stops being a silent guarantee. |
| **QE1** | Engine-detection probe for `of_root` | NOT STARTED | S | SE1 | detect engine from `%!TEX program`, `\RequirePackage`/fontspec, magic comments; feed the correct capstone or demote. |

### Track SEC — Security of the compile substrate

**Rationale.** The differential harness and any pdflatex backstop execute untrusted LaTeX; the range-oracle and build-graph parse untrusted bytes.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **SEC1** | Harden the compile substrate | NOT STARTED | M | S0 | **`-no-shell-escape` everywhere**; **sandbox + timeout** the differential harness and any pdflatex backstop; **bound `\input`/`\include` to the project root** (no `../` escape, no absolute paths); **fuzz the range-oracle and build-graph construction** on adversarial bytes. No RCE/path-escape reachable from a checked document. |

### Track H-BACKSTOP — Optional real-pdflatex confirmation

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **HB1** | `--compile-check --confirm-with-pdflatex` | NOT STARTED (Q-BACKSTOP) | M | SEC1; SO1 | optional flag runs real pdflatex; on **disagreement downgrades READY→LIKELY** and **feeds the disagreeing doc into S2**. Sandboxed/timed (SEC1). Value: a self-improving oracle + a trust escape-hatch for segment C. |

### Track OBS — Coverage Observatory (first-class, committed — "measure, don't assume")

**Rationale.** Every "reduce scope" decision in v2 rested on UNTRACKED scratch measurements (the absent `bench_classify`, a 15+-day-old scratch analysis). The Observatory makes the North-Star metric — **proven-verdict coverage at 0-false-READY** — a **measured, committed, reproducible function of {packages catalogued, macros admitted, detectors enabled}**, so the catalogue KNEE and the coverage frontier are *plotted*, not guessed. Lives in **`latex-parse/observatory/` — committed first-class, NOT scratch.**

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **OBS0** | Resurrect the classify driver, committed | NOT STARTED | S–M | none (unblocks the 38.9/60.2/0.9 quote) | commit **`observatory/classify_driver.ml`** (kills the untracked-scratch dependency); the LP-Core split becomes a versioned artefact. **Do this BEFORE quoting 38.9/60.2/0.9 as a commitment.** |
| **OBS1** | `report_vNN.json` — the coverage-frontier artefact | NOT STARTED | M | OBS0; S0 | emit **proven-verdict coverage at 0-false-READY as a function of {packages catalogued, macros admitted, detectors enabled}**; a **per-demotion-driver histogram** (why each doc is demoted); a **marginal-coverage curve** (the derivative that answers the catalogue-knee). Committed machine-readable. **This operationalizes G1's "rank by marginal coverage, build to the knee."** |
| **OBS2** | `corpus_manifest_vNN.json` — content-hash-pinned ground truth | NOT STARTED | M | OBS0; SEC1 (sandboxed pdflatex) | per-paper **sha256 + pdflatex ground-truth verdict + LP-tier**, **content-hash-pinned** to sidestep the corpus copyright problem. A **representative regression corpus sampled to the measured 38.9/60.2/0.9 distribution**, REPLACING the too-clean 470/473 lint corpus (R-corpus-representativeness). |
| **OBS3** | S2 becomes a REAL differential-fuzz generator INSIDE the observatory | PARTIAL (mechanism exists, not a generator) | L | OBS2; S2 | **structural perturbations of real roots**; the **false-READY discovery-rate per N-thousand fuzzed docs must monotonically → 0**. **Mandatory pre-release gate.** (S2 in Track S is the *contract*; OBS3 is its generator implementation.) |

### Track V — Formal Verification

**Rationale.** The Coq backbone is what makes READY a *proof*. Close the remaining trusted-layer and re-proof gaps — **but** the audit's key finding is that the real bugs live in the UNPROVEN trusted glue (V-TRUSTED-BASE), which is elevated **above** the abstract re-proof (V4). **v3: V1 is RECLASSIFIED from "out of scope" to the semantic-tier FLAGSHIP** (decidable/incremental under G1); the #1 verification priority is **VP1 `DetectComplete.v`** (Track V-PRIORITY).

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **V1** | **V1-Catalogue — the semantic-tier FLAGSHIP (`ProvidesCatalogue`)** | **RECLASSIFIED IN-SCOPE, decidable, incremental, HIGH** (was "OUT OF SCOPE / accept-the-8-residual") | L incremental (was mislabelled XL) | verified base+package macro/env catalogue (`ProvidesCatalogue` finite map); kpathsea/file-resolution model; **MERGES E5 into this ONE catalogue** | **⚠ LAZINESS REVERSAL.** The old "out of scope, accept the 8 residual" was a LAZY scope-cut — under **G1** the tier is DECIDABLE and INCREMENTALLY buildable, so the residual measures **UNBUILT CATALOGUE, not impossibility**. The "provably cannot catch" wording is STRUCK (here + in `COMPILATION_GUARANTEE.md`) and replaced with "not-yet-modelled (decidable given catalogue C under the G1 side-condition)". Build the catalogue INCREMENTALLY, **ranked by MARGINAL proven-coverage** (NOT raw `\usepackage` frequency — a ubiquitous package whose macros never cause a false-READY yields ZERO marginal coverage), to the **empirical KNEE decided by the Observatory** (not a preset N). Acceptance per increment: modelled entries turn undefined-cs/env + missing-package into correct NOT-READY under the G1 side-condition; **still 0 over-rejection**; `over_claims=false` per entry (over-listing is the only hazard — an audited curation duty); residual allowlist strictly shrinks; catalogue proof extended. **Governed by V-CAT contracts. V1 ≡ E5 ≡ H1's undefined-cs dictionary — ONE `ProvidesCatalogue` serving all three tiers.** |
| **V2** | Prove all ~660 rules to Coq soundness | PARTIAL (parametric scaffold + 114 generated family files) | XL | `T5_concrete.v` instantiation; generator completeness | `Generated.Catalogue` covers all 660 ids with per-rule Qed soundness; `pdflatex_T5_safe_holds` instantiated; Print Assumptions Closed. |
| **V3** | Byte-level certification of `detect` / `Parser_l2` / range-oracle for LP-Core | PARTIAL (`detect` cert-by-test; `Parser_l2` unverified; range oracle trusted) | XL | LP-Core grammar spec | `Parser_l2` proven sound/complete for LP-Core; `detect` completeness proven OR differential battery formalized; range oracle proven OR trust boundary explicitly bounded. **Overlaps V-TRUSTED-BASE.** |
| **V4** | Tier-3 Stage-6 re-proof | **ZERO-VALUE-SKIP (byte-identical capstone) — but ATTEMPT the isolated re-proof to SURFACE divergence, don't ADR-paper it blindly** | L (RISKY) | maintainer sign-off | **This is a ZERO-VALUE skip, NOT a lazy scope-cut** (the bridge is byte-identical / zero verdict change; re-proving a proven capstone yields no coverage). **v3 change of resolution:** rather than ADR-paper the bridge blindly, **ATTEMPT the isolated re-proof (in a throwaway branch) specifically to SURFACE any hidden abstract-vs-faithful divergence** — the re-proof's *value* is not a new theorem but a *divergence check*. If it goes through clean (or S2/HB1 surfaces no divergence), keep the additive bridge and rewrite acceptance #6. If it exposes a divergence, that divergence is the real finding. Still DE-PRIORITIZED below all coverage/utility work. |

### Track V-CAT — Catalogue-soundness contracts (split out of the old D1)

**Rationale.** Extension (E-track) and V1 both admit new constructs into READY; each admission is a soundness *contract* that, if violated, re-opens the cardinal bug. Name the contracts so they are enforced, not assumed.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **VC1** | Named admission contracts | NOT STARTED | M | E-track / V1 | Enforce, as named acceptance clauses on every admission: **(1) MATH-OPEN CONTRACT** — *any* math-mode-opening admission MUST re-derive `find_math_ranges`' entry set, or the double-script detector goes **unsound (cardinal bug)*.* **(2) ABSENCE CONTRACT** — *any* unmodelled control sequence ⇒ **NOT-READY-never-READY-by-absence** (Principle 2). **(3) CATALOGUE VERSION/OPTION/STALENESS CONTRACT** — a package/base-macro catalogue entry is authoritative only for a pinned package version + option set + TeX-Live year; a stale/mismatched catalogue must demote, not silently admit. |

### Track V-TRUSTED-BASE — Certify the unproven glue (ELEVATED above V4)

**Rationale (audit headline).** The real bugs have all been in the **UNPROVEN trusted glue**, not the abstract model: the nat-pow Qed-blowup, the duplicate `is_compile_blocking`, STYLE-033, the 46%-never-triggered producer gap. A re-proof of an already-proven capstone (V4) is lower value than certifying the glue that actually breaks.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **VT1** | Trusted-glue ledger | NOT STARTED | S–M | none | enumerate every trusted (non-verified) component on the READY path: byte-list conversion, build-graph construction, protected-range oracle, runtime↔extracted-type conversion, file I/O, OCaml+Coq extraction toolchain, `fnv_mul_bound` informal assertion, the duplicate-`is_compile_blocking` class. One ledger, each with its current evidence (test/parity/nothing). |
| **VT2** | Per-detector mutation testing | NOT STARTED | M | S2 | mutate each structural-fatal detector + each producer; assert the test/differential suite kills the mutant (catches the 46% never-triggered gap at the detector level, not just producers). |
| **VT3** | Certify `double_script_fatal` / `find_math_ranges` as a refinement of the verified front-end | NOT STARTED | L | V3; VC1 | prove (or differentially bound) that the trusted range-oracle + double-script detector are a sound refinement of the Qed front-end — closes the highest-value trusted seam on the READY path. |

### Track V-PRIORITY — the ordered verification frontier (v3)

**Rationale.** v3 names the ONE verification item that is #1, plus a proven-detector track for the real bug surface (the hand-rolled structural detectors, which are today certified by test battery, not proof).

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **VP1** | **PROMOTE `DetectComplete.v` (classifier completeness) to the #1 verification priority** | NOT STARTED | L | LP-Core grammar spec | prove the **LP-Core detector catches ALL Turing constructs** (completeness of the classifier — no dynamic-`\csname`/`\catcode`/`\write18`/runtime-conditional construct slips through as LP-Core). **Until this is closed, `COMPILATION_GUARANTEE.md` MUST state "LP-Core membership is regex-certified, NOT proven"** (honesty duty). This is the load-bearing gap under Principle 2 (any-unmodelled-cs ⇒ NOT-READY): if the classifier is incomplete, an unmodelled Turing construct could be silently admitted ⇒ cardinal bug. |
| **VP2** | **Proven-detector track — `CompileGateChecks.v`** | NOT STARTED | L | VP1; V3 | prove the hand-rolled **`double_script_fatal`** and **`find_math_ranges`** as **verified refinements of the front-end token stream** — these are **the real bug surface** (the b3bf23f1 precision regressions lived exactly here). Overlaps VT3; VP2 is the Coq-refinement statement, VT3 the trusted-seam framing. |

### Track R — Real-Time Serving (v3: the MAXIMAL real-time engine; nothing sacrificed)

**Rationale.** Deliver the sound verdict **as the user types** — the segment-A wedge (Section 0, clause 1). The correctness plane is fine; this is the latency/interactivity plane. **Standing performance-budget clause applies to every R item.** v3 upgrades this from a serving track to a **provably-sound incremental engine** with an explicit SLO, a machine-checked sound-incremental contract, a nothing-sacrificed budget invariant, and a typed two-channel result — and names the two latent false-READY bugs it must fix.

#### Latency SLO (the target, tracked)
- **Full-doc cold p50 < 100 ms.**
- **Per-keystroke edit-window p50 ≤ 3 ms / p99 ≤ 10 ms.**
- **Warm full-doc < 137 ms @ 316 KB** (tracked).

#### Wedge, corrected honestly (bank it via `scripts/bench_wedge.sh` — cold AND warm columns)
Real-doc pdflatex/Overleaf is **5–60+ s** (multi-pass + biber + tikz + network). Our **13.7 s @ 316 KB is the COLD one-shot CLI** (~55 ms startup dominates small docs); the **warm kernel is 62 / 337 ms**. **We win categorically on the DECIDABLE class delivered PER-KEYSTROKE, NOT by racing pdflatex on completeness.** Measured baseline (real papers, warm binary, local disk, v27.1.57): `--compile-check` = 0.10 s @ 4 KB / 1.5 s @ 30 KB / 2.6–4.8 s @ 80 KB / 13.7 s @ 316 KB (full lint alone = 10.0 s @ 316 KB).

#### Track-R principles (v3)
- **SOUND-INCREMENTAL contract.** `verdict(run_incremental(session, edits)) == verdict(from-scratch)` at **EVERY step**, for **BOTH** the compile-blocking subset AND full lint; **conservative over-invalidation is always safe**. Machine-checked target: **whole-doc verdict == fold(per-chunk monoid summaries)** for the compile-blocking set (delimiter = **signed bracket-depth monoid**; documentclass = **boolean-or**; usepackage-after-begin = **ordered left-fold**), composing with `pdflatex_compile_safe` + `StableNodeIds.v`. Expansion-dependency invalidation: **dirty set = byte-interval ∪ (to-EOF if the edit flips global `$`/`\begin`/`\end`/`\verb` parity, via an O(log n) prefix-parity index) ∪ (all call-sites of any macro whose def the edit touches)**. ⚠ **Two latent FALSE-READY bugs to fix here** (see items): (1) `run_all_incremental` runs compile-blocking rules on truncated per-paragraph chunks → **cross-paragraph `$`/verbatim mis-pair** (fixed by R-PARITY-GATE + R-BOUNDARY + R-MONOID); (2) nothing structurally prevents an **extension registering under a compile-prefix** (`DELIM-`/`ENC-`/`PRT-`) → a policy plugin could name itself into the READY channel (fixed by R-CHANNEL).
- **`fast == full` MACHINE-CHECKED.** Replace the prose comment in `t5_check_fast` with a **differential CI test** + a **static assertion that no compile-blocking rule reads `Semantic_state`/`Event_bus`** (so fast really is a pure prefix of full).
- **"Nothing-sacrificed" BUDGET INVARIANT.** `check_keystroke_budget.py` (sibling of `check_apply_fixes_safety.py`), driving `bench_readiness_kernel.ml` (excludes startup). **Per-stage budget @ 300 KB: parse ≤ 40 / shared ≤ 20 / rules ≤ 30 / structural ≤ 15 / IPC ≤ 5 ms.** EVERY new detector/rule/coverage/policy MUST declare a mandatory **`latency_class` (Incremental | WholeDoc)** on the rule/extension contract (a schema-drift gate): to ride the keystroke plane a check must be **proven-incrementalizable** (Local or Global_monoid footprint) or it runs **background-only**.
- **TYPED TWO-CHANNEL result.** A namespaced **non-extensible VERDICT channel** (extensions STRUCTURALLY barred from naming themselves into READY — today nothing prevents an extension registering under a `DELIM-`/`ENC-`/`PRT-` prefix) + a **POLICY channel off the keystroke path** (the G2 firewall, realized in the type system).
- **Measurement discipline.** **Bypass the whole-doc `Cache_key` on the keystroke path** (it hashes ~source ⇒ every keystroke misses ⇒ full `run_all`; a warm cache MASKS true cold-edit cost).

#### Track-R v3 items (dependency-ordered)

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **R1** | Fast compile-readiness kernel | **SHIPPED** (v27.1.59) | — | — | parse-once + compile-blocking rules; fast==full over 473+150 docs → 0 divergences; sub-150ms to ~74KB. |
| **R-BENCH** | Cold+warm wedge bench, banked | NOT STARTED | S | none | `scripts/bench_wedge.sh` reports COLD and WARM columns at every size band; the SLO numbers are tracked artefacts. |
| **R-BUDGET** | Keystroke budget invariant gate | NOT STARTED | S–M | R-BENCH | `check_keystroke_budget.py` + `bench_readiness_kernel.ml` (excludes startup); per-stage budget enforced @ 300 KB; **fails any change that regresses a stage. Must land before any E/H item.** |
| **R-CTX** | Thread `Shared_analyses` snapshot through `run_all` + `structural_fatal_reasons` | NOT STARTED | M | none | **HIGHEST single speedup**, no deps, **differential-0-diff gated**. Shared analyses computed once, threaded (not recomputed per rule). |
| **R-PARITY-GATE** | `test_incremental_verdict_parity` — **LAND RED FIRST** | NOT STARTED | M | none | **Build FIRST as RED** — it EXPOSES the existing latent false-READY (compile-blocking rules on truncated per-paragraph chunks → cross-paragraph `$`/verbatim mis-pair). Adversarial **straddling fixtures**. **Blocks ALL incremental exposure** until green. |
| **R3a** | Enrich T5 reason to carry byte offsets | NOT STARTED (trivial standalone unblock) | S | — | `T5_rule_violations` carries offsets from `Validators.result` spans so squiggles can be placed. |
| **R-BOUNDARY** | Safe chunk boundaries + real anchor-diff | NOT STARTED | M | R-CTX | `safe_chunk_boundaries` only at **depth-0 blank lines**; fix `diff_snapshots` to a **real anchor-diff**. |
| **R-MONOID** | Footprint field + delimiter monoid | NOT STARTED | M | R-BOUNDARY | add the `footprint` field; **signed bracket-depth delimiter monoid**; whole-doc verdict == fold(per-chunk summaries) for the compile-blocking set. |
| **R-OFFSET** | Document-coordinate chunk view | NOT STARTED | M | R-BOUNDARY | chunks carry document coordinates so findings map to absolute byte ranges. |
| **R-RANGEINDEX** | Edit-aware range oracle, same signatures | NOT STARTED | M | R-CTX; R-PARITY-GATE | edit-aware protected-range index; **identical signatures** (drop-in); parity-gated. |
| **R-BUFFER** | Piece-table + order-statistic dirty → ≤ 2 chunks | NOT STARTED | M | none (parallel) | piece-table buffer; order-statistic index maps an edit to **≤ 2 dirty chunks**. |
| **R2 / R-WARM** | Session daemon `POST /compile-check-session` on the REST accept thread | NOT STARTED | M | R-CTX; **PURE-CACHE contract** | endpoint == `--compile-check` on parity corpus; registry+context warmed once; warm excludes startup (~62 ms @ 50 KB). **Rides the v25/v26 keystroke-service heritage** (`main_service`, `broker`, EDF, `hedge_timer`, `rest_api_server`); **calls the in-process kernel, NOT the SIMD socket.** PURE-CACHE: any cross-request cache is a pure function of source (per-run-cleared `*_context`) ⇒ warm verdict byte-identical to cold. |
| **R-FASTFULL-ENFORCE** | `fast == full` machine-checked | NOT STARTED | S | none | differential CI test **+ static assertion** that no compile-blocking rule reads `Semantic_state`/`Event_bus`. |
| **R-CHANNEL** | Typed two-channel + `latency_class` schema gate | NOT STARTED | M | none | non-extensible VERDICT channel (extensions barred from `DELIM-`/`ENC-`/`PRT-` prefixes) + POLICY channel off the keystroke path; `latency_class` mandatory on the rule/extension contract (schema-drift gate). **Fixes the extension-can-register-under-compile-prefix hole.** |
| **R3 / R-LSP** | Native `latex_lsp` stdio → publishDiagnostics + traffic-light | NOT STARTED | M–L | **R3a (hard, offsets)**; R-WARM | native stdio LSP → `publishDiagnostics` + **traffic-light** + **~8 ms debounce**; squiggle at correct byte range for `$a^b^c$`/unclosed `\begin`/missing `\documentclass`; diagnostics == `--compile-check`. |
| **R-PARALLEL** | OCaml-5 Domain fan-out (CONDITIONAL — measure first) | NOT STARTED | M | R-BUDGET (measure) | **abandon if `rules_ms` already < 10 ms.** If pursued, Domain fan-out over rule families; **watch `Str` globals** (not domain-safe). |
| **R-SIMD** | Candidate-byte enumerator (contingent, last) | NOT STARTED | M | R-PARALLEL result | SIMD candidate-byte prefilter only if profiling shows byte-scanning is the residual floor. |
| **R4 / R-CST** | `reparse_zone` incremental CST (**R4, LAST**) | NOT STARTED (substrate exists, unwired) | XL | R-MONOID; R-RANGEINDEX; whole-doc parity gate; PURE-CACHE | **ONLY if profiling shows PARSE is the residual floor.** ⚠ the one item where soundness directly conflicts with latency: DELIM nesting is whole-doc stateful → chunk-local rescan can miss whole-doc nesting → UNSOUND false-READY; **⚠ ALPHABET SCOPE (D3):** unsound over a POST-EXPANSION alphabet once E1 admits `\def\bea{\begin{align}}` → **scope to PRE-EXPANSION source-structural rules ONLY, or park.** Deferrable indefinitely; if built MUST pass the whole-doc parity gate (R-PARITY-GATE). |

### Track E — Subset Extension (LP-Core growth)

**Rationale.** North-Star clause 3: widen the proven decidable subset — the direct lever on the North-Star metric numerator. Measured trajectory (roots-LP-Core): 38.9% → ~57.6% (def) → ~76.6% (+makeatletter) → ~84% (+let) → ~88.4% (+conditionals). **Sequencing:** E1a/V-CAT → H1 → E2 → E3 → E5 → E4. **Every E item must pass S2 and carry the performance-budget clause; every admission is governed by V-CAT.**

**Note (D1 split):** the old "expansion+resolution substrate" is split into **E1a** (an expansion-PARSER track — today's registry is `\newcommand`-only and **cannot see `\def`**, the 50.4% driver) and **V-CAT** (the catalogue-soundness contracts above).

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **E1a** | Expansion-parser: make `\def` visible | NOT STARTED (registry is `\newcommand`-only) | L | `UserExpand.v`/`UserMacroTermination.v` | the macro registry actually *parses* `\def` (undelimited/delimited param text, `\edef`/`\gdef`/`\xdef` distinction) — the prerequisite for E1's benign check. **`\def` invisibility is the single biggest coverage blocker (50.4%).** |
| **E1** | Benign-`\def`/`\let` admission via macro registry | NOT STARTED (`user_macro_registry.ml` exists but **unwired** to classify) | L | **E1a**; `UserMacroTermination.v`; VC1; reconcile with S3 (direction (a)/(b)) | per-instance benign check (undelimited params, non-recursive via `detect_cycle`, not edef/gdef/xdef, arity ≤9, no catcode/`\csname`) admits benign defs; `classify_lp_core_sound` re-proved under relaxed set; `test_language_contract_cert.ml` **EXTENDED not weakened**; re-measure ~+18–25pp; **zero new false-READY**; passes S2; **VC1 MATH-OPEN contract re-derived if any admitted def opens math.** **Δ North-Star: the single biggest proven-coverage jump.** |
| **E2** | Scoped balanced `\makeatletter…\makeatother` | NOT STARTED | M | E1 (scoped-span pattern); VC1 | lexically-balanced span with NO catcode/`\def`/`\csname` admitted; unbalanced/primitive-containing span demotes; proof update; adversarial fixtures still demote. |
| **E3** | Static conditionals, branch-union semantics | NOT STARTED | M | E2; VC1 | statically-decidable conditional admitted **iff both branches independently LP-Core**; runtime-dependent test demotes; branch-union soundness proof; nested/unbalanced-`\fi` fixtures. |
| **E4** | Static `\csname` constant-folding + whitelisted `\expandafter` | NOT STARTED (deferred last — 5.2%) | M | E3; VC1 | constant-literal `\csname` folds + admits if in-catalogue; dynamic names demote; whitelist of proven-terminating `\expandafter`. |
| **E5** | **Package-contract catalogue — MERGED INTO V1-Catalogue (`ProvidesCatalogue`)** | PARTIAL (`extension_registry.ml`: 5 built-ins + `evaluate`/`over_claims`, not ranked/wired) | L (shared with V1) | none hard; most valuable after E1–E3; VC1 (version/staleness contract) | **E5 ≡ V1 ≡ the H1 undefined-cs dictionary — ONE `ProvidesCatalogue`, not three catalogues.** Rank packages **by MARGINAL proven-coverage** (NOT raw `\usepackage` frequency), add to the empirical KNEE (Observatory), risk/support ≤ `max_support_for_risk`; wire into classifier; `over_claims=false` per entry (over-listing is the only G1 hazard); **catalogue-staleness contract (VC1) enforced.** |

### Track H — Heuristic Tier (deliberately NON-PROVEN, INVERTED soundness contract)

**Rationale.** North-Star clause 4 + **the actionable-NOW answer for the ~60% LP-Extended majority.** H1 gives segment-A authors a verdict on documents the proof cannot reach today — and its signals are **independent of `\def` admission**, so it is DECOUPLED from E1 and can ship NEAR-TERM.

> **⚠ H1 is NOT a semantic / macro-universe item.** Its soundness contract is **INVERTED**: **a false LIKELY-OK is tolerable BY DESIGN**, whereas in the proven tier a false-READY is the cardinal bug. Because the contract is inverted, H1 **MUST be visually and API-separated from the proven READY verdict** — a heuristic guess may NEVER be rendered as, or mistaken for, a proof. (Substrate already exists: the proven-sound v2 ML span-extractor, `proofs/ML/SpanExtractorSound.v`, F1=0.9799.)

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **H1** | Heuristic "likely-compiles" predictor — **pull NEAR-TERM, DECOUPLED from E1** | NOT STARTED | M–L | R1/R2 (deliver as-you-type); overlaps V1 undefined-cs class; **NOT E1** | `--compile-check` gains three states: **PROVEN-READY** / **LIKELY-OK(p)** / **LIKELY-FAIL(reasons)** — heuristic states VISUALLY/API-distinct, NEVER shown as proof. **Minimal near-term signal set (independent of `\def` admission): undefined-cs dictionary (base+package catalogue) + brace/`$`/env balance** (+ math-mode leak, package conflicts from E5 later). **monotone**: PROVEN-READY never downgraded; calibrate p on 6,899 real papers + report precision/recall vs pdflatex; **false LIKELY-FAIL tolerable, PROVEN-READY-that-fails is NOT.** **Δ North-Star: gives the ~60% LP-Extended majority an actionable non-proven verdict NOW** (does not move the *proven* numerator, but is the daily segment-A value while E-track grows it). |

### Track P — Policy / Template Enforcement (first-class application track)

**Rationale (strategy reframe).** Compile-fatality is **one policy among many**, all sharing the verified parser substrate. The rule engine is **NOT** maintenance-mode: **user-defined, provably-checked rules are CORE to segment B** (editors/publishers). This is the flagship monetizable application (Section 0). Track "C" (below) is the *rule-authoring / coverage* mechanics; Track **P** is the *editor-facing product*: an editor uploads a required template / house style / submission policy and every submission is provably, localized-ly checked **without a per-submission compile**.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **P1** | User-defined rule sets (`.lppolicy`) as first-class, provably-checked | PARTIAL (WS9 policy Stages 1–2 delivered + FROZEN; WS12 extension plane Stages 1–2 delivered + FROZEN) | M | WS9/WS12 seams (delivered); verified parser substrate | an editor authors a policy (required template + style + submission constraints); the engine checks every submission against it, **localized** (CST/graph spans) and **without compiling**; policy is config (`.lppolicy`, line/JSON), never baked into core; default output unchanged when no policy is loaded. |
| **P2** | Template-conformance enforcement (the flagship editor application) | NOT STARTED | M–L | P1; localization (R3a offsets); trust backbone (LP-Core proof) | editor uploads a **required template**; submissions are provably checked for conformance + compile-fatality **at scale, without per-submission compiles**, with precise localization and the machine-checked trust of the LP-Core backbone. **This is the segment-B monetizable surface.** |
| **P3** | Compile-issue auto-fix = REVIEW-GATED CANDIDATES (not silent auto-fix) | PARTIAL (Bucket-C candidate channel exists: 124) | M | Bucket-C infra | fixing compile/policy issues is surfaced as **review-gated candidates** (intent-dependent — the STYLE-033 / SPC-018 soundness lesson), **never silent auto-fix**; author/editor reviews before apply. |
| **P4** | **The `.lprules` DSL — a sound, sandboxed, DECIDABLE declarative policy language** | NOT STARTED (design below) | L (multi-day) | P1; the WS12 foreign-contract boundary; a `rule_fires_on_project` dispatch-mirror (built first); G2 firewall | full design in **§Track-P DSL** below. First milestone: the 3 cheapest predicates as a Coq-extracted total evaluator emitting `Validators.result`, a `--venue` loader, ONE real bundle (`acmart`), and `forbid-package total` proven. |

#### Track-P DSL — full design (a sound, sandboxed, DECIDABLE declarative policy language)

**What it is.** A sandboxed **DECLARATIVE** `.lprules` DSL: each rule = **predicate × context × count/length-bound → finding**, with **NO loops, NO recursion**. The absence of loops/recursion ⇒ a **sound sandbox** ⇒ every rule is a **DECIDABLE, total function**. This is the **ADDITIVE require/forbid path** the current `editorial_policy.ml` lacks — today it is **SUBTRACTIVE-ONLY** (`disable` / `severity` / `waive`); Track P adds require/forbid rules that **COMPILE to a `Validators.result` MERGED (not subtracted)** into the finding stream. By **G2**, the DSL emits only into the POLICY channel and only ever ADDS a conservative NOT-READY ⇒ it can never manufacture a false-READY.

**Predicate classes** (all bounded / decidable):
- forbid / require a **package**;
- forbid / require a **control sequence in a context**;
- forbid / require an **environment**, plus **require-env-order / section-nesting grammar**;
- **bounded structural counts** (e.g. "≤ N `\footnote` per page-equivalent");
- **length limits** (e.g. title ≤ N chars);
- **source-DECLARED numeric asserts** (geometry margins, fontspec font/size — read from the source's own declarations, not from a rendered PDF).

**Implementation — DEEP EMBEDDING with a Coq-extracted total evaluator** (reuse the `BodyTokenFrontEnd.v` extraction pattern): the DSL is a Coq inductive; a Coq-extracted **total** evaluator runs it. Prove ONCE a **meta-theorem**: *every well-typed DSL rule is total, deterministic, side-effect-free, and raises no finding outside its declared span.* A `rule_fires_on_project` **dispatch-mirror** must be built FIRST (multi-day) so the extracted evaluator can be dispatched over the project the same way the built-in rules are.

**Scoping & distribution.** Opt-in `--venue acmart`; **default output BYTE-IDENTICAL** when no venue is loaded. Composable via the `extension_contract` support-fold; attached through the **WS12 foreign-contract boundary**. Signed-bundle distribution. A bundle carries a **`min_verdict_tier`** field so an editor can demand **PROVEN-READY** (rejecting anything only heuristic).

**First milestone (concrete):** the **3 cheapest predicates** — `forbid-package`, `forbid-cs`, `require-env-order` — as a total evaluator emitting `Validators.result`; the `--venue` loader; **ONE real bundle** (`acmart` — already half-specified in `specs/v26/language_contract.yaml`); prove **`forbid-package` total**.

### Track C — The SHARED RULE-EXECUTION SUBSTRATE (rule-authoring mechanics; the machine Track P compiles INTO)

**Rationale (v3 reframe — do NOT demote to maintenance).** Track C is **the shared rule-execution substrate**: the 660-rule engine + `run_all` + the fix/candidate channels are **the machine the policy plane (Track P) COMPILES INTO**. V2 (660-rule Coq soundness) and the Track-P DSL soundness meta-theorem are therefore the **SAME investment** — proving the rule-execution substrate sound is what lets a *user-authored* venue rule be sound-by-construction. So Track C is first-class, not maintenance: **KEEP the ≥10-new-Bucket-A-producers-per-patch author cadence** (`FIX_PRODUCER_LEDGER.md:781`; Bucket A = 466 rules, 167 shipped, 299 pending). Complete the "every fixable rule has a fix-or-candidate" DoD as the *authoring/coverage* substrate that Track P productizes.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **C-DOD1** | Close the 2 outstanding DoD violators | NOT STARTED | S–M | none | **BIB-010 shipped (v27.1.33)**; **DE-006 and ENC-006 still `pending`** — wire each as verbatim-safe fix or Bucket-C candidate; then a fresh grep-grounded 643-rule re-audit. |
| **C-KR1** | Wire 5 known-recoverable diagnose-only rules | NOT STARTED (all 5 still plain `mk_result`) | S–M | none | MATH-056, PKG-001, TAB-002, TAB-007, TAB-011 each wired as Bucket-C candidate or verbatim-safe fix; candidate never auto-applies; differential 0-diff; `runtest` green. |
| **C-COV1** | Remaining candidate-able diagnose-only coverage | PARTIAL (family batches v27.1.44–51; tail asserted non-recoverable) | XL | KR-1 patterns | each newly-recoverable rule → determinate-target candidate; residual documented with per-rule reason; regenerated into backlog. |
| **C-WS1** | Promote deferred whitespace pilot rules (TYPO-006/007/008/024) | DEFERRED (`docs/archive/RULES_PILOT_TODO.md`) | S–M | fix-set DELEGATION + post-pilot graduation gate | deferred pending (1) fix-set delegation (TYPO-007 spaces-only vs SPC-005 tabs) and (2) the graduation gate (FP review on real corpus + perf smoke). ALL pilot TYPO rules are `maturity: Draft`, gated behind `L0_VALIDATORS=pilot`. |
| **C-NLP1** | TYPO-019/020/030/031 sentence-rewrites | DEFERRED by design | L | NLP/dictionary substrate (partial prior art: v2 ML span-extractor) | candidate (never auto-fix) gated by a real model; no false rewrites. Stays deferred until product funds NLP tier. |
| **C-FD1** | CJK/RTL byte-level feature-detection migration | PARTIAL (`Japanese_cjk` + `body_required_features` exist; general RTL/bidi absent) | M | v27.1.58 front-end (landed); `compile_evidence.ml` enum extension | CJK/RTL detected from token stream drives `all_features_compatible` vs engine profile; false-READY holes (CJK without capable engine) closed; **proven, not heuristic.** |
| **C-DR1** | Document the SETTLED 167 producer decomposition + cross-ref the two ledgers | OPEN (doc-only) | S | none | **Producer count SETTLED at 167** = 70 (`mk_result_with_fix`) + 47 (`with_fix`/`fix_of`) + rest. Document the decomposition + cross-reference `FIX_PRODUCER_LEDGER.md` + backlog. **Do NOT "correct" 167 down to 70.** The **"596" figure is a phantom** (appears nowhere; ignore it). |

### Parked (ADR-010)

**WS10 (collaboration & review) + WS11 (platform roles/permissions/deployment) — PARKED, not abandoned** (`docs/v27/adr/ADR-010-park-ws10-ws11-collaboration.md`, Accepted 2026-07-12). Effort if revived: **XL**. Compatibility contract so a future WS10/WS11 is *additive, not a rewrite*:
- **Stable anchors** — findings/edits keyed by CST/project-graph spans (byte-lossless CST).
- **Externalized review state** — WS9 Stage-2 `editorial_review.ml` (`.lpreview`) is the single-user precursor of WS10 threads; keep decoupled.
- **Deterministic, side-effect-free core** — `Validators.run_all` pure over source + per-run-cleared `*_context` (also the R2/R4 PURE-CACHE contract).
- **Policy/permission seam** — WS9 policy + WS12 contracts are config+CLI layers that never change default output; WS11 extends the same seam.
- **No format lock-in** — `.lppolicy`/`.lpreview`/manifests are line/JSON configs.

*(Already delivered and **FROZEN**, NOT parked: WS9 editorial policy Stages 1–2 + WS12 extension plane Stages 1–2 — the Track-P substrate.)*

---

## 4. Classification of every remaining item

### A. Deterministic-structural — closeable now (soundly, each must pass the S2/OBS3 generative fuzz gate)
- **OBS0/OBS1/OBS2/OBS3** (observatory — infra), **S0** (infra — BLOCKER), **S1** (ship v27.1.60), **S2** (the standing generative gate itself), **S6** (`illegal_param_number_sound`, ZERO deps, 8→7), **S3** (misplaced-`&`, shippable independently via (b)), **S5-T4** (source-only duplicate-label), **SO1** (READY oracle definition).
- **R-track v3** (R-BENCH/R-BUDGET/R-CTX/R-PARITY-GATE/R-BOUNDARY/R-MONOID/R-OFFSET/R-RANGEINDEX/R-BUFFER/R-WARM/R-FASTFULL-ENFORCE/R-CHANNEL/R-LSP + R3a — serving/incremental engineering). **R-CST/R4** is deterministic-structural but its chunk-local incrementalization is the one soundness-vs-latency conflict (see B/notes, **alphabet-scoped** to pre-expansion, under R-PARITY-GATE). R-PARALLEL/R-SIMD contingent.
- **E2, E3, E4** (balanced-span / branch-union / constant-fold — statically decidable), governed by V-CAT.
- **P1, P2, P3, P4** (policy/template enforcement + the `.lprules` DSL — deterministic total functions over the verified parse; sound-by-G2).
- **C-KR1, C-COV1, C-WS1, C-DOD1, C-DR1, C-FD1** (candidate/pilot wiring, doc, byte-level detection).

### B. Semantic / catalogue — DECIDABLE & INCREMENTAL under G1 (the residual is UNBUILT CATALOGUE, not impossibility)
- **S7** (`math_mode_leak_sound`, needs only the catalogue mode-bit, 7→6). **V1-Catalogue ≡ E5 ≡ H1's dictionary** (`ProvidesCatalogue` — ranked by marginal coverage, built to the OBS1 knee; turns the 8→6→… residual into correct NOT-READY under G1). **V2** (660-rule Coq soundness ≡ DSL soundness meta-theorem), **V3** (byte-level cert of `detect`/`Parser_l2`/range-oracle), **VP1 `DetectComplete.v`** (#1 priority) + **VP2 `CompileGateChecks.v`**, **V-CAT** (admission contracts), **V-TRUSTED-BASE** (glue certification — elevated).
- **S5-T1** (bounded-expansion probe), **SE1** (multi-engine capstones — option A).
- **E1a + E1** (make `\def` visible, then admit benign defs — the coverage jump; the E1/S3 coupling lives here).
- **R-CST/R4-statefulness** (whole-doc delimiter nesting — the soundness half of R4).

### H. Heuristic (deliberately non-proven, inverted contract) — its OWN class
- **H1** — the *labelled* likely-compiles tier. Shares the ONE `ProvidesCatalogue` undefined-cs dictionary with V1/E5, but under an inverted contract, rendered separately from proof. **Decoupled from E1 → pullable near-term.** As the catalogue grows, *parts* of H1 promote into the proven tier (V1); H1 itself is never a proof.

### C. Impossible-by-design — excluded from the guarantee
- **Full-LaTeX total compile-decision** (Turing-complete ⇒ undecidable). Anything needing `\write18`/`\catcode`/dynamic `\csname`/runtime-conditional expansion → LP-Foreign → NOT-READY or H1, never proof.

### D. Parked-by-decision
- **WS10 / WS11** (ADR-010). **C-NLP1** (deferred until product funds an NLP/dictionary substrate).

---

## 4b. Three swim-lanes (per-segment sequencing) — and the RECOMMENDED BEACHHEAD

The sequenced plan splits into three parallel swim-lanes, one per consumer segment. Each lane states its **proving-payoff** (proving pays off DIFFERENTLY per segment — never wasted).

### Lane (A) — AUTHORS (interactive, segment A)
R-track LSP (**R-LSP / R3**) + **H1 traffic-light** + the **≥10-producer author cadence** (Track C) + **E1**. **Proving-payoff:** the proof is NOT the daily hook here — SPEED + LOCALIZATION + FIX + coverage-across-all-docs is; proving pays off *indirectly* by letting the traffic-light show a distinct, trustworthy PROVEN-READY light among the heuristic ones (H1's inverted contract stays visually separate).

### Lane (B) — EDITORS / PUBLISHERS — ⭐ the RECOMMENDED BEACHHEAD
**Why the beachhead:** the capability is **~90% built**, it **tolerates current latency** (batch/submission-time, not per-keystroke), and it **does NOT need R4** (the hard incremental tail). Deliverables: **S4-as-PRODUCT** — run `diff_compile_check` over the full **6,899-root** tree and **publish a SEMVER'd SLA confusion matrix** — + **Track-P venue bundles** (the `.lprules` DSL, `--venue acmart`). **Proving-payoff:** here the proof IS the product — the machine-checked trust backbone is exactly what lets an editor rely on a READY / a policy-pass **without a per-submission compile**; the SEMVER'd matrix + `over_claims=false` catalogue curation are the sellable soundness guarantees.

### Lane (C) — PIPELINES / TOOL-BUILDERS (segment C)
A stable **`POST /compile-check` JSON route** + a **frozen, semver'd verdict schema** (the two-channel result, R-CHANNEL). **Proving-payoff:** an automated consumer needs a verdict it can *rely on without re-compiling* — the proof + the frozen schema + the 0-false-READY gate are precisely the machine-trust that makes the substrate buildable-on.

---

## 5. Sequenced Roadmap

### Hardening closed THIS PR (#498)
- **bail ⇒ demote** — the 4096-frame double-script bail now demotes to NOT-READY (was conservative toward false-READY). **DONE.**
- **`is_compile_blocking` single-source** — removed the duplicate prefix-only shadow in `compile_contract.ml`; **single source of truth is `Validators.is_compile_blocking`.** **DONE.**
- **Roadmap fact-checker** (`scripts/tools/check_roadmap_facts.py`) — anti-drift gate on every load-bearing number. **DONE.**

### Near-term (RESEQUENCED — infra, reproducibility & the zero-catalogue wins FIRST)
1. **OBS0 + S0 — commit the classify driver + verification infra FIRST.** Commit `observatory/classify_driver.ml` (**before quoting 38.9/60.2/0.9**), `bench_classify`/`ampfuzz`/the hash-manifested over-rejection corpus; wire `diff_compile_check.sh` into the release gate (hard-fail on new false-READY where pdflatex present); pin+assert `pdflatex --version`; emit the confusion matrix as committed JSON. **Everything downstream depends on this.** *(Effort M; needs local pdflatex.)*
2. **S1 — ship v27.1.60 to main** (bail⇒demote DONE). Closes the `$a^b^c$`-class holes (**10 → 8**), **0 over-rejection**. Merge → tag → `diff_compile_check.sh` = 8 known / 0 new. *(Effort S; only user merge pending.)*
3. **S6 + S7 — the ZERO-catalogue residual-shrinkers, do NOW.** `illegal_param_number_sound` (**8→7**, zero deps) + `math_mode_leak_sound` (**7→6**, needs only the catalogue mode-bit). **Do NOT defer these to a heuristic tier** — they are decidable source-structural proofs that seed `ProvidesCatalogue`. *(Effort S each.)*
4. **S2 / OBS3 — the GENERATIVE grammar-directed fuzz gate as BLOCKING infra**, implemented inside the observatory (false-READY discovery-rate per N-thousand → 0). Enumerate every detector branch × LP-Core construct class (incl. `\left..\right]` mismatch, extra alignment tab, "Dimension too large", `\verb`-newline, `\end{document}` in an open group). **Standing before any S3/S5/E detector work.** *(Effort L.)*
5. **R-PARITY-GATE — LAND RED FIRST.** Build `test_incremental_verdict_parity` before ANY incremental exposure; it exposes the latent cross-paragraph `$`/verbatim false-READY. **Blocks R-BOUNDARY/R-MONOID/R4 until green.** Pair with **R-BENCH → R-BUDGET** (budget gate before any E/H). *(Effort M.)*
6. **H1 (minimal, near-term, DECOUPLED from E1)** — undefined-cs dictionary (the seed of `ProvidesCatalogue`) + brace/`$`/env balance → a clearly-labelled LIKELY tier for the ~60% LP-Extended majority. v2 span-extractor ML substrate (F1=0.9799) exists. **Segment-A value NOW.** *(Effort M–L; UI/API-separated from proof.)*
7. **BEACHHEAD START (lane B) — S4-as-PRODUCT + Track-P DSL milestone-1.** Run `diff_compile_check` over the 6,899-root tree, publish the SEMVER'd SLA matrix; build the 3-predicate `.lprules` evaluator (`forbid-package`/`forbid-cs`/`require-env-order`) + `--venue acmart` + prove `forbid-package` total. **~90% built, tolerates latency, no R4 needed.** *(Effort M–L.)*
8. **C-DR1 + C-DOD1 + R3a → R2 — hygiene + offsets + endpoint.** Document the **settled 167** decomposition (drop phantom "596"); close DE-006/ENC-006; R3a offsets then the persistent endpoint. *(Effort S–M.)*

### Medium-term
- **S4 — full 6,899-paper differential** over the S0 corpus; publish the versioned confusion matrix (per LP-tier, per engine/year).
- **E1a → E1 — make `\def` visible, then benign-`\def`/`\let` admission** — the single biggest proven-coverage jump (~+18–25pp). **Coupled with S3:** resolve the `\def\bea{\begin{eqnarray}}` boundary via **direction (a)** (model alignment-shortcut expansion) OR **(b)** (carve those defs into LP-Extended → S3 ships independently first). Governed by **V-CAT** (re-derive `find_math_ranges` if any admitted def opens math).
- **R3 — LSP server** (hard dep: R3a; R2 preferred) — the product surface for the traffic-light.
- **P1 → P2 — policy/template enforcement** — the segment-B monetizable surface, on the frozen WS9/WS12 seams + R3a localization.
- **SE1 — resolve multi-engine scope** (option A capstones OR option B ADR + delete the alias claim).
- **E2 → E3** — scoped `\makeatletter`, then static conditionals.
- **C-KR1 → C-WS1 → C-COV1** — wire the 5 known-recoverable rules, graduate the whitespace pilot rules, then the tail.

### Long-term
- **VP1 (`DetectComplete.v`) — the #1 verification priority** — classifier completeness (LP-Core catches ALL Turing constructs); until closed, `COMPILATION_GUARANTEE.md` says "LP-Core membership is regex-certified, not proven." Then **VP2 (`CompileGateChecks.v`)** — prove `double_script_fatal`/`find_math_ranges` as verified refinements (the real bug surface).
- **V-TRUSTED-BASE (VT1→VT2→VT3)** — trusted-glue ledger, per-detector mutation testing, refinement cert. **Elevated above V4.**
- **V1-Catalogue (`ProvidesCatalogue`) — IN-SCOPE, incremental, ranked by MARGINAL coverage, built to the Observatory knee** (≡ E5 ≡ H1's dictionary — ONE catalogue). NOT "accept the residual" — the residual is UNBUILT CATALOGUE (G1). **V2 — all-660 Coq soundness** (same investment as the DSL soundness meta-theorem). **V4 — ZERO-VALUE-skip; ATTEMPT the isolated re-proof to surface divergence, don't ADR-paper blindly.**
- **Track-P DSL (P4)** — the `.lprules` deep-embedding + extracted total evaluator + the once-proven totality meta-theorem; more venue bundles beyond `acmart`.
- **E4** — `\csname`/`\expandafter` (lowest value, last), on the shared catalogue.
- **SEC1 / HB1** — sandbox the substrate; optional pdflatex backstop (feeds S2/OBS3).
- **R-CST / R4 — incremental CST** — LAST, only if profiling shows PARSE is the residual floor; **alphabet-scoped to pre-expansion**, under R-PARITY-GATE. Deferrable indefinitely. (R-PARALLEL/R-SIMD similarly contingent — measure first, abandon if `rules_ms` < 10 ms.)
- **WS10/WS11** — only on a product decision (ADR-010).

### Cross-track dependency map
- **OBS0 (classify driver) gates the 38.9/60.2/0.9 quote; S0 gates credible S2/S4/E numbers** — infra first.
- **OBS1 marginal-coverage curve decides the V1-Catalogue KNEE** (the plotted derivative, not a preset N).
- **S2/OBS3 (generative gate) is BLOCKING infra for S3 / S5 / E-track / every future detector** — not a leaf.
- **S6 (zero deps) + S7 (catalogue mode-bit only) drop the residual 8→6 BEFORE the big catalogue** — do NOW.
- **V1 ≡ E5 ≡ H1's undefined-cs dictionary — ONE `ProvidesCatalogue`.** Under **G1** an incomplete catalogue only shrinks proven-NOT-READY (never a false-READY); over-listing is the only hazard (VC1 `over_claims=false` + differential test).
- **H1 is DECOUPLED from E1** → pullable near-term; its dictionary seeds `ProvidesCatalogue`; stays rendered separately from proof.
- **E1a (make `\def` visible) precedes E1**; **S3 ⇄ E1** share the `\def`/alignment boundary — direction (b) DECOUPLES them so S3 ships first.
- **Every E admission ⇒ a V-CAT contract** (MATH-OPEN re-derivation, ABSENCE, CATALOGUE version/staleness).
- **Track R v3 order:** R-BENCH → R-BUDGET (before any E/H) ; R-CTX (highest speedup) ; **R-PARITY-GATE FIRST as RED** (blocks all incremental exposure) → R-BOUNDARY → R-MONOID/R-OFFSET ; R-RANGEINDEX (dep R-CTX+R-PARITY) ; R-BUFFER (parallel) ; R-WARM (dep R-CTX) ; R-FASTFULL-ENFORCE ; **R-CHANNEL** (fixes the extension-under-compile-prefix hole) ; R-LSP (dep R-WARM+R3a) ; R-PARALLEL/R-SIMD/R-CST contingent-last.
- **G2 policy firewall ⇒ Track P is sound-for-free** (additive-toward-NOT-READY, off the keystroke path, in the POLICY channel of R-CHANNEL). Track-P DSL (P4) COMPILES INTO the Track-C rule-execution substrate; **V2 ≡ the DSL soundness meta-theorem.**
- **BEACHHEAD = lane B (editors)** — S4-as-PRODUCT + Track-P bundles; ~90% built, tolerates latency, needs NO R4.
- **P1/P2 ⇒ frozen WS9/WS12 seams + R3a localization + the LP-Core trust backbone.**
- **VP1 (`DetectComplete.v`) is the #1 verification priority; VP2 certifies the real detector bug surface.**
- **SE1 (multi-engine) parameterizes the North-Star promise by engine + TeX-Live year.**
- **C-FD1 ⇒ v27.1.58 front-end** (landed).

---

## 6. Open Decisions & Risks

### Open decisions (need a call / sign-off)
- **Q-STRATEGY (the framing question):** is the flagship the **proven compile-verdict** or the **one-engine diagnose + fix + policy product**? **Recommendation: the latter framing** — one verified document-understanding engine (compile-prediction + policy-enforcement + localization + fix + trust), with the proof as the trust backbone for segments B/C, not the whole pitch (Section 0).
- **Q-ENGINE (S-ENGINE):** multi-engine scope — **(A)** real per-engine capstones + differential + `engine`-through-`of_root` + engine/year-parameterized promise, or **(B)** ADR scope to pdflatex-only + DELETE the xe/lua alias-as-guarantee claim + demote non-pdflatex to NOT-READY/heuristic. **Resolve before any multi-engine READY is emitted** (invisible false-READY risk today).
- **Q-BACKSTOP (H-BACKSTOP):** ship `--compile-check --confirm-with-pdflatex` (downgrade-on-disagree + feed S2)? Value: self-improving oracle + trust escape-hatch for segment C. Needs SEC1.
- **Q-S3/E1 (the coupling):** where does `\def\bea{\begin{eqnarray}}` land? **(a)** admit E1 → the `&` gate models alignment-shortcut expansion; or **(b)** carve alignment-shortcut defs into LP-Extended (S3 ships independently for strict LP-Core). **Recommendation: (b) — carve into LP-Extended, DECOUPLE** so S3 ships first. Resolve before E1 admits alignment-macro defs.
- **Q-E1 granularity:** admit a benign `\def` **per-instance** (permissive, forces the `&` coupling) or **per-document** (whole def-set benign-and-acyclic — 62.2% of def-demoted docs; simpler to prove)? **Recommendation: per-DOCUMENT first** (simpler to prove, decouples from `&`).
- **Q-catalogue-knee:** where does `ProvidesCatalogue` stop growing? **Answer = the plotted derivative** — build to the empirical KNEE of the OBS1 marginal-coverage curve (rank by marginal proven-coverage, NOT raw `\usepackage` frequency), not a preset N.
- **Q-DSL-conformance-spec:** what is the exact `.lprules` grammar + the well-typedness judgement the totality meta-theorem quantifies over? (Needs a frozen spec before P4 milestone-1.)
- **Q-super-chunk-degeneration:** if many edits flip global `$`/`\begin` parity, the to-EOF dirty rule can degenerate to whole-doc rescans — is the O(log n) prefix-parity index enough, or is a cap needed?
- **Q-to-EOF-reparse-on-`$`:** confirm the to-EOF invalidation on a parity-flipping edit is both sound (never misses) and acceptable (rare enough not to blow the keystroke budget).
- **Q-R3-build-vs-buy-LSP:** hand-rolled OCaml JSON-RPC LSP vs. an OCaml LSP lib (M vs L + UTF-16 position-mapping) + debounce policy (~8 ms).
- **Q-V1:** ~~build the semantic tier or accept the 8-doc residual permanently~~ — **RESOLVED in v3: BUILD IT (V1-Catalogue).** Under G1 it is decidable, incremental, and can only shrink the residual (never manufacture a false-READY). The question is no longer *whether* but *how far* — answered by Q-catalogue-knee (the OBS1 derivative). H1 and V1 share the ONE catalogue.
- **Q-V4:** ZERO-VALUE-skip (byte-identical capstone). **v3 resolution: ATTEMPT the isolated re-proof in a throwaway branch to SURFACE any hidden abstract-vs-faithful divergence** — don't ADR-paper it blindly. Clean ⇒ keep the bridge + rewrite acceptance #6; divergence ⇒ that's the finding. DE-PRIORITIZED below all coverage/utility work.
- **Q-H1/V1 boundary:** one modelled undefined-cs catalogue serving BOTH tiers, or two mechanisms? (H1 output stays UI/API-separated from proof either way.)
- **Q-E5/venue authority:** are built-in package/venue contracts *authoritative for compile-check* (→ proven tier) or advisory-only (→ H1)? **Recommendation: authoritative ONLY under a curated `over_claims=false` + a differential test** (the G1 over-listing hazard is the sole way a catalogue entry manufactures a false-READY), under a pinned version/option/TeX-Live-year staleness contract (VC1). Otherwise advisory (→ H1).
- **Q-R4 need:** is incremental DELIM/ENC needed for v1 at all? With the alphabet-scoping + whole-doc-nesting soundness risk, "no" is the safe default while ≤74KB holds.
- **Q-R3 build-vs-buy:** hand-rolled OCaml JSON-RPC LSP vs. an OCaml LSP lib (effort M vs L + UTF-16 position-mapping). Plus debounce policy.
- **Q-scope:** formally spec + version the "Latex-epsilon"/LP-Core boundary name so "provably compiles" has a citable scope (currently only `LP-Core/Extended/Foreign` in `specs/v26/language_contract.md`).
- **Q-DoD:** DoD **not** fully closed — **DE-006/ENC-006 still pending**; no full grep-grounded 643-rule re-audit. Needs C-DOD1.
- **Q-WS10/11:** pending product decision; PARKED stands.
- **Q-NLP funding:** TYPO-019/020/030/031 + Bucket-B STYLE rules deferred until a decision funds the NLP substrate.

### Key risks
- **R-drift:** v27.1.60 unpushed ⇒ `COMPILATION_GUARANTEE.md` narrates the gate + "8 false-READY" as landed while `main`'s tag is v27.1.59 and shows 10. Mitigated by the new fact-checker (§5) + S1 merge.
- **R-north-star-not-activity:** producer/theorem/proof-file counts are infrastructure, NOT the success metric. Do not report activity as coverage; report **proven-verdict coverage at zero false-READY** on the committed corpus.
- **R-single-source-of-truth (fixed, now a guardrail):** the duplicate prefix-only `is_compile_blocking` in `compile_contract.ml` is REMOVED (DONE this PR); do not reintroduce. Single source = `Validators.is_compile_blocking`.
- **R-multi-engine-false-READY (S-ENGINE):** xe/lua aliases are the same proof object but `feature_compatible` is engine-sensitive and the differential is pdflatex-only → a lualatex user can get an **invisible false-READY** until Q-ENGINE is resolved.
- **R-oracle-undefined (S-ORACLE):** without a precise READY oracle + documented false-READY classes (multi-pass/aux/bbl staleness; recoverable-but-wrong) + a bib/biber probe, "READY" is ambiguous and the matrix under-counts.
- **R-trusted-base (ELEVATED):** the real bugs live in the UNPROVEN glue (nat-pow blowup, duplicate `is_compile_blocking`, STYLE-033, 46% never-triggered producers) — not the abstract model. `fnv_mul_bound` asserted informally. Mitigation = V-TRUSTED-BASE, above V4.
- **R-additive-bridge:** Tier-3 Stage-6 is an additive consistency result, NOT the plan's re-proof; if the abstract capstone diverges from the faithful model the bridge won't catch it — but re-proving is de-prioritized (V4) since divergence would surface via S2/HB1.
- **R-empirical-detectors:** structural-fatal detectors are pinned "against pdflatex" by a *test battery*, not a Coq proof; a missed edge (unusual catcode/engine version) could re-open false-READY. **Mitigation = S2 (generative gate).**
- **R-coverage-gates-are-not-full-surface:** "differential 0-diff + convergence" exercised only ~54% of producers (69/150 never corpus-triggered). Full-surface safety needs `check_producer_coverage.py` + output inspection + per-detector mutation (VT2).
- **R-fast==full:** verdict-equality is an equivalence argument + differential gate, not a Coq proof.
- **R-E1-cardinal:** relaxing blanket `\def`-demotion is precisely the move that could introduce a false-READY. `test_language_contract_cert.ml` must be EXTENDED (recursive/mutual/delimited/edef still demote) before any admission; `classify_lp_core_sound` re-proved; VC1 contracts enforced. Unknown ⟹ demote.
- **R-R4-statefulness + alphabet (D3):** DELIM nesting is whole-doc stateful; chunk-local rescan is UNSOUND, and **doubly so over a post-expansion alphabet once E1 admits `\def\bea{\begin{align}}`** → scope R4 to pre-expansion source-structural rules or park it; parity gate before any wiring.
- **R-count-authority:** 167 (ledger) is generated independently from 124 (candidates) and 70 (`_with_fix_exempt` subset); the new roadmap fact-checker (§5) closes the cross-file drift hole. C-DR1 documents the reconciliation.
- **R-squash-drops-commits:** a squash strands later commits (v27.1.5 lost 11 producers). Serialize; keep a recovery plan.
- **R-residual-assertion:** the 402 "non-candidate-able" diagnose-only rules are a *per-family* assertion, not individually re-audited. Re-audit against `rules_v3.yaml` before declaring done.
- **R-corpus-representativeness:** the lint corpus is 470/473 LP-Core (too clean); the 88.4% recovery number rests on an UNTRACKED `bench_classify` driver + a 15+-day-old scratch analysis. **S0 commits the bench + corpus under version control** before quoting E-coverage as a commitment.
- **R-security (SEC):** the differential harness / any pdflatex backstop / the range-oracle execute or parse untrusted LaTeX — `-no-shell-escape`, sandbox+timeout, bound `\input` to project root, fuzz the oracle (SEC1) before exposing any of it as a service.
- **R-tags-without-commits:** v27.1.58/59 tags are on `origin/main`; the tree is v27.1.60 (PR #498, pending merge/tag). C-FD1 depends on the front-end (confirmed on origin/main this session).

---

*v3 adds: the G1/G2 keystones; V1-Catalogue (`ProvidesCatalogue`, ≡ E5 ≡ H1's dictionary); S6/S7 zero-catalogue residual-shrinkers; the Coverage Observatory (`latex-parse/observatory/`: `classify_driver.ml`, `report_vNN.json`, `corpus_manifest_vNN.json`); the Track-P `.lprules` DSL (deep embedding + extracted total evaluator + totality meta-theorem, `--venue acmart`); VP1 `DetectComplete.v` (#1 priority) + VP2 `CompileGateChecks.v`; Track-R v3 (Latency SLO, sound-incremental contract, budget invariant, typed two-channel result, R-BENCH…R-CST); the three swim-lanes with editors/publishers as the recommended beachhead. Sources: `docs/COMPILATION_GUARANTEE.md`, `governance/project_facts.yaml`, `specs/v27/{FIX_PRODUCER_LEDGER,CANDIDATE_BACKLOG}.md`, `specs/rules/{rules_v3,rule_contracts}.yaml`, `docs/archive/RULES_PILOT_TODO.md`, `docs/v27/adr/ADR-010-*.md`, `latex-parse/src/{compile_contract,compile_gate_checks,validators,language_profile,unsupported_feature,user_macro_registry,extension_contract,extension_registry,compile_evidence,validators_l0_typo,validators_l1_math,validators_l2}.ml`, `ml/checkpoints_v2/{best_model.pt,eval_results.json}`, `proofs/{PdflatexModel,BodyTokenFrontEnd,CompileGuaranteeBridge,LanguageContract,LexerFaithfulStep,FaithfulWS8Bridge}.v`, `proofs/ML/SpanExtractorSound.v`, `scripts/tools/{diff_compile_check.sh,check_producer_coverage.py,check_roadmap_facts.py}`; memory: `MEMORY.md`, `compile_prediction_priority.md`, `realtime_readiness_track.md`, `lp_extension_measurement.md`, `compile_blocking_promotion_finding.md`, `producer_coverage_gate.md`, `coq_nat_pow_qed_blowup.md`, `feedback_squash_merge_drops_late_commits.md`, `v27_faithful_status.md`, `fix_output_safety.md`, `bucketB_sentence_pilot.md`. Canonical numbers this session: version 27.1.60 (tree; tags v27.1.58/59 on origin/main; v27.1.60 = PR #498 green); producers 167 SETTLED; candidates 124; proof files 178 (63 core + 114 generated + 1 ML) + 7 archived; theorems 1543; per-rule soundness 643; 0 Admitted / 0 Axiom; LP-Core 38.9%; 65-doc differential matrix = 35 true-READY / 20 true-NOT-READY / 8 false-READY / 2 false-NOT-READY; false-READY allowlist = 8.*
