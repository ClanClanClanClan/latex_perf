# LaTeX Perfectionist — Master Roadmap (v2)

> **Status:** authoritative planning document (single source of truth for the compile-guarantee **and** policy-enforcement program). v2 folds in the adversarial strategy audit + the sharpened positioning. Grounded synthesis of the per-track reconstructions plus the maintainer's project memory, corrected against `governance/project_facts.yaml`, `specs/v27/FIX_PRODUCER_LEDGER.md`, `docs/COMPILATION_GUARANTEE.md`, and the live worktree.
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

The **proof** covers only **LP-Core** — a subset that most real papers do not *fully* live in (measured: **38.9% LP-Core** roots). So the proof is the **trust backbone for segments B and C**, but for segment **A** the daily value is **SPEED + LOCALIZATION + FIX + COVERAGE across ALL documents** (a clearly-labelled proven tier *and* a clearly-labelled heuristic tier). Chasing "prove everything" at the expense of coverage / speed / localization would be strategically wrong.

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
- **LP-Core split (real papers, roots):** **38.9% LP-Core / 60.2% LP-Extended / 0.9% LP-Foreign** (16,193 `.tex`, 6,899 roots). **97.4% of ~96k real `\def` are BENIGN** — the E1 opportunity. **The ~60% LP-Extended majority is the addressable market for H1** (heuristic, non-proven, actionable NOW).

### Honest current scope of the guarantee
`--compile-check` runs **T0 (parse + LP-Foreign classify) + T2 (source closure) + T3 (feature/engine compat) + T4 (aux label uniqueness) + T5 (37 DELIM/ENC/PRT Error rules) + the v27.1.60 structural-fatal gate**, with **T1 (macro expansion) a deliberate conservative no-op**. Scoped to **LP-Core**, **pdflatex only** (see S-ENGINE), for the READY oracle defined in S-ORACLE.

Measured soundness residual on the **65-doc differential confusion matrix** (v27.1.60, `diff_compile_check.sh` at scale, pdfTeX / TeX Live 2026):
- **35 true-READY / 20 true-NOT-READY / 8 false-READY / 2 false-NOT-READY** (total 65).
- The v27.1.60 structural-fatal gate closed the prior **10 → 8** false-READY residual — `fail_double_subscript` and `fail_no_documentclass` are now correctly NOT-READY (and `fail_missing_begin_document` is caught by T0, so it is not a false-READY either — a stale allowlist entry to prune).

All **8** residual false-READYs need macro/package-universe modelling or full expansion (0 new beyond the documented `KNOWN_FALSE_READY` allowlist, whose 8 real entries ARE this count), and the gate holds **0 over-rejection on the scanned real-root corpus**. See `docs/COMPILATION_GUARANTEE.md` for the enumerated residual.

---

## 3. Tracks

Tracks: **S** (verdict soundness), **S0/S-ENGINE/S-ORACLE/SEC/H-BACKSTOP** (verification infrastructure & scope), **V / V-CAT / V-TRUSTED-BASE** (formal verification), **R** (real-time serving), **E** (subset extension), **H** (heuristic tier), **P** (policy / rule engine), **C** (rules / candidate coverage). Effort scale S/M/L/XL. **Every S/E detector-adding item and every R item carries the standing performance-budget clause (Principle 9).**

### Track S — Verdict Soundness

**Rationale.** Directly serves the cardinal promise: eliminate every false-READY, over the widest possible sound subset, without introducing over-rejection.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **S0** | **Verification infrastructure (NEAR-TERM BLOCKER)** | NOT STARTED | M | local pdflatex | **Commit `bench_classify` + `ampfuzz` + a hash-manifested, redistributable over-rejection corpus** (kill the untracked-scratch dependency, R-corpus). **Wire `diff_compile_check.sh` into the release gate** — hard-fail on any NEW false-READY where pdflatex is present. **Pin + assert `pdflatex --version`** (engine + TeX-Live year). **Emit the confusion matrix as committed machine-readable JSON.** This blocks credible S2/S4/E-track numbers. Budget clause: harness run bounded + sandboxed (SEC). |
| **S1** | Ship v27.1.60 structural gate to main | IN FLIGHT (`f0f8cbcd`, PR #498 green) | S | green CI + user merge; local `diff_compile_check.sh` | PR merged, tag v27.1.60 pushed; `diff_compile_check.sh` = 8 known / 0 new false-READY; `test_compile_gate.ml` passes; fast==full parity green. **Δ North-Star: closes the `$a^b^c$`-class holes (10→8 false-READY), 0 over-rejection.** |
| **S2** | **GENERATIVE grammar-directed coverage — the STANDING gate (BLOCKING infra)** | PARTIAL (mechanism exists; generator not automated) | L | S0; local pdflatex; `diff_compile_check.sh` | **Enumerate EVERY detector decision-branch × EVERY LP-Core construct class**, including the missing deterministic-FATAL classes: **`\left..\right]` mismatch, extra alignment tab, "Dimension too large", `\verb`-newline, `\end{document}` in an open group**. Generator emits structurally-perturbed LaTeX; report every `cc=READY ∧ pdflatex=FAILS`; each new class fixed OR moved to `KNOWN_FALSE_READY` with written justification; 0 NEW false-READY over ≥N-thousand fuzzed docs. **This is BLOCKING infra that every deterministic-structural item (S3/S5/E-track/every future detector) must pass — it is the standing gate, NOT a leaf.** Local/pre-release (CI has no TeX). |
| **S3** | Misplaced-`&` gate via strict LP-Core scoping | DROPPED, but shippable EARLIER/INDEPENDENTLY of E1 via direction (b) | M | LP-Core classifier; alignment-env stack model; **decoupled from E1 if (b)**; must pass S2 | fires on genuine misplaced `&` in strict LP-Core docs; **0 over-rejection** on the 6,396-paper corpus; differential fixture passing S2. Carving alignment-shortcut `\def` macros into LP-Extended (direction (b)) makes `&` soundly gate-able for strict LP-Core *without* over-rejecting `\def`-alignment papers → S3 is **not** permanently blocked on E1. |
| **S4** | Deepen differential validation vs real pdflatex at scale | PARTIAL (65-doc matrix + 6,396 over-reject pass) | M | **S0 (corpus + JSON matrix)**; local pdflatex | harness over full real-paper tree; confusion matrix published as committed JSON in `COMPILATION_GUARANTEE.md`; 0 NEW false-READY; over-rejection reported per LP-tier and **per engine + TeX-Live year**. **Δ North-Star: turns 35/65 into a reproducible versioned commitment.** |
| **S5** | Finish T0–T5 as TOTAL checks over the real parse | PARTIAL (T1 no-op; T4 aux-gated) | L | catalogue for mode/macro state; `User_macro_registry`; must pass S2 | T1 catches math-only-in-text + illegal `\newcommand` param-count on the 2 residual fixtures without over-rejecting; T4 does source-only duplicate-label detection; documented totality. |

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

### Track V — Formal Verification

**Rationale.** The Coq backbone is what makes READY a *proof*. Close the remaining trusted-layer and re-proof gaps — **but** the audit's key finding is that the real bugs live in the UNPROVEN trusted glue (V-TRUSTED-BASE), which is elevated **above** the abstract re-proof (V4).

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **V1** | Macro/package-universe semantic tier (catalogue modelling) | OUT OF SCOPE, documented | XL | verified base+package macro/env catalogue; kpathsea/file-resolution model | modelled catalogue turns undefined-cs/env + missing-package into correct NOT-READY; **still 0 over-rejection**; residual allowlist shrinks; catalogue proof extended. **Governed by V-CAT contracts.** |
| **V2** | Prove all ~660 rules to Coq soundness | PARTIAL (parametric scaffold + 114 generated family files) | XL | `T5_concrete.v` instantiation; generator completeness | `Generated.Catalogue` covers all 660 ids with per-rule Qed soundness; `pdflatex_T5_safe_holds` instantiated; Print Assumptions Closed. |
| **V3** | Byte-level certification of `detect` / `Parser_l2` / range-oracle for LP-Core | PARTIAL (`detect` cert-by-test; `Parser_l2` unverified; range oracle trusted) | XL | LP-Core grammar spec | `Parser_l2` proven sound/complete for LP-Core; `detect` completeness proven OR differential battery formalized; range oracle proven OR trust boundary explicitly bounded. **Overlaps V-TRUSTED-BASE.** |
| **V4** | Tier-3 Stage-6 re-proof | **ADR-ACCEPT-THE-BRIDGE (default) — DE-PRIORITIZED below all coverage/utility work** | L (RISKY) | maintainer sign-off | **DECISION REVERSED from the earlier "re-prove `PdflatexModel.v`".** The bridge is byte-identical / **zero verdict change** and re-proving a proven capstone is real risk for no measured gain. **Default = ADR accepting the additive bridge** + rewrite acceptance #6. **Re-prove ONLY if a concrete abstract-vs-faithful divergence is found** (e.g. surfaced by S2 or HB1). |

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

### Track R — Real-Time Serving

**Rationale.** Deliver the sound verdict **as the user types** — the segment-A wedge (Section 0, clause 1). The correctness plane is fine; this is the latency/interactivity plane. **Standing performance-budget clause applies to every R item.**

**Measured baseline** (user's real papers, warm binary, local disk, v27.1.57): `--compile-check` = **0.10s @ 4KB / 1.5s @ 30KB / 2.6–4.8s @ 80KB / 13.7s @ 316KB** (full lint alone = 10.0s @ 316KB). **13.7s is "unusable" as-you-type** — R1 already fixes the 4–74KB band; 316KB is the R4 tail.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **R1** | Fast compile-readiness kernel | **SHIPPED** (v27.1.59) | — | — | parse-once + compile-blocking rules; fast==full over 473+150 docs → 0 divergences; sub-150ms to ~74KB (NOT at 316KB — that gap = R4). |
| **R3a** | Enrich T5 reason to carry byte offsets | NOT STARTED (trivial standalone unblock; independent of R2) | S | — | `T5_rule_violations` carries offsets from `Validators.result` spans (`compile_contract.{ml,mli}`) so squiggles can be placed. |
| **R2** | Persistent service `POST /compile-check` + CLI `--watch` | NOT STARTED | M | R1 (done); **cross-request PURE-CACHE contract** | endpoint returns SAME verdict as `--compile-check` on parity corpus; registry + per-file context warmed once; warm latency excludes startup (~62ms@50KB); `--watch` re-checks without re-spawning. **Rides the v25/v26 keystroke-service heritage** (`main_service`, `broker`, EDF scheduler, `hedge_timer`, REST `rest_api_server`). **Must call the in-process kernel, NOT the SIMD socket.** **PURE-CACHE contract: any cross-request cache is a pure function of source (per-run-cleared `*_context`), so a warm verdict is byte-identical to a cold one** (guards R4 too). |
| **R3** | LSP server (didChange → debounced fast kernel → publishDiagnostics) | NOT STARTED | M–L | **R3a (hard dep, offsets)**; R2 preferred | VS Code squiggle at correct byte range for `$a^b^c$`/unclosed `\begin`/missing `\documentclass`, clears on fix, updates within debounce; diagnostics == `--compile-check`; sub-150ms on ≤74KB. |
| **R4** | Incremental DELIM/ENC rules (sub-150ms on large docs) | NOT STARTED (substrate exists, unwired) | XL | R2/R3; incremental substrate + a parity gate; **PURE-CACHE contract (R2)** | **⚠ THE ONE real-time item where soundness DIRECTLY CONFLICTS with latency.** DELIM nesting is **whole-doc stateful** → chunk-local rescan can miss whole-document nesting → an **UNSOUND false-READY**. **⚠ ALPHABET SCOPE (D3):** chunk-local rescan is unsound over a **POST-EXPANSION alphabet** once E1/D1 admits `\def\bea{\begin{align}}` (a local chunk can't know an earlier `\def` opened an environment) → **scope R4 to PRE-EXPANSION source-structural rules ONLY, or park it.** Deferrable indefinitely while the target holds for ≤74KB; if built it MUST pass a whole-doc parity gate (incremental verdict == whole-doc across a fuzzed edit stream). |

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
| **E5** | Package-contract catalogue (top packages by frequency) | PARTIAL (`extension_registry.ml`: 5 built-ins + `evaluate`/`over_claims`, not ranked/wired) | L | none hard; most valuable after E1–E3; VC1 (version/staleness contract) | rank `\usepackage` frequency on 16k corpus, add top-N with risk/support ≤ `max_support_for_risk`; wire into classifier; `over_claims=false` per entry; **catalogue-staleness contract (VC1) enforced.** |

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

### Track C — Rules / Candidate Coverage (rule-authoring mechanics feeding Track P)

**Rationale.** Complete the "every fixable rule has a fix-or-candidate" DoD; this is the *authoring/coverage* substrate that Track P productizes. **Cadence: ≥10 new Bucket-A producers per patch release** (`FIX_PRODUCER_LEDGER.md:781`; Bucket A = 466 rules, 167 shipped, 299 pending).

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

### A. Deterministic-structural — closeable now (soundly, each must pass the S2 generative fuzz gate)
- **S0** (infra — BLOCKER), **S1** (ship v27.1.60), **S2** (the standing generative gate itself), **S3** (misplaced-`&`, shippable independently via (b)), **S5-T4** (source-only duplicate-label), **SO1** (READY oracle definition).
- **R2, R3, R3a** (serving/offset enrichment — engineering, not modelling). **R4** is deterministic-structural but its chunk-local incrementalization is the one soundness-vs-latency conflict (see B/notes, **alphabet-scoped** to pre-expansion).
- **E2, E3, E4** (balanced-span / branch-union / constant-fold — statically decidable), governed by V-CAT.
- **P1, P2, P3** (policy/template enforcement — deterministic checks over the verified parse).
- **C-KR1, C-COV1, C-WS1, C-DOD1, C-DR1, C-FD1** (candidate/pilot wiring, doc, byte-level detection).

### B. Semantic / macro-universe — needs a modelled catalogue (bounded but heavy)
- **V1** (macro/package-universe tier — the 8 residual false-READYs), **V2** (660-rule Coq soundness), **V3** (byte-level cert of `detect`/`Parser_l2`/range-oracle), **V-CAT** (admission contracts), **V-TRUSTED-BASE** (glue certification — elevated).
- **S5-T1** (bounded-expansion probe), **SE1** (multi-engine capstones — option A).
- **E1a + E1** (make `\def` visible, then admit benign defs — the coverage jump; the E1/S3 coupling lives here).
- **E5** (package-contract catalogue).
- **R4-statefulness** (whole-doc delimiter nesting — the soundness half of R4).

### H. Heuristic (deliberately non-proven, inverted contract) — its OWN class
- **H1** — the *labelled* likely-compiles tier. Reuses V1's undefined-cs / package modelling, but inverted contract, rendered separately from proof. **Decoupled from E1 → pullable near-term.** A fully-modelled catalogue can promote *parts* of H1 into the proven tier (V1); H1 itself is never a proof.

### C. Impossible-by-design — excluded from the guarantee
- **Full-LaTeX total compile-decision** (Turing-complete ⇒ undecidable). Anything needing `\write18`/`\catcode`/dynamic `\csname`/runtime-conditional expansion → LP-Foreign → NOT-READY or H1, never proof.

### D. Parked-by-decision
- **WS10 / WS11** (ADR-010). **C-NLP1** (deferred until product funds an NLP/dictionary substrate).

---

## 5. Sequenced Roadmap

### Hardening closed THIS PR (#498)
- **bail ⇒ demote** — the 4096-frame double-script bail now demotes to NOT-READY (was conservative toward false-READY). **DONE.**
- **`is_compile_blocking` single-source** — removed the duplicate prefix-only shadow in `compile_contract.ml`; **single source of truth is `Validators.is_compile_blocking`.** **DONE.**
- **Roadmap fact-checker** (`scripts/tools/check_roadmap_facts.py`) — anti-drift gate on every load-bearing number. **DONE.**

### Near-term (RESEQUENCED — infra & reproducibility FIRST)
1. **S0 — verification infrastructure + reproducible full-corpus numbers FIRST.** Commit `bench_classify`/`ampfuzz`/the hash-manifested over-rejection corpus; wire `diff_compile_check.sh` into the release gate (hard-fail on new false-READY where pdflatex present); pin+assert `pdflatex --version`; emit the confusion matrix as committed JSON. **Everything downstream (credible S2/S4/E numbers) depends on this.** *(Effort M; needs local pdflatex.)* **Δ North-Star: makes the metric reproducible/version-controlled.**
2. **S1 — ship v27.1.60 to main** (with the bail⇒demote fix now DONE). Closes the `$a^b^c$`-class holes (**10 → 8**), **0 measured over-rejection**. Merge → tag → `diff_compile_check.sh` = 8 known / 0 new. *(Effort S; only user merge pending.)*
3. **S2 — the GENERATIVE grammar-directed fuzz gate as BLOCKING infra.** Enumerate every detector decision-branch × LP-Core construct class (incl. the missing FATAL classes: `\left..\right]` mismatch, extra alignment tab, "Dimension too large", `\verb`-newline, `\end{document}` in an open group). **This gate must be standing before any S3/S5/E-track detector work.** *(Effort L.)*
4. **H1 (minimal, near-term, DECOUPLED from E1)** — undefined-cs dictionary + brace/`$`/env balance → a clearly-labelled LIKELY tier for the ~60% LP-Extended majority. Its signals are independent of `\def` admission; the v2 span-extractor ML substrate (F1=0.9799) already exists. **Gives segment A an actionable verdict NOW** without waiting on E1. *(Effort M–L; UI/API-separated from proof.)*
5. **C-DR1 + C-DOD1 — doc & DoD hygiene.** Document the **settled 167** decomposition + cross-ref the two ledgers (drop the phantom "596"); close **DE-006/ENC-006** (BIB-010 already shipped). *(Effort S then S–M.)*
6. **R3a → R2 — offsets, then the persistent endpoint** (R3a is a trivial standalone unblock, independent of R2). *(Effort S then M.)*

### Medium-term
- **S4 — full 6,899-paper differential** over the S0 corpus; publish the versioned confusion matrix (per LP-tier, per engine/year).
- **E1a → E1 — make `\def` visible, then benign-`\def`/`\let` admission** — the single biggest proven-coverage jump (~+18–25pp). **Coupled with S3:** resolve the `\def\bea{\begin{eqnarray}}` boundary via **direction (a)** (model alignment-shortcut expansion) OR **(b)** (carve those defs into LP-Extended → S3 ships independently first). Governed by **V-CAT** (re-derive `find_math_ranges` if any admitted def opens math).
- **R3 — LSP server** (hard dep: R3a; R2 preferred) — the product surface for the traffic-light.
- **P1 → P2 — policy/template enforcement** — the segment-B monetizable surface, on the frozen WS9/WS12 seams + R3a localization.
- **SE1 — resolve multi-engine scope** (option A capstones OR option B ADR + delete the alias claim).
- **E2 → E3** — scoped `\makeatletter`, then static conditionals.
- **C-KR1 → C-WS1 → C-COV1** — wire the 5 known-recoverable rules, graduate the whitespace pilot rules, then the tail.

### Long-term
- **V-TRUSTED-BASE (VT1→VT2→VT3)** — trusted-glue ledger, per-detector mutation testing, certify `double_script_fatal`/`find_math_ranges` as a refinement. **Elevated above V4** (the real bugs live here).
- **V1 — macro/package-universe semantic tier** (XL) — the dominant 8-doc residual; decide vs. leaving it to H1 (Q-V1).
- **V2 — all-660 Coq soundness.** **V4 — DE-PRIORITIZED** (ADR-accept the bridge unless S2/HB1 surfaces a concrete divergence).
- **E5 → E4** — package catalogue (parallelizable), then `\csname`/`\expandafter` (lowest value, last).
- **SEC1 / HB1** — sandbox the substrate; optional pdflatex backstop (feeds S2).
- **R4 — incremental DELIM/ENC** — only if the size SLA demands sub-150ms on 316KB, **alphabet-scoped to pre-expansion source-structural rules**, under a whole-doc parity gate. Deferrable indefinitely.
- **WS10/WS11** — only on a product decision (ADR-010).

### Cross-track dependency map
- **S0 gates credible S2/S4/E numbers** — infra first.
- **S2 (generative gate) is BLOCKING infra for S3 / S5 / E-track / every future detector** — not a leaf.
- **H1 is DECOUPLED from E1** (signals independent of `\def` admission) → pullable near-term; overlaps V1's undefined-cs class; stays rendered separately from proof.
- **E1a (make `\def` visible) precedes E1**; **S3 (misplaced-`&`) ⇄ E1** share the `\def`/alignment boundary — direction (b) DECOUPLES them so S3 ships first.
- **Every E admission ⇒ a V-CAT contract** (MATH-OPEN re-derivation, ABSENCE, CATALOGUE version/staleness).
- **R3-LSP ⇒ R3a (offsets, hard) + R2 (warm state, preferred)**; R2/R4 ride the **PURE-CACHE contract**; **R4 alphabet-scoped to pre-expansion** + whole-doc parity gate.
- **P1/P2 ⇒ frozen WS9/WS12 seams + R3a localization + the LP-Core trust backbone.**
- **SE1 (multi-engine) parameterizes the North-Star promise by engine + TeX-Live year.**
- **C-FD1 ⇒ v27.1.58 front-end** (landed).

---

## 6. Open Decisions & Risks

### Open decisions (need a call / sign-off)
- **Q-STRATEGY (the framing question):** is the flagship the **proven compile-verdict** or the **one-engine diagnose + fix + policy product**? **Recommendation: the latter framing** — one verified document-understanding engine (compile-prediction + policy-enforcement + localization + fix + trust), with the proof as the trust backbone for segments B/C, not the whole pitch (Section 0).
- **Q-ENGINE (S-ENGINE):** multi-engine scope — **(A)** real per-engine capstones + differential + `engine`-through-`of_root` + engine/year-parameterized promise, or **(B)** ADR scope to pdflatex-only + DELETE the xe/lua alias-as-guarantee claim + demote non-pdflatex to NOT-READY/heuristic. **Resolve before any multi-engine READY is emitted** (invisible false-READY risk today).
- **Q-BACKSTOP (H-BACKSTOP):** ship `--compile-check --confirm-with-pdflatex` (downgrade-on-disagree + feed S2)? Value: self-improving oracle + trust escape-hatch for segment C. Needs SEC1.
- **Q-S3/E1 (the coupling):** where does `\def\bea{\begin{eqnarray}}` land? **(a)** admit E1 → the `&` gate models alignment-shortcut expansion; or **(b)** carve alignment-shortcut defs into LP-Extended (S3 ships independently for strict LP-Core). Resolve before E1 admits alignment-macro defs.
- **Q-E1 granularity:** admit a benign `\def` **per-instance** (permissive, forces the `&` coupling) or **per-document** (whole def-set benign-and-acyclic — 62.2% of def-demoted docs; simpler to prove)?
- **Q-V1:** build the macro/package semantic tier (XL, still not a *total* certificate) or accept the 8-doc residual permanently and invest in H1 instead?
- **Q-V4:** **default = ADR-accept the additive bridge (DE-PRIORITIZED).** Re-prove `PdflatexModel.v` **only** if S2/HB1 surfaces a concrete abstract-vs-faithful divergence.
- **Q-H1/V1 boundary:** one modelled undefined-cs catalogue serving BOTH tiers, or two mechanisms? (H1 output stays UI/API-separated from proof either way.)
- **Q-E5 authority:** are built-in package contracts *authoritative for compile-check* (→ proven tier) or advisory-only (→ H1), and under what version/option/year staleness contract (VC1)?
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

*Sources: `docs/COMPILATION_GUARANTEE.md`, `governance/project_facts.yaml`, `specs/v27/{FIX_PRODUCER_LEDGER,CANDIDATE_BACKLOG}.md`, `specs/rules/{rules_v3,rule_contracts}.yaml`, `docs/archive/RULES_PILOT_TODO.md`, `docs/v27/adr/ADR-010-*.md`, `latex-parse/src/{compile_contract,compile_gate_checks,validators,language_profile,unsupported_feature,user_macro_registry,extension_contract,extension_registry,compile_evidence,validators_l0_typo,validators_l1_math,validators_l2}.ml`, `ml/checkpoints_v2/{best_model.pt,eval_results.json}`, `proofs/{PdflatexModel,BodyTokenFrontEnd,CompileGuaranteeBridge,LanguageContract,LexerFaithfulStep,FaithfulWS8Bridge}.v`, `proofs/ML/SpanExtractorSound.v`, `scripts/tools/{diff_compile_check.sh,check_producer_coverage.py,check_roadmap_facts.py}`; memory: `MEMORY.md`, `compile_prediction_priority.md`, `realtime_readiness_track.md`, `lp_extension_measurement.md`, `compile_blocking_promotion_finding.md`, `producer_coverage_gate.md`, `coq_nat_pow_qed_blowup.md`, `feedback_squash_merge_drops_late_commits.md`, `v27_faithful_status.md`, `fix_output_safety.md`, `bucketB_sentence_pilot.md`. Canonical numbers this session: version 27.1.60 (tree; tags v27.1.58/59 on origin/main; v27.1.60 = PR #498 green); producers 167 SETTLED; candidates 124; proof files 178 (63 core + 114 generated + 1 ML) + 7 archived; theorems 1543; per-rule soundness 643; 0 Admitted / 0 Axiom; LP-Core 38.9%; 65-doc differential matrix = 35 true-READY / 20 true-NOT-READY / 8 false-READY / 2 false-NOT-READY; false-READY allowlist = 8.*
