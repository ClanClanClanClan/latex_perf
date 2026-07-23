# LaTeX Perfectionist — Master Roadmap

> **Status:** authoritative planning document (single source of truth for the compile-guarantee program). Grounded synthesis of four per-track reconstructions plus the maintainer's project memory notes, corrected against `governance/project_facts.yaml`, `specs/v27/FIX_PRODUCER_LEDGER.md`, `docs/COMPILATION_GUARANTEE.md`, and the live worktree.
> **Version-of-record:** `dune-project` = **v27.1.57** on the checked-out tree; HEAD `36b1dc3c` (#495). Tags **`v27.1.58` and `v27.1.59` are tagged on `origin/main`** (both real, pushed). **v27.1.60 is IN FLIGHT** on worktree branch `feat/v27160-sound-compile-gate` (`f0f8cbcd`, `/private/tmp/wt-sound`) — **not yet tagged/merged**.
> **Merge model:** user merges each green PR; I tag. Serialize version bumps (label-conflict/rebase hell otherwise). CI flakes to auto-rerun: rust-proxy, format, xxh-selfcheck, schema (rest-schema ~15min).

---

## 1. North Star & Principles

### The core promise
> **A LaTeX document COMPILES if and only if our verified parser says it will (READY) — as long as it stays within the non-Turing-complete decidable subset (LP-Core, expandable).**

Delivered (1) with **verdict SOUNDNESS**, (2) in **REAL-TIME** as-you-type, (3) over the **WIDEST decidable subset** we can prove, (4) with a **clearly-labelled HEURISTIC tier** for the rest — all on a **FORMALLY-VERIFIED (Coq)** backbone.

### Principles (non-negotiable)

1. **SOUNDNESS IS PARAMOUNT.** The cardinal bug is a **false-READY**: we certify "provably compiles", pdflatex fails (e.g. `$a^b^c$`). It breaks the guarantee. A **false-NOT-READY** (over-rejection) is merely conservative and acceptable. Every design choice resolves ties toward NOT-READY. **Exception to watch:** the double-script detector's fixed 4096-frame array "bails safely" on extreme nesting — a bail is conservative toward false-READY (the dangerous direction), so it is a monitored risk, not a free pass.

2. **Precise dedicated compile-gate detectors OVER advisory-lint-rule promotion.** Promoting the ~641 lint rules to compile gates was **TRIED and ABANDONED** — they over-reject real compiling papers (MATH-047: 34/44; MATH-077/PKG-004 comment/verbatim-blind; CMD-016 ignores `\renewcommand` order). Root insight: *advisory linting ≠ compile-gate precision.* Any subset-widening must be a **dedicated precise detector, differentially fuzzed vs real pdflatex** (`compile_blocking_promotion_finding.md`).

3. **Differential-fuzz-vs-real-pdflatex is the STANDING gate, not a one-off.** Soundness confidence comes from running BOTH `--compile-check` and real `pdflatex`, building a confusion matrix, and failing **only on a NEW false-READY** outside the documented `KNOWN_FALSE_READY` allowlist (`scripts/tools/diff_compile_check.sh`). **Every deterministic-structural item (S3, S5, future detectors, the whole E-track) must pass this gate before shipping.** Hard external dependency: it needs **local pdflatex** — CI has no TeX — so it is a **local / pre-release gate**, run before every gate-touching release.

4. **Honest-scope docs.** READY = "no runtime precondition we check is violated + the extracted project passes the proven premise-check", **NOT** "your exact bytes are certified to compile" (`docs/COMPILATION_GUARANTEE.md`). `--compile-check` is an honest **fail-first readiness pre-check**, not a total compile certificate. LaTeX is Turing-complete ⇒ a total compile-decision is **provably impossible**; we only claim decidability over LP-Core.

5. **The LP-Core / LP-Extended / LP-Foreign boundary** is the citable scope of the guarantee. It is a **total, deterministic, Coq-proven** classifier (`classify_lp_core_sound`, Qed, 0 admits). "Latex-epsilon" = LP-Core.

6. **The over-rejection real-paper safety scan (found-and-fixed, not a clean sheet).** Any new gate must show **0 over-rejection** on the user's real-paper corpus (**6,396–6,899 compiling root papers**, free ground truth). Honest history: the v27.1.60 double-script detector's precision scan (1,218 real published papers) initially produced **4 false-NOT-READY regressions on genuinely-compiling papers** — all confirmed compiling by pdflatex, all **FIXED** (commit `b3bf23f1`: compute `find_math_ranges` on a comment/verbatim/url-BLANKED copy so a commented unbalanced `$$`/`$` can't spill a fake math range; plus a `\ref`-alias moving-arg skip so user `\newcommand`/`\def` label-key macros aren't misread as double subscripts). **Final state: 0 over-rejection on the scanned corpus** — the number is earned, not assumed. (The structural `&` gate was separately dropped precisely because it over-rejected **107 real roots**.)

7. **fast == full parity.** The fast readiness kernel must be **verdict-identical** to the full path (`test_fast_readiness_parity.ml`, wired into `runtest`, 473 corpus + 150 real papers → 0 divergences). The v27.1.60 structural gate is a **pure function of source** ⇒ fast==full trivially.

### Hard-won safety guardrails (each cost a real bug — do not relearn)

- **Control-word-glue corruption.** A fix that emits a *bare* control word (`·`→`\cdot`, `÷`→`\div`, `->`→`\rightarrow`, …) yields `$a\cdotb$` — an **undefined control word / compile error** — when the next source byte is a letter. It passed **every** idempotence / valid-UTF-8 / convergence gate; only *output inspection* caught it. Mitigated by `Validators_common.control_word_repl` (append a space iff the next byte is an ASCII letter) and the permanent multi-variant `scripts/tools/check_producer_coverage.py` gate. **Any fix emitting a control word MUST be tested with letter-adjacency.**
- **The 46% producer-coverage gap.** **69 of 150 producers (~46%) were NEVER corpus-triggered** — so "differential 0-diff + convergence" is *not* full-surface safety; it only exercises producers whose trigger appears in the corpus AND its mode. `check_producer_coverage.py` now applies EVERY `produces_fix:true` rule to a registered adversarial trigger (`specs/v27/producer_triggers.json`), asserting applied + valid-UTF-8 + idempotent + golden-match.
- **Offset-on-length-changing-transform corruption (STYLE-033).** Match the **ORIGINAL** source; never emit edits at offsets computed on a length-changing transform (e.g. `strip_comments` shrinks the string → deletes land mid-UTF-8-char → invalid bytes). Prose-changing rules are **candidates, never auto-fixes** (SPC-018).
- **Coq nat-pow Qed-blowup.** A Peano-`nat` `2^k` constant (FNV masks) forces the kernel to reduce `2^30` to a ~10⁹-unary numeral at `Qed` → multi-minute hang (bit v27.1.58). Fixed by peeling the recursion with an **abstract opaque `fold_left_cons_eq` rewrite**, NOT `cbn`/`simpl`/`reflexivity` on the concrete term (`coq_nat_pow_qed_blowup.md`). `set`/`clearbody`/isolating `nia` all fail — the concrete power is re-substituted at the kernel boundary.
- **Squash-merge drops late commits / stacked-PR trap.** A squash-merge of a base PR strands commits that landed on its branch after the squash point (v27.1.5 = 11 producers were stranded, **recovered via cherry-pick**). Serialize; never stack a PR into a branch you intend to squash without a recovery plan (`feedback_squash_merge_drops_late_commits.md`).

### Operational notes
- **External-worktree discipline:** file-editing agents MUST use `isolation:'worktree'` branched from **main** (not a feature branch, or they duplicate unmerged infra). Verify agents must inspect the **build's** worktree (`path_match`), not the main tree.
- **Dropbox CloudStorage FS is pathologically slow** for git — use partial commits `git commit -- <pathspec>`; clear stale `.git/index.lock`.

---

## 2. Where We Are

### Shipped milestones (compile-readiness flagship)

| Version | Delivered | Grounding |
|---|---|---|
| **v27.1.53** (#490) | `--compile-check` READY/NOT-READY verdict; T0/T5 de-stubbed | `validators_cli.ml`, `dab9673e` |
| **v27.1.54–56** | Premise-decision bridge **extracted + executed**: `project_wf_dec` decides T2/T3/T4; `project_wf_dec_compile_safe` (Qed, Closed); hand mirror removed → MODEL-CONNECTED | `proofs/CompileGuaranteeBridge.v`, `docs/COMPILATION_GUARANTEE.md` |
| **v27.1.57** (#495) | **LP-Core subset boundary certified** — tier DECISION is Coq-extracted `LanguageContract.classify` governed by `classify_lp_core_sound` (Qed); only `Unsupported_feature.detect` stays trusted (adversarially certified) | HEAD `36b1dc3c` |
| **v27.1.58** (#496) | **Verified bytes→body_token front-end** — Coq-modelled, Qed-proved, 0-admit/0-axiom scanners, extracted + executed at runtime; capstone `compile_safe_of_source` (Print Assumptions Closed). (Bit the Coq nat-pow Qed-blowup here; fixed via abstract fold rewrite.) | `proofs/BodyTokenFrontEnd.v`, `body_token_frontend_extracted.ml` |
| **v27.1.59** (#497, **tagged on origin/main**) | **Fast compile-readiness kernel** — `check_ready_to_compile ~fast`: parses **once**, runs only the **37 compile-blocking rules** (`DELIM-`/`ENC-`/`PRT-`) not ~641; verdict-identical to full path on 623 docs; parity gate wired | `compile_contract.ml`, tag `v27.1.59` |
| **v27.1.60** (**IN FLIGHT**, `f0f8cbcd`) | **Precise structural-fatal compile-gate** (`compile_gate_checks.ml`, **632 lines**): comment/verbatim/context-aware detectors firing **iff pdflatex genuinely fails** — (1) double super/subscript in math, (2) no `\documentclass`, (3) `\usepackage` after `\begin{document}`. Pure function of source ⇒ byte-identical fast/full. **Misplaced-`&` DELIBERATELY DROPPED** (over-rejected 107 real roots). Precision-scan regressions found-and-fixed (`b3bf23f1`). | `feat/v27160-sound-compile-gate` |

### Formal backbone state (Coq)
- **176 proof files total** = **61 core + 114 generated + 1 ML + 7 archived** (`governance/project_facts.yaml`). **NO `Admitted`, NO `Axiom`** in active proofs (only archived `.disabled` files carry them).
- **Capstone** `PdflatexModel.pdflatex_compile_safe` — **Qed, unconditional, Print Assumptions Closed**; `xelatex`/`lualatex` aliases are the same proof object.
- Front-end gap #1 **CLOSED** (v27.1.58); premise bridge **extracted+executed** (v27.1.54-56); LP-Core boundary **certified** (v27.1.57).
- **Faithful pdflatex semantics** (Tier-3, v27.1.29-32): `LexerFaithfulStep.v` + `FaithfulWS8Bridge.v` — tokenize/aux/log/pass, ≤2-pass convergence with tight bound; all Qed, Closed. **⚠ shipped ADDITIVELY** (bridge, capstone byte-identical) — NOT the plan's re-proof (see V4).
- **ML span-extractor asset:** `proofs/ML/SpanExtractorSound.v` proves `v2_span_extractor_sound` (Qed) over the trained v2 byte-classifier `ml/checkpoints_v2/best_model.pt` (**F1=0.9799, precision 0.975, recall 0.9849**), covering 8 ambiguous TYPO rules — prior art / substrate for Track H and the NLP-deferred rules.
- **T5 catalogue scaffold:** parametric `rule_passes` + **114 generated per-family proof files**.
- `theorem_count_reported: 1484`; `per_rule_soundness_count: 643`.

### Coverage numbers
- **Rule catalogue:** 660 total / 17 reserved / **643 non-reserved / 643 shipped** (`governance/project_facts.yaml`, internally consistent).
- **Fix producers (Bucket A):** **167 (~25%) — SETTLED, authoritative** (`FIX_PRODUCER_LEDGER.md`, `SHIPPED_VERSIONS`). Decomposition: 70 (L1+ via `mk_result_with_fix`) + 47 (L0 via `with_fix`/`fix_of`) + the remainder across families. **Bucket A = 466 rules; 167 shipped / 299 pending.** **⚠ Do NOT "correct" 167 down to 70** — the 70-count is only the `_with_fix_exempt`-grep subset (verbatim-hardened L1+); it is not the producer total (see C-DR1). **Standing cadence commitment:** ≥10 new Bucket-A producers per patch release (`FIX_PRODUCER_LEDGER.md:781`) — actual recent cadence has been ~1/patch (audit-depth over throughput).
- **Review-only candidates (Bucket C):** **124** distinct rule-ids (`mk_result_with_candidates`, matches backlog header).
- **Diagnose-only:** 402 (family-partitioned; "rest non-candidate-able" is a per-family assertion, not individually re-audited).
- **LP-Core split (real papers, roots):** **38.9% LP-Core / 60.2% LP-Extended / 0.9% LP-Foreign** (16,193 `.tex`, 6,899 roots). **97.4% of ~96k real `\def` are BENIGN.**

### Honest current scope of the guarantee
`--compile-check` runs **T0 (parse + LP-Foreign classify) + T2 (source closure) + T3 (feature/engine compat) + T4 (aux label uniqueness) + T5 (37 DELIM/ENC/PRT Error rules) + the v27.1.60 structural-fatal gate**, with **T1 (macro expansion) a deliberate conservative no-op**. Scoped to **LP-Core**.

Measured soundness residual on the **61-doc differential confusion matrix**, stated per-tree:
- **On `main` (v27.1.57):** **33 true-READY / 16 true-NOT-READY / 10 false-READY / 2 false-NOT-READY** (total 61).
- **With v27.1.60 IN FLIGHT (`f0f8cbcd`):** the structural gate closes **2 → 8 false-READY** — `fail_double_subscript` and `fail_no_documentclass` are now correctly NOT-READY.

All residual false-READYs need macro/package-universe modelling or full expansion (0 new beyond the documented `KNOWN_FALSE_READY` allowlist), and the gate holds **0 over-rejection on the scanned real-root corpus** (after the found-and-fixed precision regressions above).

---

## 3. Tracks

Six tracks: **S** (verdict soundness), **V** (formal verification), **R** (real-time serving), **E** (subset extension), **H** (heuristic tier), **C** (rules/candidate coverage). Effort scale S/M/L/XL.

### Track S — Verdict Soundness

**Rationale.** Directly serves the cardinal promise: eliminate every false-READY, over the widest possible sound subset, without introducing over-rejection.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **S1** | Ship v27.1.60 structural gate to main | IN FLIGHT (`f0f8cbcd`) | S | green CI + user merge; local `diff_compile_check.sh` (needs pdflatex) | PR merged, tag v27.1.60 pushed; `diff_compile_check.sh` = 8 known / 0 new false-READY; `test_compile_gate.ml` passes; fast==full parity green |
| **S2** | The STANDING differential-fuzz gate: systematically enumerate ALL structural false-READYs | PARTIAL — the mechanism exists (`diff_compile_check.sh`), automate the generator; only manual `ampfuzz/` scratch so far | L | **local** pdflatex runner; `diff_compile_check.sh` harness | generator emits structurally-perturbed LaTeX, reports every `cc=READY ∧ pdflatex=FAILS`; each new class fixed OR moved to `KNOWN_FALSE_READY` with written justification; 0 NEW false-READY over ≥N-thousand fuzzed docs. **This is the gate S3/S5/E-track must pass — run locally / pre-release, CI has no TeX.** |
| **S3** | Misplaced-`&` gate via strict LP-Core scoping | DROPPED (`compile_gate_checks.ml`), but **can ship EARLIER and INDEPENDENTLY of E1 via direction (b)** | M | LP-Core classifier (shipped); alignment-env stack model; **decoupled from E1 if (b)** | fires on genuine misplaced `&` in strict LP-Core docs; **0 over-rejection** on the 6,396-paper corpus; differential fixture added and passing S2. If we **carve alignment-shortcut `\def` macros into LP-Extended** (direction (b)), then `&` is soundly gate-able for strict LP-Core *without* over-rejecting `\def`-alignment papers — so S3 is **not** permanently blocked on E1. |
| **S4** | Deepen differential validation vs real pdflatex at scale | PARTIAL (61-doc matrix + 6,396 over-reject pass) | M | user's 6,899 compiling root papers; **local** pdflatex | harness run over full real-paper tree; confusion matrix published in `COMPILATION_GUARANTEE.md`; 0 NEW false-READY; over-rejection rate reported per LP-tier |
| **S5** | Finish T0–T5 as TOTAL checks over the real parse | PARTIAL (T1 no-op; T4 aux-gated) | L | catalogue for mode/macro state; `User_macro_registry` (exists); must pass S2 | T1 catches math-only-in-text + illegal `\newcommand` param-count on the 2 residual fixtures without over-rejecting; T4 does source-only duplicate-label detection; documented which totality holds |

### Track V — Formal Verification

**Rationale.** The Coq backbone is what makes READY a *proof*, not a heuristic. Close the remaining trusted-layer and re-proof gaps.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **V1** | Macro/package-universe semantic tier (catalogue modelling) | OUT OF SCOPE, documented | XL | verified base+package macro/env catalogue; kpathsea/file-resolution model | modelled catalogue turns undefined-cs/env + missing-package into correct NOT-READY; **still 0 over-rejection**; residual allowlist shrinks; `LanguageContract`/catalogue proof extended |
| **V2** | Prove all ~660 rules to Coq soundness | PARTIAL (parametric scaffold + 114 generated family files) | XL | `T5_concrete.v` instantiation; generator completeness | `Generated.Catalogue` covers all 660 ids with per-rule Qed soundness; `pdflatex_T5_safe_holds` instantiated; `PdflatexT5Wired.v` derived; Print Assumptions Closed |
| **V3** | Byte-level certification of `detect` / `Parser_l2` / range-oracle for LP-Core | PARTIAL (`detect` cert-by-test; `Parser_l2` unverified; range oracle trusted) | XL | LP-Core grammar spec (`specs/v26/language_contract.md`) | `Parser_l2` proven sound/complete for LP-Core grammar; `detect` completeness proven OR differential battery formalized; range oracle proven OR trust boundary explicitly bounded |
| **V4** | Tier-3 Stage-6 true re-proof (or ADR-accept bridge) | OPEN decision | L (RISKY) | maintainer sign-off | `PdflatexModel.v` re-proved against faithful `compilation_succeeds`/`produces` OR an ADR accepting the additive bridge + rewriting acceptance #6 |

### Track R — Real-Time Serving

**Rationale.** Deliver the sound verdict **as the user types**. The correctness plane is fine; this is the latency/interactivity plane.

**Measured baseline that motivates the whole track** (user's real papers, warm binary, local disk, v27.1.57): `--compile-check` = **0.10s @ 4KB / 1.5s @ 30KB / 2.6–4.8s @ 80KB / 13.7s @ 316KB** (full lint alone = 10.0s @ 316KB). **13.7s is "unusable"** as-you-type — R1 (fast kernel) already fixes the 4–74KB band; 316KB is the R4 tail.

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **R1** | Fast compile-readiness kernel | **SHIPPED** (v27.1.59) | — | — | parse-once + 37 rules; fast==full over 473+150 docs → 0 divergences; sub-150ms holds to ~74KB (NOT at 316KB — that gap = R4) |
| **R3a** | Enrich T5 reason to carry byte offsets | NOT STARTED (trivial standalone unblock for R3; **independent of R2**) | S | — | `T5_rule_violations of string list` → carries offsets from `Validators.result` spans (touches `compile_contract.{ml,mli}`) so squiggles can be placed |
| **R2** | Persistent service `POST /compile-check` + CLI `--watch` | NOT STARTED | M | R1 (done) | endpoint returns SAME verdict as `--compile-check` on parity corpus; rule registry + per-file context warmed once; warm latency excludes startup (~62ms@50KB); `--watch` re-checks on change without re-spawning. **Rides the existing v25/v26 keystroke-service heritage** (`main_service`, `broker`, EDF scheduler, `hedge_timer`, REST `rest_api_server` `/tokenize` `/expand`). **Must call the in-process kernel, NOT the SIMD socket.** |
| **R3** | LSP server (didChange → debounced fast kernel → publishDiagnostics) | NOT STARTED | M–L | **R3a (hard dep, offsets)**; R2 preferred | VS Code shows squiggle at correct byte range for `$a^b^c$`/unclosed `\begin`/missing `\documentclass`, clears on fix, updates within debounce; diagnostics verdict == `--compile-check`; sub-150ms perceived on ≤74KB |
| **R4** | Incremental DELIM/ENC rules (sub-150ms on large docs) | NOT STARTED (substrate exists, unwired) | XL | R2/R3; incremental substrate (`chunk_store`/`invalidation`/`cst_edit`) + a parity gate | **⚠ THE ONE real-time item where soundness-paramount DIRECTLY CONFLICTS with the latency goal.** DELIM nesting is **whole-doc stateful** — chunk-local incremental rescan can miss whole-document nesting → an **UNSOUND false-READY** (the cardinal bug). Therefore R4 is **deferrable indefinitely** while the target holds for ≤74KB docs; if ever built it MUST preserve whole-doc delimiter soundness (parity gate: incremental verdict == whole-doc `--compile-check` across a fuzzed edit stream) before wiring. |

### Track E — Subset Extension (LP-Core growth)

**Rationale.** North-Star clause 3: widen the proven decidable subset. Measured trajectory (roots-LP-Core): 38.9% → ~57.6% (def) → ~76.6% (+makeatletter) → ~84% (+let) → ~88.4% (+conditionals). **Sequencing:** E1 → H → E2 → E3 → E5 → E4. (E1 is **not** blocked on any phantom "correctness items 1–6" gate — see §5; the real compile-guarantee gaps were only THREE, two DONE, one open, and none gate E1.)

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **E1** | Benign-`\def`/`\let` admission via macro registry | NOT STARTED (vehicle `user_macro_registry.ml` exists but **unwired** to classify) | L | `UserExpand.v`/`UserMacroTermination.v`; **reconcile with S3 `&`-scoping (direction (a) vs (b))** | per-instance benign check (undelimited params, non-recursive via `detect_cycle`, not edef/gdef/xdef, arity ≤9, no catcode/`\csname`) admits benign defs; `classify_lp_core_sound` re-proved under relaxed set; `test_language_contract_cert.ml` **EXTENDED not weakened** (recursive/mutual/delimited/edef still demote); re-measure ~+18–25pp; **zero new false-READY**; passes S2 |
| **E2** | Scoped balanced `\makeatletter…\makeatother` | NOT STARTED | M | E1 (shared scoped-span pattern) | lexically-balanced span with NO catcode/`\def`/`\csname` admitted; unbalanced/primitive-containing span demotes; proof update; adversarial fixtures (unbalanced, nested, catcode-inside) still demote |
| **E3** | Static conditionals, branch-union semantics | NOT STARTED | M | E2 (span/balance machinery) | statically-decidable conditional admitted **iff both branches independently LP-Core**; runtime-dependent test demotes; branch-union soundness proof; nested/unbalanced-`\fi` fixtures |
| **E4** | Static `\csname` constant-folding + whitelisted `\expandafter` idioms | NOT STARTED (deferred last — 5.2% of demotions) | M | E3 | constant-literal `\csname` folds + admits if in-catalogue; dynamic names still demote; whitelist of proven-terminating `\expandafter`; fixtures |
| **E5** | Package-contract catalogue (top packages by measured frequency) | PARTIAL (`extension_registry.ml`: 5 built-ins + `evaluate`/`over_claims`, **not ranked, not wired to classify**) | L | none hard; most valuable after E1–E3 | rank `\usepackage` frequency on 16k corpus, add top-N with risk/support ≤ `max_support_for_risk`; wire registry into classifier; `evaluate ~base` reflected in profile; `over_claims=false` asserted per entry |

### Track H — Heuristic Tier (deliberately NON-PROVEN, INVERTED soundness contract)

**Rationale.** North-Star clause 4: the ~12–16% residual no decidable extension will cover still needs a user-facing signal.

> **⚠ H1 is NOT a semantic / macro-universe item.** It is the deliberately **non-proven** tier whose soundness contract is **INVERTED** relative to the proven tier: **a false LIKELY-OK is tolerable BY DESIGN**, whereas in the proven tier a false-READY is the cardinal bug. Because its contract is inverted, H1 **must be visually and API-separated from the proven READY verdict** — a heuristic guess may NEVER be rendered as, or mistaken for, a proof. (Existing substrate: the proven-sound v2 ML span-extractor, `proofs/ML/SpanExtractorSound.v`, F1=0.9799 — prior art for the calibrated predictor.)

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **H1** | Heuristic "likely-compiles" predictor | NOT STARTED (no heuristic compile-tier exists) | M–L | E1 (calibrate on enlarged boundary); R1/R2 (deliver as-you-type); overlaps V1 undefined-cs class | `--compile-check` gains three states: **PROVEN-READY** / **LIKELY-OK(p)** / **LIKELY-FAIL(reasons)** — heuristic states VISUALLY/API-distinct, NEVER shown as proof; signals = undefined-cs dictionary (base+package catalogue), brace/`$`/env balance, math-mode leak, package conflicts (from E5); **monotone**: PROVEN-READY never downgraded; calibrate p on 6,899 real papers + report precision/recall vs pdflatex; **false LIKELY-FAIL tolerable, PROVEN-READY-that-fails is NOT** |

### Track C — Rules / Candidate Coverage

**Rationale.** Complete the "every fixable rule has a fix-or-candidate" DoD; the flagship compile work took priority, but coverage remains a live secondary track. **Standing cadence commitment: ≥10 new Bucket-A producers per patch release** (`FIX_PRODUCER_LEDGER.md:781`; Bucket A = 466 rules, 167 shipped, 299 pending).

| ID | Title | Status | Effort | Depends-on | Acceptance |
|---|---|---|---|---|---|
| **C-DOD1** | Close the 2 outstanding DoD violators | NOT STARTED | S–M | none | **BIB-010 shipped (v27.1.33)**; **DE-006 and ENC-006 are still `pending` in `FIX_PRODUCER_LEDGER.md`** — wire each as a verbatim-safe fix or Bucket-C candidate; then a fresh grep-grounded 643-rule re-audit to confirm "every fixable rule has fix-or-candidate" actually holds |
| **C-KR1** | Wire 5 known-recoverable diagnose-only rules | NOT STARTED (all 5 still plain `mk_result`) | S–M | none | MATH-056, PKG-001, TAB-002, TAB-007, TAB-011 each wired as Bucket-C candidate or verbatim-safe fix; candidate never auto-applies; differential 0-diff; `runtest` green; regenerate backlog + ledger |
| **C-COV1** | Remaining candidate-able diagnose-only coverage | PARTIAL (family batches v27.1.44–51; long tail asserted non-recoverable) | XL | KR-1 patterns | each newly-recoverable rule → determinate-target candidate; residual documented with per-rule reason (threshold/NLP/dictionary/ambiguous), regenerated into backlog |
| **C-WS1** | Promote deferred whitespace pilot rules (TYPO-006/007/008/024) to default lint | DEFERRED (`docs/archive/RULES_PILOT_TODO.md`) | S–M | fix-set **DELEGATION** design + post-pilot graduation gate | TYPO-006/007/008/024 are candidates for default-lint promotion, deferred pending: (1) fix-set **delegation** (e.g. **TYPO-007 spaces-only vs SPC-005 tabs** — decide who emits what) and (2) the **post-pilot graduation gate** = 2 unchecked tasks in `RULES_PILOT_TODO.md`: **FP review on a real corpus** + **perf smoke** (full-doc + 4KB window). **NB: ALL pilot TYPO rules are `maturity: Draft`, gated behind `L0_VALIDATORS=pilot`** — promotion means un-gating, so the graduation gate is load-bearing |
| **C-NLP1** | TYPO-019/020/030/031 sentence-rewrites | DEFERRED by design (`validators_l0_typo.ml`) | L | NLP/dictionary substrate the repo lacks (partial prior art: the v2 ML span-extractor) | candidate (never auto-fix) gated by a real model; no false rewrites. Likely stays deferred until product funds NLP tier |
| **C-FD1** | CJK/RTL byte-level feature-detection migration | PARTIAL (`Japanese_cjk` + `body_required_features` exist; general RTL/bidi + byte-level not present) | M | v27.1.58 front-end (landed); `compile_evidence.ml` enum extension | CJK/RTL detected from token stream drives `all_features_compatible` vs engine profile; false-READY holes (CJK without capable engine) closed; **proven, not heuristic** |
| **C-DR1** | Document the SETTLED 167 producer decomposition + cross-ref the two ledgers | OPEN (doc-only) | S | none | **Producer count is SETTLED at 167** = 70 (L1+ `mk_result_with_fix`) + 47 (L0 `with_fix`/`fix_of`) + rest. Task is to **DOCUMENT this decomposition** and **cross-reference the two generated ledgers** (`FIX_PRODUCER_LEDGER.md` + backlog) so their independently-generated numbers reconcile in one place. **Do NOT "correct" 167 down to 70** (70 is only the `_with_fix_exempt` verbatim-hardened subset). Also note: **the "596" figure is a phantom** — it appears nowhere in specs/docs/governance and has **no retirement task**; ignore it entirely. |

### Parked (ADR-010)

**WS10 (collaboration & review) + WS11 (platform roles/permissions/deployment) — PARKED, not abandoned** (`docs/v27/adr/ADR-010-park-ws10-ws11-collaboration.md`, Accepted 2026-07-12). The Overleaf-like multi-user layer is an undecided product commitment. Effort if revived: **XL**. Compatibility contract to preserve so a future WS10/WS11 is *additive, not a rewrite*:
- **Stable anchors** — findings/edits keyed by CST/project-graph spans (byte-lossless CST); keep intact.
- **Externalized review state** — WS9 Stage-2 `editorial_review.ml` (`.lpreview`, states + owner + audit trail) is the single-user precursor of WS10 threads; keep decoupled from core.
- **Deterministic, side-effect-free core** — `Validators.run_all` pure over source + per-run-cleared `*_context`; required for WS10 merge/rebase determinism.
- **Policy/permission seam** — WS9 policy + WS12 contracts are config+CLI layers that never change default output; WS11 extends the same seam. Do not bake auth/roles into core.
- **No format lock-in** — `.lppolicy`/`.lpreview`/manifests are line/JSON configs.

*(Already delivered and NOT parked: WS9 editorial policy Stages 1–2, WS12 extension plane Stages 1–2.)*

---

## 4. Classification of every remaining item

### A. Deterministic-structural — closeable now (soundly, with a precise detector; each must pass the S2 differential-fuzz gate)
- **S1** (ship v27.1.60 gate), **S2** (the standing fuzz gate itself), **S3** (misplaced-`&` in strict LP-Core — deterministic *within* LP-Core, shippable independently via direction (b)), **S5-T4** (source-only duplicate-label).
- **R2, R3, R3a** (serving/offset enrichment — engineering, not modelling). **R4** is deterministic-structural but its chunk-local incrementalization is the one soundness-vs-latency conflict (see B/notes).
- **E2, E3, E4** (balanced-span / branch-union / constant-fold — statically decidable).
- **C-KR1, C-COV1, C-WS1** (candidate/pilot wiring with determinate targets), **C-DOD1** (close DE-006/ENC-006), **C-DR1** (doc reconciliation), **C-FD1** (byte-level CJK/RTL detection).

### B. Semantic / macro-universe — needs a modelled catalogue (bounded but heavy)
- **V1** (macro/package-universe tier — the 6/8 residual false-READYs), **V2** (660-rule Coq soundness), **V3** (byte-level cert of `detect`/`Parser_l2`/range-oracle).
- **S5-T1** (bounded-expansion probe for math-in-text / illegal `\newcommand` arg-count).
- **E1** (benign-`\def`/`\let` admission — the coverage jump; the E1/S3 `\def\bea` coupling lives here — resolvable via direction (a) OR (b)).
- **E5** (package-contract catalogue).
- **R4-statefulness** (whole-doc delimiter nesting — the soundness half of the R4 conflict).

### H. Heuristic (deliberately non-proven, inverted contract) — its OWN class
- **H1** — the *labelled* likely-compiles tier. It reuses the same undefined-cs / package modelling as V1, but its false-positive contract is inverted (false LIKELY-OK tolerable) and its verdict must be **rendered separately from proof**. A fully-modelled catalogue can promote *parts* of H1 into the proven tier (V1), but H1 itself is never a proof.

### C. Impossible-by-design — excluded from the guarantee
- **Full-LaTeX total compile-decision** (Turing-complete ⇒ undecidable). Anything outside LP-Core requiring `\write18`/`\catcode`/`\csname`-on-dynamic-names/runtime-conditional expansion. These are classified **LP-Foreign → NOT-READY** or surfaced only via the H1 heuristic tier, never as proof.

### D. Parked-by-decision
- **WS10 / WS11** (ADR-010). **C-NLP1** (TYPO-019/020/030/031 — deferred until product funds an NLP/dictionary substrate; Bucket-B STYLE sentence rules with it).

---

## 5. Sequenced Roadmap

### Near-term (next 3–5 moves)
1. **S1 — Ship v27.1.60 to main.** Closes the real `$a^b^c$`-class false-READY holes (**10 → 8** on the differential matrix) with **0 measured over-rejection** (after the found-and-fixed precision regressions). The guarantee doc already narrates it as landed on the branch → doc/impl drift vs `main` until this merges. Merge → tag → `diff_compile_check.sh` = 8 known / 0 new. *(Effort S; only user merge pending.)*
2. **S2 — Stand up the standing differential-fuzz gate.** Automate the generator on top of `diff_compile_check.sh`; mechanically enumerate structural false-READYs instead of anecdotal fixtures. **This becomes the gate every future structural/E-track item must pass — local / pre-release (CI has no pdflatex).** *(Effort L.)*
3. **C-DR1 + C-DOD1 — Documentation & DoD hygiene.** Document the **settled 167** producer decomposition + cross-ref the two ledgers (drop the phantom "596"); and close the **2 outstanding DoD violators DE-006/ENC-006** (BIB-010 already shipped). Cheap, removes live stakeholder-confusion + a DoD gap. *(Effort S then S–M.)*
4. **R3a → R2 — offsets, then the persistent endpoint.** **R3a** (T5 reason byte-offset enrichment, effort **S**, `compile_contract.{ml,mli}`) is a **trivial standalone unblock** for any squiggle UI and is **independent of R2**; do it first. **R2** (persistent `POST /compile-check` + `--watch`, effort **M**) amortizes registry-build cost and rides the existing v25/v26 keystroke-service heritage. *(Effort S then M.)*
5. **S4 — Run differential validation over the full 6,899-paper tree**, publish the confusion matrix. Turns the honest "8 / 0" numbers into a versioned, reproducible commitment. *(Effort M; needs local pdflatex.)*

### Medium-term
- **R3 — LSP server** (hard dep: R3a done; R2 preferred). The product surface for the traffic-light.
- **E1 — benign-`\def`/`\let` admission** — the single biggest proven-coverage jump (~+18–25pp). **Not blocked on any phantom gate.** **Coupled with S3:** admitting `\def\bea{\begin{eqnarray}}` moves alignment-macro docs into the proven tier where an `&` gate would fire → resolve the boundary via **direction (a) model alignment-shortcut expansion** OR **(b) carve those defs into LP-Extended** (which also lets S3 ship independently first). Resolve the boundary *before* E1 admits alignment-macro defs.
- **H1 — heuristic tier** — after E1 re-calibrates the boundary; overlaps V1's undefined-cs modelling; must be UI-separated from proof.
- **E2 → E3** — scoped `\makeatletter`, then static conditionals (share span/balance machinery).
- **C-KR1 → C-WS1 → C-COV1** — wire the 5 known-recoverable rules, graduate the whitespace pilot rules (after delegation + graduation gate), then the remaining candidate-able tail.
- **V4 decision** — do the risky Tier-3 re-proof or ADR-accept the bridge.

### Long-term
- **V1 — macro/package-universe semantic tier** (XL) — the dominant 6/8 residual; decide vs. leaving it to H1 (see Q-V1).
- **V2 — all-660 Coq soundness**, **V3 — byte-level cert of the trusted layer** (`Parser_l2`, `detect`, range oracle).
- **E5 → E4** — package catalogue (parallelizable), then `\csname`/`\expandafter` (lowest value, last).
- **R4 — incremental DELIM/ENC** — only if the size SLA demands sub-150ms on 316KB docs. **Deferrable indefinitely** while the target is typical ≤74KB papers; the whole-doc-nesting soundness risk means it must preserve delimiter soundness under a parity gate before wiring.
- **WS10/WS11** — only on a product decision (ADR-010 is the go/no-go checklist).

### Cross-track dependency map
- **S3 (misplaced-`&`) ⇄ E1** — share the `\def`/alignment-macro boundary (the cardinal coupling); direction (b) DECOUPLES them so S3 can ship first.
- **S2 is a gate for S3 / S5 / E-track / every future detector** — not a leaf.
- **H1 overlaps V1** — the undefined-cs / missing-package classes are the same; decide one catalogue serving both tiers vs. two mechanisms. H1 stays separately rendered from proof regardless.
- **R3-LSP ⇒ R3a (offsets, hard) + R2 (warm state, preferred).** R3a and R2 are independent of each other.
- **R4 ⇒ R2/R3** (only meaningful with a warm buffer + edit stream) **+ whole-doc delimiter parity gate.**
- **C-FD1 ⇒ v27.1.58 front-end** (landed).
- **E2/E3/E4 chain** on shared span/balance machinery; **E1 first** establishes the "admit-within-scope" pattern.

---

## 6. Open Decisions & Risks

### Open decisions (need a call / sign-off)
- **Q-S1:** Ship v27.1.60 now? (Closes real false-READY holes 10→8, 0 measured over-rejection; pending only user merge.) — **Recommend yes.**
- **Q-S3/E1 (the coupling):** Where does `\def\bea{\begin{eqnarray}}` land? **(a)** admit E1 → the `&` gate must model alignment-shortcut expansion; or **(b)** carve alignment-shortcut defs out into LP-Extended (then S3 ships independently and soundly for strict LP-Core). **Resolve before E1 admits alignment-macro-bearing defs.**
- **Q-E1 granularity:** admit a benign `\def` **per-instance** (more permissive, forces the `&` coupling) or **per-document** (only when the whole def-set is benign-and-acyclic — 62.2% of def-demoted docs; simpler to prove sound)?
- **Q-V1:** Build the macro/package semantic tier (XL, still not a *total* certificate) or accept the 8-doc residual permanently and invest in H1 instead?
- **Q-V4:** Risky isolated re-proof of `PdflatexModel.v` against faithful semantics, or ADR-accept the additive bridge + rewrite acceptance #6?
- **Q-H1/V1 boundary:** one modelled undefined-cs catalogue serving BOTH tiers (proven NOT-READY where authoritative, heuristic LIKELY-FAIL elsewhere), or two separate mechanisms? (H1 output stays UI/API-separated from proof either way.)
- **Q-E5 authority:** are built-in package contracts *authoritative for compile-check* (provided macros count as defined → feeds proven tier) or advisory-only (→ H1)?
- **Q-R4 need:** is incremental DELIM/ENC needed for v1 at all? Depends on the target document-size SLA — with the whole-doc-nesting soundness risk, "no" is the safe default while ≤74KB holds.
- **Q-R3 build-vs-buy:** hand-rolled OCaml JSON-RPC LSP vs. an OCaml LSP lib (affects effort M vs L + UTF-16 position-mapping burden). Plus debounce policy (idle interval, on-save vs. on-keystroke).
- **Q-scope:** formally spec the "Latex-epsilon"/LP-Core boundary name so "provably compiles" has a citable, versioned scope? (Currently only `LP-Core/Extended/Foreign` in `specs/v26/language_contract.md`; "Latex-epsilon" appears only in appendices.)
- **Q-DoD:** the DoD is **not** fully closed — **DE-006/ENC-006 are still pending** (only BIB-010 shipped), and no full grep-grounded 643-rule re-audit was run. Needs C-DOD1.
- **Q-WS10/11:** still pending product decision; PARKED stands.
- **Q-NLP funding:** TYPO-019/020/030/031 + Bucket-B STYLE rules stay deferred until a decision funds the NLP substrate (partial prior art: the v2 ML span-extractor).

### Key risks
- **R-drift:** v27.1.60 unpushed ⇒ `COMPILATION_GUARANTEE.md` (on the branch) narrates the gate + "8 false-READY" as landed while `main`'s tag is v27.1.59 and shows 10. Anyone reading `main` gets an inconsistent picture until S1 merges.
- **R-single-source-of-truth (fixed en-route, now a guardrail):** `compile_contract.ml` carried a **DUPLICATE local `is_compile_blocking`** (prefix-only over `DELIM-`/`ENC-`/`PRT-`) that would make any *id-level* promotion a **silent no-op**. Standing guardrail: the **single source of truth is `Validators.is_compile_blocking`** — do not reintroduce a prefix-only shadow.
- **R-additive-bridge:** Tier-3 Stage-6 is an additive consistency result, NOT the plan's re-proof; if the abstract capstone diverges from the faithful model, the bridge won't catch it (V4).
- **R-empirical-detectors:** the structural-fatal detectors are pinned "against pdflatex" by a *test battery*, not a Coq proof. A missed pdflatex edge case (unusual catcode/engine version) could re-open a false-READY or add over-rejection. The 4096-frame "bail safely" path is conservative toward false-READY (the dangerous direction). **Mitigation is exactly S2 — the standing fuzz gate.**
- **R-coverage-gates-are-not-full-surface:** "differential 0-diff + convergence" exercised only ~54% of producers (69/150 never corpus-triggered) and passed the control-word-glue corruption + STYLE-033 corruption unnoticed. Full-surface safety needs the multi-variant `check_producer_coverage.py` gate + output inspection, not just convergence.
- **R-trusted-base:** even with the verified front-end, byte-list conversion, build-graph construction, the protected-range oracle, runtime↔extracted-type conversion, file I/O, and the OCaml+Coq extraction toolchain are trusted/tested, not verified end-to-end. `fnv_mul_bound` is asserted informally (validated by parity test, not in-kernel).
- **R-fast==full:** the fast kernel's verdict-equality to the full path is an equivalence argument + differential gate, not a Coq proof; a bug in `run_compile_blocking`'s shared-context reproduction could make fast disagree with full.
- **R-E1-cardinal:** relaxing the blanket `\def`-demotion is precisely the move that could introduce a false-READY. `test_language_contract_cert.ml` must be **EXTENDED** (recursive/mutual/delimited/edef still demote) *before* any admission, and `classify_lp_core_sound` re-proved. Unknown ⟹ demote.
- **R-R4-statefulness:** DELIM nesting is whole-document stateful; naive chunk-local rescan is UNSOUND (a `{` before the edit changes downstream meaning) → the cardinal bug. The R1-style parity gate must precede any wiring. The incremental substrate (`chunk_store`/`invalidation`) was built for tokenize/expand, never exercised under compile-blocking rules.
- **R-count-authority:** 167 (ledger, SETTLED) is generated independently from the 124 (candidates) and the 70 (`_with_fix_exempt` subset) — CI drift gates enforce each file against ITS OWN generator, so none catches cross-file disagreement (C-DR1 documents the reconciliation).
- **R-squash-drops-commits:** a squash-merge strands later commits on the branch (v27.1.5 lost 11 producers, recovered via cherry-pick). Serialize version bumps; keep a recovery plan for any stacked PR.
- **R-residual-assertion:** the 402 "non-candidate-able" diagnose-only rules are a *per-family* assertion, not individually re-audited. History warns this judgement has been wrong before ("my rule EXCLUSIONS were wrong — I deferred rules as unsafe/ambiguous without reading the catalogue"). Re-audit against `rules_v3.yaml` before declaring done.
- **R-corpus-representativeness:** the lint corpus is 470/473 LP-Core (too clean); the 88.4% recovery number rests on an UNTRACKED `bench_classify` driver + a 15+-day-old scratch analysis. Commit the bench and re-reproduce under version control before quoting E-coverage as a commitment.
- **R-tags-without-commits:** v27.1.58/59 tags are on `origin/main` but the checked-out HEAD is v27.1.57; C-FD1 depends on the front-end. Confirmed present on origin/main this session — but if those branches were ever lost, several items are further from done than the tag list implies.

---

*Sources: `docs/COMPILATION_GUARANTEE.md`, `governance/project_facts.yaml`, `specs/v27/{FIX_PRODUCER_LEDGER,CANDIDATE_BACKLOG}.md`, `specs/rules/{rules_v3,rule_contracts}.yaml`, `docs/archive/RULES_PILOT_TODO.md`, `docs/v27/adr/ADR-010-*.md`, `latex-parse/src/{compile_contract,compile_gate_checks,validators,language_profile,unsupported_feature,user_macro_registry,extension_contract,extension_registry,compile_evidence,validators_l0_typo,validators_l1_math,validators_l2}.ml`, `ml/checkpoints_v2/{best_model.pt,eval_results.json}`, `proofs/{PdflatexModel,BodyTokenFrontEnd,CompileGuaranteeBridge,LanguageContract,LexerFaithfulStep,FaithfulWS8Bridge}.v`, `proofs/ML/SpanExtractorSound.v`, `scripts/tools/{diff_compile_check.sh,check_producer_coverage.py}`; memory: `MEMORY.md`, `compile_prediction_priority.md`, `realtime_readiness_track.md`, `lp_extension_measurement.md`, `compile_blocking_promotion_finding.md`, `producer_coverage_gate.md`, `coq_nat_pow_qed_blowup.md`, `feedback_squash_merge_drops_late_commits.md`, `v27_faithful_status.md`, `fix_output_safety.md`, `bucketB_sentence_pilot.md`. Verified this session: version 27.1.57 on the tree; tags v27.1.58/59 on origin/main; v27.1.60 in flight `f0f8cbcd` (compile_gate_checks.ml = 632 lines, matrix 10→8 false-READY, precision regressions found-and-fixed in b3bf23f1); 176 proof files (61 core + 114 generated + 1 ML + 7 archived); producers 167 SETTLED (BIB-010 shipped, DE-006/ENC-006 pending); no Admitted/Axiom in active proofs; ADR-010 present; no pre-existing `docs/v27/ROADMAP.md`.*
