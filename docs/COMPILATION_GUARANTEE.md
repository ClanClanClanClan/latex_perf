# Compilation guarantee — user-facing summary

**For LaTeX Perfectionist v26.2+.**

This doc summarises what claims v26.2 makes about your project's
compilability, and what claims it explicitly does not make. Formal
details live in [specs/v26/compilation_guarantee_stack.md](../specs/v26/compilation_guarantee_stack.md)
and [specs/v26/compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml).

---

## TL;DR

Run `latex_parse_cli --compile-check path/to/main.tex` before running
latexmk. If it says **READY**, these runtime preconditions genuinely
held (within the declared profile):

- Your source **parsed** with the real L2 parser (no unclosed
  math/environment/`\verb`) and is **not** in the LP-Foreign tier
  (no `\write18`, etc.).
- Your multi-file project is closed (no missing `\input`, no cycles).
- Your selected engine supports every **declared** feature.
- No **compile-blocking** lint rule fired (`DELIM-`/`ENC-`/`PRT-`) —
  including the `DELIM-001` unbalanced-brace check the parser itself
  does not catch.
- If a sibling `.aux` was present, its labels are unique.

**READY is a sound readiness PRE-CHECK, not a total "it will compile"
certificate.** It means every runtime precondition we check held; it does
**not** prove the document compiles. What is NOT verified at runtime: T1
macro-expansion (skipped), T4 without an `.aux` (skipped), and the
byte-for-byte connection from your source to the abstract model the T6/T7
compile-safety capstone is proved over (see the residual-gap note below).
Everything else about compile success falls back on the toolchain itself.

---

## What `--compile-check` runs (v27.1.52; fast kernel v27.1.59; structural-fatal gate v27.1.60)

The CLI's `--compile-check <file.tex>` flag invokes
`Compile_contract.check_ready_to_compile` in
`latex-parse/src/compile_contract.ml`, with the same per-file context the
lint path sets up (file context, command spans, build profile, user
macros, language profile). It checks the T0–T5 conditions and prints
`READY` (exit 0) or `NOT-READY` + the failing reasons (exit 1). Here is
**exactly** what each check does at runtime today — no more, no less:

| Check | What it ACTUALLY runs now | Real / conservative |
|---|---|---|
| T0 Parse + profile | `Language_profile.classify_source` → NOT-READY on **LP-Foreign**; then `Parser_l2.parse_located` → NOT-READY with the first structural parse error (unclosed math/env/`\verb`, `\end` without `\begin`, nesting blow-up) + line/offset. As of **v27.1.57** the tier DECISION (feature-list → tier) is the **Coq-extracted** `LanguageContract.classify` (governed by `classify_lp_core_sound`); only `Unsupported_feature.detect` (bytes → features) stays trusted, adversarially certified — see "LP-Core classifier" below | **REAL** |
| T1 Expansion | *no-op* — not runtime-checked at this layer | conservatively skipped (never claims a T1 property) |
| T2 Project closed | `Build_graph` — every `\input`/`\include` resolves, no include cycle | **REAL** |
| T3 Profile compat | declared-feature × engine compatibility table | **REAL** (from *declared* features; v26.2 does not auto-detect) |
| T4 Semantic coherence | if a sibling `.aux` exists: duplicate-label detection | **REAL when `.aux` present**, else skipped |
| T5 Rule safety | runs the **compile-blocking** rules only (`Validators.run_compile_blocking`, fast kernel v27.1.59) and flags their `Error` results — rule families `DELIM-*`, `ENC-*`, `PRT-*` | **REAL** (narrowed on purpose; see below) |

If every check passes, `check_ready_to_compile` returns `Ready`; otherwise
a list of structured reasons is returned and printed one per line.

**Why T5 is narrower than "no Error rule fires".** Many `Error`-severity
rules are completeness/style faults that pdflatex compiles through anyway
(e.g. `DOC-001` "missing `\maketitle`"). Flagging every Error would make a
perfectly clean article NOT-READY. `--compile-check` therefore flags only
the `DELIM-`/`ENC-`/`PRT-` families — mismatched delimiters, byte/encoding
faults, and parse-reliability rules — which correspond to structural faults
the engine cannot recover from. This is intentionally conservative: a
false NOT-READY is safe; a false READY on a broken document is not.

**T0 and T5 are complementary.** The L2 parser is error-*recovering*, so
some structural faults it does not itself flag — most notably an unbalanced
brace group, which it silently closes at EOF — are caught by **T5's
`DELIM-001`**, not by T0. Neither check alone is a proof of well-formedness.

**Fast readiness kernel (v27.1.59) — a verdict-preserving optimization, not a
semantic change.** `--compile-check` used to call `Validators.run_all` (parse the
whole document, build the semantic state, scan the event bus, execute all ~641
registered rules) and parse a second time in the T0 check, then FILTER the results
down to the 37 compile-blocking rules. Since v27.1.59 it parses **once** and runs
**only** those 37 rules (`Validators.run_compile_blocking`, sharing the single
`Parser_l2.parse_located`). This is sound because validators are pure functions of
`(source + shared context)` and the compile-blocking set is a fixed prefix filter, so
running only those rules yields the SAME results as running all then filtering — the
Ready/NotReady verdict and its reason set are **byte-identical**. A parity gate
(`test_fast_readiness_parity.ml`, wired into `runtest`) asserts fast==full over every
`corpora/` document (473 docs) plus a 150-paper CLI sample; the original full path
remains available as `--compile-check-full`. The kernel is ~6.8x faster on large
documents (a 316KB paper: ~6.3s → ~0.93s; a 50KB paper: ~0.92s → ~0.14s).

---

## Theorems that are NOT runtime checks

- **T6 (compilation progress):** if T0–T5 hold AND the toolchain
  converges in bounded passes, compilation succeeds. v26.2 shipped
  this hypothesis-parametric; **v27 WS8 discharges it concretely
  for pdflatex** in `proofs/PdflatexModel.v::pdflatex_T6_discharged`.
- **T7 (output well-formedness):** if T6 holds AND the toolchain
  produces a well-formed artefact, the output satisfies the subset's
  output contract (valid PDF graph, fatal-free log). v27 WS8
  discharges it concretely for pdflatex in
  `proofs/PdflatexModel.v::pdflatex_T7_discharged`.
- **Headline (v27 WS8 capstone):** `pdflatex_compile_safe` (Qed,
  Closed under the global context) — for any project_well_typed
  project and profile_supported profile, there exists an artefact
  such that pdflatex produces it, compilation succeeds, and the
  output is well-formed. Zero axioms, zero admits. As of v27.1.29–v27.1.39
  the capstone is proved against a **faithful operational pdflatex
  semantics** (token/aux/log/pass model, tight ≤2-pass convergence,
  warnings-iff-unresolved, PDF-artefact model) rather than the earlier
  abstract pass-iteration model; see
  [`specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md`](../specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md).
  Honest residuals: the T0/T1/T5 universal obligations and byte-exact PDF
  *structural* semantics stay conservative/deferred.
- **Decidable premise-bridge (v27.1.53) + Coq→OCaml extraction (v27.1.55):**
  `proofs/CompileGuaranteeBridge.v::project_wf_dec` + `project_wf_dec_sound`
  (Qed, 0 admits, Closed) make the capstone's premises a *computable* check.
  As of v27.1.55 that checker is **Coq-EXTRACTED** to OCaml
  (`proofs/CompileGuaranteeExtract.v` →
  `latex-parse/src/compile_guarantee_extracted.ml`) and `--compile-check`'s
  `MODEL-CONNECTED` line **executes the extracted proven function** on the real
  document — the hand-written OCaml mirror is eliminated (residual (a) closed).
  See "Model-connected verdict" below for exactly what is proven vs tested vs
  trusted.
- **Verified bytes→`body_token` front-end (v27.1.58):** the input end of the
  pipeline — token/key scanning, FNV-1a hashing, feature detection, body
  assembly — is now **Coq-extracted-and-proven**
  (`proofs/BodyTokenFrontEnd.v::compile_safe_of_source`, Qed, 0 admits, Closed →
  `latex-parse/src/body_token_frontend_extracted.ml`, byte-identical regen).
  `--compile-check` runs this extracted front-end (`extract_body_verified`), and a
  differential parity gate proves it byte-identical to the retained hand OCaml over
  393 corpus files + 422 fixtures. The trusted base at the input end shrinks to the
  protected-range oracle + string→byte-list conversion (see "Model-connected
  verdict"). Two honest notes: `fnv_mul_bound (<2^55)` is asserted informally (a
  Peano-`nat` kernel pathology, validated by the parity test), and the FNV
  constants are realized as native `int` literals each provably equal to their Coq
  definitions.
- **LP-Core classifier: proven tier-decision + certified detection (v27.1.57).**
  The compile guarantee is scoped to the **decidable subset LP-Core**, which
  excludes the Turing-complete escape hatches of LaTeX — arbitrary `\def`
  (and `\edef`/`\gdef`/`\xdef`/`\let`), `\csname`, `\catcode`, and primitive
  conditionals outside the supported catalogue (`\ifnum`/`\ifx`/`\ifcase`/…),
  plus LP-Foreign triggers (`\write18`, `\directlua`, shell-escape). The
  classifier is a two-step pipeline; the trust boundary between the steps is now
  precise:
  1. **`Unsupported_feature.detect` (bytes → feature-list)** — a regex scan.
     This is **TRUSTED, not formally verified**, but is now **adversarially
     certified** by `latex-parse/src/test_language_contract_cert.ml`: 15 construct
     families across **63 syntactic forms** (whitespace, comments, line breaks,
     obfuscation — e.g. `\def` after a comment, `\csname` split across lines,
     `\catcode` with an interposed space) must all leave LP-Core, plus 7
     obfuscated whole-document cases and 15 genuine LP-Core documents (with
     lexical near-misses like `\mydef`, the word "define", `\textbf{def}`) that
     must **stay** LP-Core. A single slip-through fails the build.
  2. **`LanguageContract.classify` (feature-list → tier)** — the tier DECISION.
     This is now **Coq-EXTRACTED** to OCaml (`proofs/LanguageContractExtract.v`
     → `latex-parse/src/language_contract_extracted.ml`, regen
     `scripts/tools/regen_language_contract_extract.sh`, byte-identical), and
     `Language_profile.classify_source` **executes the extracted proven
     function** — the former hand-written OCaml mirror of the foreign-then-
     forbidden-then-core decision is eliminated. The extracted verdict is
     governed by `classify_lp_core_sound` (Qed, 0 admits, Closed): if the result
     is `LP_Core`, no forbidden-in-core feature was present in the feature-list.
  Net: the feature-list → tier step is **proven-and-executed**; the residual is
  that step 1's regex-over-bytes is trusted rather than formally verified. That
  residual is a **bounded, decidable-subset** task (a fixed catalogue of
  primitives), NOT the impossible general problem of statically deciding
  arbitrary Turing-complete LaTeX — and it is guarded by the adversarial
  certification corpus above.

xelatex / lualatex remain hypothesis-parametric; concrete WS8-style
discharge for those engines is a future workstream.

---


## Differential validation against real pdflatex (measured, not asserted)

`scripts/tools/diff_compile_check.sh` runs `--compile-check` AND the real `pdflatex`
binary over a labeled corpus (`corpora/compile_check/`) and reports the confusion
matrix. This turns the readiness claim into a *measured* fact rather than an assertion.
Classification is outcome-driven (from the two real verdicts), not from the filename.

**At-scale run (65 standalone documents, pdfTeX 3.141592653-2.6-1.40.29 / TeX Live 2026).**
The corpus spans clean docs of varied complexity (`good_*`: article with
sections/math/lists/tabular/figure/verbatim/footnotes/cross-refs/bibliography, amsthm,
tikz, minipage, `\input` child, report class, UTF-8 accents, user macros), genuine
compile-FAILURE classes (`fail_*`), and pdflatex-TOLERATED sloppiness (`tolerated_*`):

| soundness direction | count | meaning |
|---|---|---|
| correct **READY & COMPILES** (true-READY) | 35 | clean docs of varied complexity, all certified and all compile |
| correct **NOT-READY & FAILS** (true NOT-READY) | 20 | unclosed math/display-math/env/`\verb`, extra/stray `}`, `\begin`/`\end` mismatch, extra `\end`, `\left` without `\right`, mismatched `$` toggles, runaway argument, missing `\input`, missing `\begin{document}` — plus (v27.1.60 structural-fatal gate) **double super/subscript, missing `\documentclass`, `\usepackage` after `\begin{document}`** — all caught by T0/T2/T5 and the new structural-fatal gate |
| **FALSE-READY** (cc=READY, pdflatex FAILS) | **8** | the dangerous soundness residual — every one requires macro/package-universe modeling or full expansion the pre-check does not perform (enumerated below); **0 new** beyond the documented allowlist. Reduced from 10 in v27.1.60: `fail_double_subscript` and `fail_no_documentclass` are now correctly NOT-READY. |
| false-not-ready (cc=NOT-READY, pdflatex COMPILES) | 2 | safe conservative over-rejection: a bare unclosed `{` group pdflatex auto-closes, and a `\write18` doc pdflatex tolerates in restricted mode (shell-escape is genuinely LP-Foreign) |

Total = 35 + 20 + 8 + 2 = 65.

The harness exits nonzero ONLY on a **NEW** false-READY — one whose basename is not in
the documented `KNOWN_FALSE_READY` allowlist inside the script (the 8 limit-class docs
below). Known-limitation misses do not fail the run; a genuinely new soundness miss does.
This makes it a usable local soundness **regression guard** (not a CI gate — CI has no TeX).

### Structural-fatal gate (v27.1.60) — deterministic non-Turing compile-fatals now caught

Some compile-fatals are **not** Turing-hard: they are decidable from the token structure
alone, without building the macro table or expanding anything. v27.1.60 adds a dedicated,
comment-/verbatim-/math-/moving-arg-aware detector module (`compile_gate_checks.ml`),
wired into **both** the fast readiness kernel and the full readiness path, that turns three
such classes from false-READY into correct NOT-READY:

- **Double super/subscript** — `$a^b^c$`, `$x_a_b$` (a subscript/superscript with no
  intervening group is `! Double superscript`/`! Double subscript`). The detector is
  math-mode-aware and only fires on adjacent unbraced scripts, so legitimately nested
  braced scripts (`$x^{a^b}$`) stay READY.
- **No `\documentclass`** — a body with no `\documentclass` leaves the format
  uninitialized (`! LaTeX Error: … \normalsize is not defined`).
- **`\usepackage` after `\begin{document}`** — `\usepackage` is only legal in the
  preamble (`! LaTeX Error: Can be used only in preamble`). The detector ignores
  `\usepackage` text inside verbatim/comments and preamble occurrences.

Each detector reads the raw token structure (comment-, verbatim-, math- and moving-arg-aware)
so it does not fire on literal text in verbatim/comments or on false-positive contexts.
Measured impact: **zero over-rejection across 6,396 real root papers**, and the differential
false-READY count dropped from 10 to 8. Misplaced `&` was intentionally **dropped** from
this gate — see "Known remaining false-READY classes" below.

### The 8 false-READYs, enumerated and analyzed (honest soundness data)

Each of these is a document the pre-check certified READY but `pdflatex` FAILED on. They
are the point of this exercise: they measure exactly where READY is *not* a compile
certificate. Every one is caused by the pre-check NOT modeling the macro/package universe
or NOT running full TeX expansion — precisely the T1-expansion obligation that
`--compile-check` conservatively skips (see the T1 row of the runtime table above).

| doc | real pdflatex error | why the pre-check provably cannot catch it |
|---|---|---|
| `fail_undefined_cs.tex` | `! Undefined control sequence` | `\foobarbazundefined` parses as a well-formed control word; knowing it is undefined requires the live macro table (format + every loaded package), which the pre-check does not build. |
| `fail_undefined_environment.tex` | `! LaTeX Error: Environment nonexistentenv undefined` | `\begin{nonexistentenv}…\end{nonexistentenv}` is structurally balanced (T0/T5 see a matched env); whether the env is *defined* is a macro-universe fact only `\begin` resolves at expansion time. |
| `fail_missing_usepackage.tex` | `! LaTeX Error: Environment tikzpicture undefined` | Same class: `tikzpicture` is balanced but undefined because `\usepackage{tikz}` is absent. The pre-check does not simulate package loading to know which environments a package would define. |
| `fail_align_no_amsmath.tex` | `! LaTeX Error: Environment align undefined` | `align` is balanced but undefined without `amsmath`. Detecting this needs the package→macro map, i.e. modeling the package universe. |
| `fail_bad_usepackage.tex` | `! LaTeX Error: File 'this_package_does_not_exist_xyz.sty' not found` | The pre-check's T2 project-closure resolves `\input`/`\include` sources, but does **not** resolve `\usepackage` against `kpathsea`/the TeX tree, so a nonexistent `.sty` is invisible to it. |
| `fail_bad_graphics_include.tex` | `! LaTeX Error: File '…' not found` | `\includegraphics` file existence is a runtime graphics-backend lookup on the TeX search path, not part of the closure T2 tracks. |
| `fail_math_in_text.tex` | `! Missing $ inserted` | `\alpha`/`\beta` used outside math is a *mode* error: the token is defined, but only legal in math mode. Catching it requires tracking TeX's math/text mode through expansion — the full-expansion state the pre-check skips. |
| `fail_newcommand_wrong_args.tex` | `! Illegal parameter number in definition of \greet` | A `#3` in a 2-argument `\newcommand` body is caught when TeX *scans the definition*; the pre-check does not evaluate `\newcommand` bodies, so arg-count consistency is out of scope. |

> Two former entries — `fail_double_subscript` (`! Double subscript`) and
> `fail_no_documentclass` (`! … \normalsize is not defined`) — were **removed from this
> residual in v27.1.60**: they are now caught by the structural-fatal gate above and
> report NOT-READY correctly.

**Common root cause.** All eight sit on the far side of the T1 boundary: they are only
observable once TeX *expands* macros and *loads* packages/classes against the live format
and file system. `--compile-check` deliberately runs T0 (structural parse) + T2 (source
closure) + T3 (declared-feature/engine compat) + T4 (aux label uniqueness) + T5
(`DELIM-`/`ENC-`/`PRT-` Error rules) and treats T1 as a conservative no-op. Closing this
residual would require either (a) shelling out to the real engine (which is what running
`pdflatex` already does) or (b) a verified model of the macro/package universe and TeX's
expansion+mode machinery — a much larger workstream than a fast fail-first pre-check.

### Known remaining false-READY classes (measured, honestly out of scope)

These are the residual documents the pre-check reports READY but pdflatex FAILS. They are
NOT caught by the v27.1.60 structural-fatal gate because catching them precisely requires
either macro expansion or modelling the base+package macro catalogue — the T1 boundary the
pre-check deliberately does not cross.

- **Macro/package-universe class (6 of 8 above): undefined control sequences, undefined
  environments, missing/nonexistent `\usepackage`, missing package/graphics files.**
  The pre-check does not build the live macro table or resolve names against the TeX tree,
  so a structurally well-formed but semantically undefined name is reported READY. This is
  the dominant false-READY class and is why READY is a *readiness pre-check*, not a total
  compile certificate. Closing it needs a verified base+package macro-catalogue model.
- **Expansion-time arg-semantics class (2 of 8 above): math-only command in text mode,
  illegal `\newcommand` parameter number.** These are caught only by TeX's
  expansion/math-list machinery, which the pre-check does not run.
- **Misplaced `&` (intentionally out of the structural-fatal gate).** A `&` outside any
  alignment context (`tabular`/`array`/`align`/…) is `! Misplaced alignment tab character &`.
  It was **considered for the v27.1.60 gate and deliberately dropped**: `\def`-based
  alignment macros can introduce `&` in bodies that expand into legal alignment cells, so a
  purely structural gate over-rejects real documents. A precise `&` gate requires macro
  expansion and is tied to the LP-Extended boundary; it remains a documented, honest
  false-READY rather than an over-rejecting gate.
- **Conservative over-rejection of auto-closeable groups (a false-NOT-READY, the *safe*
  direction).** An unclosed OPEN group (`{x\end{document}`) is reported NOT-READY, but
  pdflatex auto-closes it and compiles (`tolerated_bare_unclosed_brace.tex`). The parser
  is stricter than the engine on sloppy groups — good for linting, conservative for
  compile-prediction. The residual over-rejection comes from the T0 parser flagging the
  unclosed group; DELIM-001 stays compile-blocking on purpose (a fatal consumed-brace case
  it cannot cheaply distinguish is the dangerous direction).
- **`\write18` shell-escape (a false-NOT-READY).** `tolerated_write18.tex` is reported
  NOT-READY (LP-Foreign) but pdflatex tolerates it in restricted-shell-escape mode. This
  over-rejection is intentional: shell-escape is genuinely out of the safe subset.


## Model-connected verdict — the `MODEL-CONNECTED` line (v27.1.53)

`--compile-check` now emits an additional `MODEL-CONNECTED` line that
genuinely wires the runtime parse to the Coq capstone's *proven premise
logic*. It is built from three pieces:

1. **A DECIDABLE premise-checker + soundness lemma, in Coq**
   (`proofs/CompileGuaranteeBridge.v`). `project_wf_dec : pdflatex_project →
   pdflatex_profile → list node → bool` checks exactly the capstone's
   hypotheses — T2 (`project_closed`, via a witness topological order it
   certifies), T3 (`profile_admits` for the profile's declared features AND
   every feature the document body requires), and T4
   (`NoDup (body_label_defs)`). The lemma
   `project_wf_dec_sound : project_wf_dec p pf order = true → project_well_typed
   p ∧ profile_supported p pf ∧ pdflatex_T4_coherent p` is **Qed, zero
   admits/axioms**, and the corollary `project_wf_dec_compile_safe` discharges
   `pdflatex_compile_safe` from a `true` verdict. `Print Assumptions
   project_wf_dec_compile_safe` prints *Closed under the global context*.
   So a `true` from this checker **provably** implies the capstone's
   conclusion (compiles, ≤2-pass convergence, fatal-free, warns-iff-unresolved).

2. **An OCaml extractor** (`latex-parse/src/compile_evidence.ml`,
   `Compile_evidence`) that maps a real `.tex` to the abstract
   `pdflatex_project`/`pdflatex_profile` the checker consumes: it **reuses**
   `Ast_semantic_state.labels`/`refs` for `\label`→`BT_label_def`,
   `\ref`/`\eqref`→`BT_label_ref` (keys hashed to stable `nat` ids), detects
   T3-relevant features (`fontspec`→`Opentype_fonts`, `unicode-math`,
   `luacode`/`\directlua`→`Lua_scripting`, CJK, …)→`BT_needs_feature`, and
   builds the T2 graph + topological order from `Build_graph.of_project`.

3. **The wiring (v27.1.55 — extracted, no mirror)**: `--compile-check`
   converts the extracted project's runtime types into the **Coq-extracted**
   types (a 1:1 constructor map in `compile_evidence.ml`) and runs the
   **extracted** `project_wf_dec` (module `Compile_guarantee_extracted`,
   generated from `proofs/CompileGuaranteeExtract.v`). It prints
   `MODEL-CONNECTED MODEL-READY` iff the extracted proven function returns
   `true` (else `MODEL-NOT-READY` with the failing T2/T3/T4 obligation).
   Default (no-flag) output is byte-identical. The hand-written OCaml mirror of
   the boolean checkers is **removed**.

### What is PROVEN-and-EXECUTED vs TESTED vs TRUSTED (be precise)

- **PROVEN (Coq, Qed, 0 admits, `Print Assumptions` Closed) AND EXECUTED at
  runtime:** the premise-decision logic itself — that `project_wf_dec = true` is
  *sufficient* for `pdflatex_compile_safe`'s hypotheses and hence its full
  conclusion. As of v27.1.55 the runtime does not re-implement this check: it
  runs the **Coq-extracted** `project_wf_dec`, so the code deciding READY is the
  same code `project_wf_dec_sound` governs. This closes residual (a): the
  executed premise-decision *is* the proven-extracted code.
- **TESTED (not proven), `test_compile_evidence.ml`:** (a) the OCaml extractor
  faithfully reflects the source — it flags a duplicate `\label` (T4) and a
  required-but-unsupported feature (T3) on real documents, accepts clean ones;
  (b) **verdict-equivalence** — the extracted `project_wf_dec` returns the SAME
  boolean as the Coq `Example`s (`project_wf_dec_true_clean`,
  `project_wf_dec_false_dup`, `project_wf_dec_false_otf`,
  `project_wf_dec_true_otf_on_xe`, proved by `vm_compute`) on the shared abstract
  projects — a sanity replay, now over the extracted function itself.
- **PROVEN-and-EXECUTED (new in v27.1.58): the bytes→`body_token` front-end.**
  The input end of the pipeline — token/key scanning, FNV-1a hashing of label
  keys, feature detection, and body assembly (the `body_token` list) — used to be
  the hand-written, UNVERIFIED extractor (`extract_body`, residual (i) below).
  It is now the **Coq-extracted** `BodyTokenFrontEnd.body_of_source`
  (`proofs/BodyTokenFrontEnd.v` → `latex-parse/src/body_token_frontend_extracted.ml`,
  regen `scripts/tools/regen_body_token_frontend_extract.sh`, byte-identical), run
  by `compile_evidence.ml`'s `extract_body_verified` on the real source. The
  capstone theorem `compile_safe_of_source` (Qed, 0 admits, `Print Assumptions`:
  Closed) connects a body built by *this* code to
  `PdflatexModel.pdflatex_compile_safe`. A **differential parity gate**
  (`test_body_token_frontend.ml`) asserts the extracted front-end == the retained
  hand OCaml over 393 corpus files + 422 fixtures.
- **TRUSTED (residuals, now precisely — the base SHRANK):** (i) the
  **protected-range oracle** `Validators_common.find_verbatim_comment_url_ranges`,
  which tells the verified front-end which byte ranges are verbatim/comment/URL
  (the front-end is proven relative to that range set, not over the raw regex that
  computes it); (ii) the **string→byte-list conversion** feeding the source to the
  extracted function; (iii) **build-graph construction** (`Build_graph.of_project`,
  the T2 include graph + topological order) and (iv) the small
  **runtime→extracted-type conversion** (`to_ext_feature`/`to_ext_engine`/
  `to_ext_node`/…, a 1:1 constructor map); plus (v) **file I/O** and the (vi)
  **OCaml compiler + Coq extraction** toolchain. Two honest notes on the new
  front-end proof: (a) the `fnv_mul_bound` (`< 2^55`) lemma is asserted informally
  (a Peano-`nat` kernel pathology), validated by the parity test rather than
  proved in-kernel; (b) the extraction realizes `two30`/`fnv_basis`/`fnv_prime` as
  native `int` literals, each **provably equal** to its Coq definition.

Net effect: residual (a) — "the runtime runs a hand-written mirror, not the
proven code" — is **closed**, and residual (i) — the bytes→`body_token` front-end
— is now **proven-and-executed** too (v27.1.58). READY + `MODEL-READY` means "for
the abstract project we extracted from your source, the *proven, Coq-extracted*
front-end and checker certify the capstone premises hold." It still does **not**
mean "your exact bytes are certified to compile", because the trusted base above
(protected-range oracle + byte-list/type conversion + build graph + I/O +
toolchain) is trusted/tested rather than verified end-to-end.

Treat `--compile-check` as a fast, honest fail-first gate: NOT-READY (or
`MODEL-NOT-READY`) reliably means "do not bother running latexmk yet"; READY +
`MODEL-READY` means "no runtime precondition we check is violated, and the
extracted project passes the proven premise-check" — then run your real build.

---

## Per-profile coverage

| Profile | Status | T6/T7 discharge |
|---|---|---|
| pdflatex | GA | v27 WS8 concrete (`PdflatexModel.pdflatex_compile_safe`) |
| xelatex | beta | hypothesis-parametric; v26.3 adds xelatex aux-parser |
| lualatex | beta | hypothesis-parametric; `\directlua` side effects out of scope |
| pTeX/upTeX | experimental | no T6/T7 claim |

Full profile metadata: [compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml).

---

## What this is NOT

- **A replacement for latexmk.** Run `--compile-check` first for
  fast-fail; then run your real build. They're complementary.
- **A style checker.** The existing validators cover that.
  `--compile-check` only verifies compile-readiness, not style.
- **A guarantee against LaTeX bugs.** If pdflatex itself has a bug on
  your document, v26.2 can't catch it — T6 is parametric on toolchain
  correctness.
- **A fully Coq-extracted runtime.** v26.2's Coq theorems verify the
  abstract pipeline; most of the runtime OCaml is hand-written and tested.
  The one exception (v27.1.55) is the capstone *premise-checker*
  `project_wf_dec`, which IS now Coq-extracted
  (`compile_guarantee_extracted.ml`) and executed by `--compile-check`; the
  parser and the runtime→model type conversion around it remain hand-written.

---

## Example: CI usage

```yaml
# .github/workflows/my-paper.yml
- name: Check compile readiness
  run: latex_parse_cli --compile-check main.tex
- name: Build with latexmk
  if: success()
  run: latexmk -pdf main.tex
```

`--compile-check` exits 0 on Ready, non-zero on any failure reason.
Exit codes + structured stderr let CI fail fast before latexmk bills
you for compute on a document that can't possibly compile cleanly.

---

## Example: library usage

```ocaml
open Latex_parse_lib

let () =
  match Project_model.of_root "main.tex" with
  | Error _ -> prerr_endline "could not load project"
  | Ok project ->
      let profile =
        Build_profile.create ~tex_path:"main.tex" ~base_dir:"."
      in
      (* [~source] lets T0/T5 run on the exact bytes you already hold;
         omit it and the root .tex is read from disk. *)
      match Compile_contract.check_ready_to_compile project profile with
      | Ready -> print_endline "OK to compile"
      | NotReady reasons ->
          List.iter
            (fun r -> print_endline (Compile_contract.reason_to_string r))
            reasons
```

For formal reasoning, instantiate the Section-quantified theorems in
`proofs/CompileProgress.v` with your own toolchain model and discharge
the `compile_progress_rule` hypothesis.

---

## References

- [specs/v26/compilation_guarantee_stack.md](../specs/v26/compilation_guarantee_stack.md)  — T0–T7 formal detail
- [specs/v26/compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml) — profile metadata
- [docs/v26_2/adr/ADR-007](v26_2/adr/ADR-007-compile-stack-ships-in-v26-2.md) — why this ships in v26.2
- [docs/SUPPORT_MATRIX.md](SUPPORT_MATRIX.md) — broader support matrix
