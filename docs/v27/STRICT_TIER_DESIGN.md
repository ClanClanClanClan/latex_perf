# Design: the contract-bounded proven tier

**Status:** approved design, adopted by [ADR-012](adr/ADR-012-contract-bounded-proven-tier.md) on 2026-09-26, which records the owner's answers to §H verbatim. Milestones M0 and M1 slice 1 (§F) are implemented. M2 phase 1, the Coq kernel of the fragment L_S0 (§I.4), and M2 phase 2, the decision on the BYTES of a file with its verified reader (§I.5, a stacked branch), are proved and attested, but no product verdict uses them: the CLI's strict tier is still a stub, so nothing a user sees is proven yet. Programme ledger row: OPEN-116 in [PROJECT_STATE.md](PROJECT_STATE.md).

**Paths.** Repository paths below are relative to the repository root. A `file:line` reference gives the line as of commit `978601ee` and may have moved since. Anything marked *(scratch-only)* was produced by the design spikes in a private scratch area and is **not in the repository**; it is cited as evidence for a measured figure, not as a file you can open.

Measured against `main` = `978601ee`. Pin: `pdfTeX 3.141592653-2.6-1.40.29`, TeX Live 2026, re-checked on 2026-09-26.

This document merges three designs. The base is the judges' unanimous winner, **semantics-first**. Grafts come from **attestation-first** and **product-first**, and both fatal flaws the judges found are fixed.

Evidence tags:
- **[M]** means measured in a spike on 2026-09-26 under the pin.
- **[U]** means unverified.

Spike artefacts *(scratch-only)* were kept in a private scratch area, in three directories named semantics_first, attest and product. Every figure marked [M] comes from them. The standing battery of §E is the one spike output that M0 rebuilt in the repository, as `corpora/strict_battery/`.

---

## 0. The decision in five sentences, and the trust structure

1. **Grammar.** A document is in the **strict tier** iff its whole closure parses in a *whitelist* grammar `L_S`, and its exact *configuration* (class, ordered package loads with options, and the preamble definers between them) has a contract that was **generated and solo-attested under the pin for that configuration**.
2. **Decider.** Inside the strict tier, an extracted Coq decider `decide` returns PROVEN READY or PROVEN NOT-READY (with reason and location). It is proved equal, in both directions, to a separate **declarative** semantics `Runs`.
3. **Faithfulness.** `Runs` models real pdflatex. That modelling is a *named* hypothesis `Faithful`, never an axiom. It is attested per rule and per contract entry by generated probe documents, and by a release-blocking generated differential.
4. **Composition.** Per-package contracts, and anything built by composing them, feed only a **prediction** layer. That layer can print PENDING or LIKELY-*, and can **never print PROVEN**. This fixes the fatal flaw shared by attestation-first and product-first: `revtex4-2` + `tabularx` compiles with rc 0 when only the preamble is loaded, and fails with `! Extra \or.` as soon as the environment is used [M].
5. **Heuristics.** Everything else is the heuristic tier (today's pipeline, relabelled) or FOREIGN. Heuristic code never changes a PROVEN verdict.

**Trust structure** (the owner's three layers, made explicit):

| layer | what it is | how it is established |
|---|---|---|
| (1) semantics | `Runs C σ toks o`: an inductive relation, one constructor per construct × failure mode, each tagged with probe ids | human-reviewed Coq |
| (2) exactness | `decide C d = ProvenReady <-> Runs … Compiles`, and `= ProvenNotReady r l <-> Runs … (Fatal r l)` | **Coq proof**, `Print Assumptions … Closed` |
| (3) faithfulness | `Faithful oracle C`: for every strict `d`, `oracle(d)` compiles `<-> Runs C … Compiles` | **not provable**. Attested by solo probes and the generated differential, and enumerated in the trusted base (§G.2) |

The bridge corollary `strict_ready_iff_pdflatex : Faithful oracle C -> in_strict C d -> (decide C d = ProvenReady <-> oracle_ok d)` takes `Faithful` as an explicit **premise** (a `Definition`, not an `Axiom`, and not a `Section` `Hypothesis`, which would vanish into a ∀-binder on `End`). As a result:
- the existing `Print Assumptions … Closed` gate still holds;
- a new gate checks the corollary's *statement* textually, so that `Faithful` is its **only** non-structural premise;
- the *body* of `Faithful` is pinned too (OPEN-121 final review, MEDIUM-1). A pinned statement cannot see what a premise means: the review redefined `Faithful` as `oracle_ok (render d) <-> decide C d = ProvenReady`, which turns the corollary into decide = decide, and coqc printed the same pinned statement with `Print Assumptions` still Closed. `check_print_assumptions.py` now pins coqc's `Print Faithful` (the elaborated body) AND, because `Print` shows the shortest unambiguous name and a shadow `Module Semantics` placed on Bridge.v's Require line still printed `Semantics.Runs` (the re-review's MEDIUM-1, C-87), asks the KERNEL `eq_refl : Faithful = <body>` with every name fully qualified, in a file that Requires `Bridge` without Importing it; and check 10 of `check_strict_kernel.py` pins the source text, requires the body to mention `Runs` and none of `decide`/`run`/`step`, and forbids any other definer in any Coq SENTENCE of `Bridge.v` (only the pinned Require sentence, `Faithful` and the two bridge Corollaries). All arms are MEASURED to fail on the review's redefinition, and the convertibility and sentence arms on the re-review's shadow module; the textual arm has four registered kill-tests. The STATEMENTS are pinned the same way since the second re-review (HIGH-1, C-88): a shadow `in_strict_doc := False` defined in Bridge.v after `Faithful` made the corollary vacuous while `Check` still printed the pinned statement, and it evaded check 10 twice (a `Time` prefix; a Definition between `(* "(*" *)` and `(* "*)" *)`, which Coq reads as two comments). Now: both corollaries are Closed-checked and their types are checked by kernel conversion against fully qualified statements (Require without Import); `Print Module Bridge` must list exactly `Faithful` and the two corollaries; and check 10 lexes strings inside comments as Coq does, forbids any `"` in Bridge.v, strips control prefixes (`Time`, `Timeout n`, `Redirect`, attributes, ...) before its keyword scan, and PINS the whole comment-stripped code of Bridge.v sentence by sentence (an allow-list: any sentence not on it fails, whatever its keyword). MEASURED: every arm fails on the two mutants of that review, on the plain shadow, the `Time Notation` shadow and the comment-string `Module Decide` shadow; the clean tree passes; three more kill-tests.

**What the theorem covers, and what it does not.** `Faithful` and the bridge corollary are about READY iff compiles, and nothing else. The reason and line of a PROVEN NOT-READY are exact with respect to `Runs` (`strict_decider_exact`, the `Fatal r l` direction), but no theorem connects `Fatal r l` to pdfTeX's first error message or its line: that is attested EMPIRICALLY, by the rule probes and the generated differential, which compare message class and line (line only for the classes that have an l.N; E0 has none) and report 0 disagreements. "A wrong reason or location counts as `strict_wrong`" (§E North Star, ADR-012 decision 6) is a claim the probes and the differential check, not a claim of the theorem.

This repairs the graft from attestation-first. Its proposal, "Print Assumptions lists exactly `faithful`", only works if `faithful` is an `Axiom`, and that would break the Closed gate.

---

## A. The strict subset, exactly

### A.1 Membership: `in_strict C P` (decidable, proved `in_strict_dec`)

A project `P` is STRICT with respect to contract `C` iff all six conditions hold.

1. **Closure.** Every file pdflatex reads as LaTeX parses under `parse C` into `L_S`. That means the root, each `\input`/`\include`/`\subfile`/`\import` target with a *literal* path argument, and the `.bbl` when `\bibliography` is used (graft from product-first; 16/51 ceiling papers have Turing boilerplate in the `.bbl` [M]).
   - The closure is resolved by the modelled kpathsea rule over a file-system snapshot `FS : path → option bytes`.
   - A literal path that does not exist is **not** an exit from the tier. It is the decided fatal E10.
   - This will close OPEN-024 by construction in the strict tier once strict verdicts exist (M2/M3); the heuristic tier still admits it, and M0 records one such document in the battery, `corpora/strict_battery/e12_fontspec_in_input_child/` (`docs/v27/PROJECT_STATE.md` row OPEN-024: T3 sees only the root; `check_ready_to_compile` in `latex-parse/src/compile_contract.ml` reads the root, while `read_closure_source` in the same file is used only for probes).
2. **Configuration attested.** The configuration key is: class + options + sha256, ordered loads + options + sha256, the preamble definer items interleaved with them, and `pdflatex.fmt` sha256. `C` for that key must have `status = attested` and `load_outcome` recorded (§B).
   - Vendored `.cls`/`.sty` files enter by **content hash** like any other file (41/200 sample-2 papers ship their own class [M]). Whether they are admitted at all is an owner decision (§H).
3. **Use-based coverage** (graft from product-first). The tier depends on what the document *uses*, not on everything its packages define.
   - Every control sequence, environment, counter, active character, non-ASCII code point, key and file reference *used* must have a closed-world answer in `C`: either a solo-attested signature for the (mode, context) of the use, or `Undefined`, which is itself the decided fatal E1.
   - A name that is defined but whose signature is not attested in that (mode, context) is **outside** the tier. It is never guessed.
   - Loading tikz without using it can stay strict. This is sound here and was not in product-first, because the *configuration trace* (not a per-package overlay) has already recorded tikz's hooks, catcode changes and `load_outcome`.
4. **Standard catcode regime.** No production exists for `\catcode`, `\makeatletter`, `\def`, `\let`, `\csname`, `\expandafter`, primitive `\if*`, `\write`/`\openout`/`\write18`, `\newif`, `\loop`, `\ifthenelse`, `\whiledo`, `\foreach`, `\ExplSyntaxOn`, `\NewDocumentCommand`, or `@`-names.
   - Active characters introduced by the configuration (babel french makes `! : ; ?` active, ngerman `"`, spanish `" < >` [M]) come from the contract's `catcodes` field. Each one either has a signature or is out of the tier.
   - Verbatim constructs (`\verb`, `verbatim`, `\url`) are productions with their own lexical rule, admitted at top level only.
5. **Layout-independence side conditions** (graft from attestation-first). These make page-builder fatals structurally impossible rather than modelled.
   - At most `k_float` floats between flush points. `k_float` is read from the traced `\@freelist`, not hand-typed.
   - No float or `\marginpar` inside a box.
   - Dimen arguments are literals, or a length register times a literal (no arithmetic).
   - Anything newly found to depend on layout becomes another side condition, never a guess.
6. **Bounds.** Size, nesting depth and user-macro expansion size stay within constants read from the pin. Capacity overflow is a modelled fatal.

A project that fails a condition gets `why_not_strict` reasons (§D) and goes to the heuristic tier. `\write18`, `\directlua` and shell-escape go to FOREIGN.

### A.2 The grammar Coq models

The lexer works bytes → tokens under the fixed catcode table plus the contract's active characters. It strips comments exactly as TeX does, and turns a blank line into `par`.

The lexer must be byte-level. The one false-READY in the semantics-first differential was an empty inline `$$`, which lexes as display math [M].

```coq
Inductive node :=
 | NText (w : list byte) | NUni (cp : nat) | NSpace | NPar
 | NGroup (b : list node) | NStrayClose
 | NMath (k : math_kind) (b : list node)                 (* $ \( \[ $$ *)
 | NScript (up : bool) (arg : node) | NAmp | NCr (opt : option dimen)
 | NCmd (cs : name) (args : list arg)                    (* shape read from C *)
 | NEnv (e : name) (args : list arg) (b : list node)
 | NVerb (k : verb_kind) (bytes : list byte)
 | NInclude (p : path)
 | NDef (d : user_def)        (* \newcommand \renewcommand \providecommand \newenvironment
                                 \renewenvironment \newtheorem(4 forms) \theoremstyle
                                 \DeclareMathOperator \newcounter \setcounter \addtocounter *)
with arg := AReq (t : argty) (b : list node) | AOpt (t : argty) (b : list node) | AStar
with argty := TyText | TyMath | TyInherit | TyLabel | TyFile | TyCounter | TyDimen
            | TyNumber | TyKV (family : name) | TyUrl | TyEnvName | TyCsName | TyKeyExpanded.
Record doc := { d_class : load; d_pre : list pre_item; d_body : list node;
                d_has_end : bool; d_trailing : list byte }.
```

- **Undefined cs.** An undefined control sequence parses as `NCmd cs []`. The semantics stops at the first fatal, so NOT-READY verdicts never need argument shapes.
- **Argument types.** The typed-argument lattice (`argty`, graft from attestation-first) is attested per position. A payload that does not lex as its type puts the document outside the tier. It does not produce a guessed fatal.
- **Expanded keys.** `TyKeyExpanded` carries the `\selectlanguage{\english}` class: a control sequence inside an expanded key is decided E1 [M].
- **User macros.** They are admitted only through `NDef`. Bodies must be in `L_S` and the catalogue must be acyclic, which reuses `merge_acyclic` (`proofs/UserExpand.v`, line 62).
  - **Do not reuse** `user_expand_deterministic` (`proofs/UserExpand.v`, line 78); it is the tautology `input = input`.
  - New theorems are needed: `expand_terminates` and `subst_preserves_L_S`.

---

## B. Contract schema, generation, attestation

### B.1 Two kinds of contract, only one of which can prove

| kind | key | produced | may feed |
|---|---|---|---|
| **configuration contract** | full configuration key (A.1.2) + pin | a trace of that exact configuration plus solo use-site probes, on demand and cached by hash | PROVEN verdicts |
| **package contract** | (class or package, canonical option set, load-context class) + pin | offline farm | prediction (`PENDING (predicted)`), heuristic `LIKELY-*`, and seeding which probes to run |

The two-kind split is forced by measurement:
- 200/200 sample-2 configurations are distinct, even ignoring options and order [M] (attestation-first counted 199 distinct (class, package-set) vectors).
- Composition is not free: 5 packages loaded together give 51 names that appear only in the combination, and 6 names that exist singly are absent [M].
- `revtex4-2`×`tabularx` breaks only at use [M].
- Most pairs do overlay (361/380 = 95.0% [M]), so predictions will usually be right. "Usually right" still cannot carry the word PROVEN.

### B.2 Fields: every one is generated, none is hand-listed

| field | content | generation (under the pin) | attestation |
|---|---|---|---|
| `pin` | engine banner, TL year, `pdflatex.fmt` sha256, tlpdb revision | `pdflatex --version`, `kpsewhich`, sha256 | stored |
| `kernel_names` | complete set of format-level names | **INITEX re-run of `pdflatex.ini` under `\tracingassigns=1`**: 26,369 names, 1,552 public, 349 `u8:` slots, 20.6 s [M] | closure self-check (below) |
| `load_outcome` | `Ok` or `Fatal{msg, load_index}` | the generation run itself: configuration + `\begin{document}\end{document}`, `-halt-on-error` | this compile *is* the attestation. `llncs`+`amsthm` → `\proof already defined` [M]. `cleveref` before `hyperref` → load-order fatal [M] |
| `files_read`, `lazy_files` | files read at load, and files read on first use (e.g. `\mathbb` → `umsa.fd`) | `pdflatex -recorder` `.fls` of the load, and of each positive probe, minus the empty-document baseline | re-run with the file hidden; the expected fatal must appear |
| `defined_names` (closed world) | every name whose final meaning at body start differs from the kernel | pass 1: `\tracingassigns=1` over `\documentclass…\begin{document}`, with `\typeout` load boundaries and `max_print_line=1000000`. Pass 2: `\ifcsname`-guarded `\meaning` dump **after `AtBeginDocument`** (65 names assigned during load revert by body start [M]) | **closure self-check**: `\ifdefined` on a random 1% of the kernel∪contract universe plus every name the document uses must agree with membership. Any mismatch blocks the contract. As built (§I.2) the universe is also checked against TeX's own hash-table count, and the per-document part is M2's |
| `meaning` | `Undefined \| Relax \| Primitive \| Char \| MathChar \| Register \| Macro{long, protected, robust, ltcmd-spec}` | pass 2 dump, a lazy closed-world memo (negatives are answers too; this settles ROADMAP G1's polarity split) | from the dump |
| `signature(name, mode, context)` | `allowed : Ok \| Fatal msg`, plus `args : [kind ∈ {req, opt, star}, argty, long]` | Candidates come from the ltcmd spec in the meaning, the `\@protected@testopt`/`\@ifstar` idioms, and the outer-sentinel arity probe (`\outer\def\STOP{}`, then `\cs{x}^n\STOP`). **A shape read is a hint, never attestation**: static `#n` arity disagreed with behavioural arity on **121/405 = 30%** of macros [M]. Payload lattice: `{a}`, `{1pt}`, `{equation}`, `{example-image}`, `{http://x}`, `[width=1cm]`, a counter name | **solo** `-halt-on-error` probes, **one variable each**, classified by *error class*, not rc. Positive probes: a well-typed use compiles, in T, in M, and in each context. Negative probes: wrong mode, `\par` in the argument (long-ness), a missing argument. **Batched probes are triage only**: batch-vs-solo polarity agreement was 142/143 [M]. A 15 s timeout guards against the MetaPost-support hangs [M] |
| `environments` | begin-args, body mode, the context it pushes (list, float, alignment n, theorem, display) | `\X` and `\endX` both in `defined_names`, plus the same probe families | solo |
| `definer_rules` | pin-level semantics of each admitted definer | a probe table (13 probes [M]). Plausible hand rules are false at the pin: `\newcounter{lemma}` followed by `\newtheorem{lemma}` **compiles**, and `\newcommand` on a `\relax`-meaning name compiles [M] | the table is the attestation |
| `decl_templates` | per declaration command and **owner combination** (kernel / amsthm / amsthm+thmtools / ntheorem): the names it defines, `errors_if_defined`, and `requires` | fresh-name probe (`\newtheorem{zzq}[section]{Zzq}`), then a meaning diff of the zzq family, then collision probes. The amsthm+thmtools template differs, and it reproduces `Command \c@lemma already defined` [M] (graft from product-first) | collision matrix |
| `load_delta[k]`, definer kind | names assigned while load k ran, with kind `new \| renew \| provide \| def` | pass 1 per-load slices. The kind is found by a **sensitivity probe** (insert `\newcommand{\n}{}` before load k), run only for names that a user defines before a later load | solo |
| `counters` | `c@X`, with `\theX` and the `cl@X` reset lists | from `defined_names` and the meanings | `\stepcounter{X}` probe |
| `key_families` | `\KV@<fam>@<key>`, kvoptions, `\ds@<opt>` | from the trace: Gin 31, Hyp 161, Field 85 keys [M] | one misspelled-key probe per family (`keyval Error: widht undefined` [M]) |
| `catcodes` | the catcode table at body start, where it differs from the base | `\the\catcode` dump for bytes 0–255 inside the body [M] | from the dump |
| `unicode` | code points with `u8:` defined, per mode | `\ifcsname u8:…` sweep [M]: `é` is defined; `П`, `≈`, `α` are not | sample one probe per block |
| `graphics` | the extension search list | final meaning of `\Gin@extensions` [U] | missing-file probe |
| `limits` | grouping levels, input levels, `k_float` | pin constants and `\@freelist` [U] | a probe at the bound |
| `provenance` | generator sha, per-entry probe `.tex`/`.log` hashes, file sha256 list | written by the generator (as built, §I.2: a semantic generator version, not a source sha) | a byte-identical regeneration gate |

**Validity rules:**
- Nothing is hand-listed; the generator is the only writer.
- Any change to a file hash or the format hash invalidates the contract (VC1).
- `complete = true` only if the closure self-check passes and there was no unexpected load `!`.
- Signature coverage need **not** be complete, because an unattested use simply leaves the tier. Completeness of the *name set* is what makes E1 exact.

### B.3 Spike feasibility (measured, loaded laptop, load average 24–300, so pessimistic)

| step | measured cost |
|---|---|
| trace + dump of one configuration | 0.2–1.2 s; real 14-package paper 2506.11486v1: 2.26 s, 10,428 names assigned, 2,192 new user-facing |
| solo use-site probes | 0.11 s each on 6 workers; 170 probes / 40 commands in 19.2 s |
| median distinct body cs to probe | 85 (p90 143), so a new configuration takes a few seconds |
| triage batch probing | 24,768 probes / 2,064 names, 953 s |
| pair farm (prediction layer) | 380 ordered pair dumps in 135 s on 8 processes; top-80 pairs ≈ 6,400 compiles, one night |

Shape distribution over 2,192 new names: 1,717 plain-undelimited, 238 register/char/font, 59 robust, 24 ltcmd, 18 with an optional argument, and **136 (6.2%) delimited/lookahead/other**. Those 136 are outside the tier unless probes attest them.

### B.4 Oracle protocol (attestation and metrics use the same predicate)

READY means rc 0 under `-interaction=nonstopmode -halt-on-error`, a ≤3-pass fixpoint, default restricted shell-escape, **and a PDF produced**. An explicit fatal code E0 covers "rc 0, no PDF" (the empty body; `\label` alone [M]).

**The timeout is part of `oracle_ok`.** A run that does not finish within the timeout is not "compiles", so the predicate `Faithful` speaks about is "rc 0 and a PDF, within the timeout". The timeout is PER PASS: `_oracle.run_to_fixpoint` calls `run_once` with it for each of up to 3 passes and once more for the confirming pass, so the wall-clock bound on `oracle_ok` is (passes+1) × 300 s, at most 1,200 s. The harnesses (`strict_differential.py`, `gen_strict_signatures.py`) use 300 s, and `_strict_s0.grade` now defaults to the same 300 s (`GRADE_TIMEOUT_S`; it was 60 s) so an ad-hoc caller cannot get a flaky disagreement from a tighter one. The slowest documents measured INSIDE the capacity bounds (OPEN-121 final review, under the pinned oracle, READY on both sides): 6,666 forced pages (`x \par \break` × 6,666) at 47–52 s, and 19,995 `\mathstrut` in one display at 54.7 s, the latter under machine load. The margin to 300 s is about 5.5×; that no in-bounds document is slower is INFERRED from these adversarial searches, not proved.

**`oracle_ok` is clock-independent on the fragment: MEASURED, and enforced by a rule (OPEN-118 known limit (b), 2026-09-28).** The protocol sets `SOURCE_DATE_EPOCH=0` but not `FORCE_SOURCE_DATE`, so `\year`, `\month`, `\day` and `\time` follow the container's clock, and a document that branches on them could grade differently on different days. That would make `Faithful` (bytes → outcome) a claim about the day of grading, not about the bytes. The experiment graded the documents under three clocks through `_oracle.run_to_fixpoint` itself: the protocol as it is (the real clock, 2026-09-28/29), and two forced dates that differ in every field (1971-02-03 04:05 and 2049-11-28 23:59 UTC, each with `FORCE_SOURCE_DATE=1`). It used a scratch-only wrapper around `graded_env`, and the protocol was not changed. The documents were every probe-family document of the 130 admitted names (130 × 58 = 7,540), the 24 interleaving documents, the 510 graded rule probes, and the first 600 documents of the v2 differential (seed 2). Every regenerated differential document matched its recorded `tex_sha256`. That is 8,557 unique documents and 18,622 fresh grades, 0 of them infrastructure failures or timeouts. For the 7,049 signature-only documents, the normal-protocol grade came from their committed evidence, which was graded on an earlier day. Across the three clocks, 0 documents differ in rc, PDF, first error, line, or the PDF's bytes with its dates and `/ID` removed (for the 7,049 documents whose normal grade is committed evidence, which records no PDF digest, the byte comparison covers the two forced clocks only). Each of the 1,601 committed records that has a fresh normal-protocol grade (1,508 documents, some recorded more than once) matches that grade exactly. Positive controls show the instrument sees a clock dependence: `\ifnum\year>2025 \undefined\fi` is rc 1 today and in 2049 but rc 0 in 1971, and `\ifnum\time>600` behaves the same way. `\today` changes only the PDF. Rule R-CLOCK of `check_strict_kernel.py` (check 11, pure, three kill-tests) keeps this true for the next signature file. The date is not pdfTeX's only per-run input: the review of this experiment MEASURED `\pdfrandomseed` seeded from the real time on every run (so `\pdfuniformdeviate`/`\pdfnormaldeviate` differ per run), the timer `\pdfelapsedtime`, and `\pdffilemoddate` returning a file's real modification time even with `FORCE_SOURCE_DATE=1`; `\pdfcreationdate` is pinned by `SOURCE_DATE_EPOCH=0`. So the rule covers every RUN-DEPENDENT primitive: it fails if an admitted name is one of `\year`, `\month`, `\day`, `\time`, `\pdfrandomseed`, `\pdfsetrandomseed`, `\pdfuniformdeviate`, `\pdfnormaldeviate`, `\pdfelapsedtime`, `\pdfresettimer`, `\pdffilemoddate` (itself or `\let` to one), or if its recorded expansion closure (the same one R-INERT uses) reaches one of them or one of the kernel file's `date_dependent_names`. Only these primitives are hand-listed. No admitted closure reaches any of them today. Known limits: the screen limit of §I.4 (a name made of non-letter characters is not followed), and a name BUILT at run time (`\csname year\endcsname`) is not followed either; both are closed only by ADR-013's token-exact closure.

**Which pdflatex is the oracle (owner decision of 2026-09-26, ADR-012 decision 7).** The oracle is frozen as CI's digest-pinned TeX Live image, the `TEX_IMAGE` digest in `.github/workflows/tex-oracle.yml`, run locally through a container. The laptop TeX Live is not the oracle, so the earlier plan to repair its pdfmanagement orphan files is superseded. Every graded artefact is re-graded once under the image and the diffs are published as an oracle-baseline change; sample 3 is drawn and graded only after that. The [M] figures in this document were taken under the laptop pin and are pre-baseline.

**Implemented 2026-09-27 (OPEN-118).** Attestation and metrics both call `scripts/tools/_oracle.py`, the only code allowed to start pdflatex (`check_oracle_pin.py` enforces this). It runs the image through a container locally and natively only inside the image in CI, and it fails rather than fall back to a host TeX Live. Each run records rc, the number of passes and whether a PDF was produced, so the E0 predicate above can be evaluated. Every artefact records the image digest, the architecture and two fingerprints of the TeX tree (the package database and a per-package revision digest of the macro layer), because the version banner does not pin the macro layer: the laptop printed the pinned banner while differing from the image in 190 packages. The re-grade under the image moved no cell of any re-graded artefact. The M1 contract generator must use the same entry point and store the macro-layer fingerprint in each contract's `pin` field (§B.2).

---

## C. Formal semantics, decided failure modes, the Coq statement, reuse

### C.1 State

`σ = {phase ∈ Pre|Body|Ended; mode ∈ V|H|R|M|D; ctx : list context; envstack; group_depth; defs : name ↦ entry (C ⊕ user defs); counters; labels; script_pending; align_cols; list_depth; floats_since_flush}`

**Contexts are dynamic, not lexical.** `\item` inside `\footnote` inside `itemize` compiles [M]. That case was a false-NOT-READY in the spike.

### C.2 `fatal_reason`: one constructor per row, each tied to a probe family

| code | failure | decided from |
|---|---|---|
| E0 | rc 0 but no PDF (no typeset material) | body contents |
| E1 | undefined cs, including one inside an expanded key (`\selectlanguage{\english}`, `\ref{\undefinedfoo}` [M]) | `defined_names` closed world + user defs |
| E2 | undefined environment | `\X`/`\endX` |
| E3 | mode violation: math-only in text, `^`/`_` in text, `\\` in vertical mode, `&` outside alignment, context-restricted (`\tag`, `\caption`, `\item` outside a list) | `signature.allowed`, `ctx` |
| E4 | double superscript/subscript | kernel rule [M] |
| E5 | stray `}`; `\begin{a}…\end{b}`; missing `\end{document}`; **a surplus `{` at EOF is NOT fatal** (rc 0 [M]; OPEN-010 in `docs/v27/PROJECT_STATE.md`) | stack discipline |
| E6 | `\par` in math (including a blank line inside `align` [M]) or in a non-long argument | `long` flags |
| E7 | missing mandatory argument | `args` |
| E8 | definer clashes (`\newcommand` on a defined non-`\relax` name or an `\end…` name; `\renewcommand` on an undefined name; `\newenvironment`/`\newcounter`/`\newtheorem` on an existing one; unknown `within` counter; `\DeclareMathOperator` on an existing name), class/package-vs-user (`\c@theorem` via llncs [M]) | `definer_rules`, `decl_templates`, `load_delta` |
| E9 | counter operation on an unknown counter | `counters` |
| E10 | missing `\input`/`\include`/`\includegraphics` target (after extension search) | FS snapshot, `graphics` |
| E11 | Unicode code point without `u8:` in its mode | `unicode` |
| E12 | configuration fatal: class vintage, missing `.sty`, option clash, class×package, load order; `\usepackage` after `\begin{document}`; preamble-only command in the body; typeset material in the preamble | `load_outcome`, flags |
| E13 | list depth exceeded, bad key, ill-typed dimen/number/counter argument | `limits`, `key_families`, `argty` |
| E14 | capacity overflow | `limits` |
| W | undefined ref/cite, duplicate label: **warnings, not fatals** [M] | reuses `L0Pass` (`proofs/LexerFaithfulStep.v`: `converged_at_two` at line 838, `warns_iff_unresolved_two` at line 967) |

**Multi-pass.** The lemma `fatal_aux_independent` states that in `L_S` the aux file feeds only ref/cite *text*. So one-pass fatality equals 3-pass fatality. `\ref` in numeric contexts has no production.

### C.3 Theorems (targets; none exist yet)

```coq
Inductive Runs (C : contract) : state -> list node -> outcome -> Prop := ...  (* declarative, probe-tagged *)
Theorem runs_deterministic : forall C s b o1 o2, Runs C s b o1 -> Runs C s b o2 -> o1 = o2.
Theorem runs_total : forall C d, contract_wf C -> in_strict_doc C d -> exists o, Runs C (init C) (flatten d) o.

Theorem strict_decider_exact : forall C bytes d,
  contract_wf C -> parse C bytes = Some d -> in_strict_doc C d ->
  (decide C d = ProvenReady <-> Runs C (init C) (flatten d) Compiles) /\
  (forall r l, decide C d = ProvenNotReady r l <-> Runs C (init C) (flatten d) (Fatal r l)).

Theorem parse_exact   : forall C bytes d, parse C bytes = Some d <-> Derives C bytes d.
Theorem in_strict_dec : forall C d, {in_strict_doc C d} + {~ in_strict_doc C d}.
Corollary no_turing_construct : forall C bytes d, parse C bytes = Some d ->
  ~ In_bytes_as_token turing_primitive bytes.          (* VP1/DetectComplete, now structural *)
Theorem decide_incremental : forall C d1 d2 k, agree_prefix k d1 d2 ->
  decide_from (checkpoint C d1 k) (suffix k d2) = decide C d2.
Theorem strict_fatal_iff : forall C d,
  (exists r l, Runs C _ _ (Fatal r l)) <-> exists ch, channel_fires C d ch.   (* D1 pattern *)

(* the bridge: Faithful is an explicit premise, so Print Assumptions stays Closed *)
Definition Faithful (oracle_ok : project -> Prop) (C : contract) : Prop :=
  forall d, in_strict_doc C d -> (oracle_ok (render d) <-> Runs C (init C) (flatten d) Compiles).
Corollary strict_ready_iff_pdflatex : forall oracle_ok C bytes d,
  Faithful oracle_ok C -> contract_wf C -> parse C bytes = Some d -> in_strict_doc C d ->
  (decide C d = ProvenReady <-> oracle_ok (render d)).
```

`Runs` exists separately from `decide` so that exactness is a real refinement proof and not `decide = decide`. There is a review rule: every `Runs` constructor cites its probe family ids.

### C.4 Existing proofs: reused, retained, retired

| artefact | fate |
|---|---|
| `pdflatex_compile_safe` (`proofs/PdflatexModel.v`, line 1062), `body_token` (line 127, 4 constructors), `project_wf_dec` | **retained unchanged** as the *heuristic* "premise-certified" statistic. A strict verdict never cites them. (product-first's grafting of `BT_fatal` onto these is rejected: it blurs the two tiers) |
| `model_fatal_iff` (`proofs/PdflatexFatalChannels.v`, line 389) | its **proof pattern** (per-channel biconditional, then disjunction) is reused for `strict_fatal_iff` over about 15 channels. `ch_edge` (line 63), proved unreachable for encoder graphs by `encoder_model_fatal_iff` (`proofs/BuildGraphFrontEnd.v`, line 127; OPEN-095), is replaced by E10 over the FS snapshot. `ch_decl` (line 73, always `[]`) is dropped. `ch_body` (line 77) becomes E12/E11 |
| `proofs/BodyTokenFrontEnd.v` | its **method** (Coq bytes model, extraction, byte-identical regeneration via `scripts/tools/regen_body_token_frontend_extract.sh`) is the template for `parse C`. Its label/ref scanners feed W |
| `LexerFaithfulStep.v` (L0Pass) | reused for W and multi-pass |
| `LanguageContract.classify` (`proofs/LanguageContract.v`, line 60), `classify_lp_core_sound` (line 87), `latex-parse/src/unsupported_feature.ml` | kept **only** as heuristic sub-labels (LP-Core/Extended/Foreign). `in_strict` is the new proof boundary; VP1 `DetectComplete` dissolves into `no_turing_construct` |
| `UserExpand.merge_acyclic` (`proofs/UserExpand.v`, line 62), `proofs/UserMacroTermination.v` | reused; `user_expand_deterministic` (`:78`) is not |
| `latex-parse/src/extension_registry.ml`, `over_claims` | kept as policy checks. Positive provides come only from generated contracts |
| extraction | `ExtrOcamlNatInt` precondition (non-negative ints only; OPEN-096 in `docs/v27/PROJECT_STATE.md`) re-audited for the new extract |

---

## D. Verdicts, plumbing, output, real time

### D.1 One type, one renderer (the VD1 idea with a tier coordinate)

```ocaml
type verdict =
  | Proven_ready     of { contract : hash; pin : string; decider : string }
  | Proven_not_ready of { reason : fatal_reason; file : string; line : int; col : int;
                          rule : string; probe : string; contract : hash }
  | Pending          of { predicted : [`Ready | `Not_ready]; missing : attestation list }  (* heuristic *)
  | Likely_ok        of { basis : string (* "premise-certified" *); why_not_strict : boundary list }
  | Likely_fail      of { reasons : Compile_contract.reason list; why_not_strict : boundary list }
  | Foreign          of { construct : string; loc : loc }
```

- **Rendering.** The TIER line's verdict kind is `PROVEN-READY`/`PROVEN-NOT-READY` if and only if the verdict is `Proven_*`. The kind is a fixed token produced only by the renderer; user data (paths, macro names) is quoted verbatim in delimited fields and never rewritten, so a user path may contain the word PROVEN. Enforced by the renderer's structure plus a unit test.
  - Example: `PROVEN NOT-READY main.tex:42:7 \frac is math-only, used in text mode [E3, probe P-MODE/frac, contract 1a2b3c4d]`.
  - Heuristic lines always carry `heuristic — not a proof`.
  - **What PROVEN NOT-READY's reason and location rest on.** The PROVEN in `PROVEN NOT-READY` is the theorem's: pdflatex does not compile (`strict_not_ready_pdflatex`, under `Faithful`). The `file:line:col` and the E-code are exact against `Runs`, but that they are pdfTeX's first error and its line is attested empirically by the rule probes and the differential (0 disagreements on message class and line; line only where pdfTeX reports an l.N, so never for E0), not proved (§0).
- **`why_not_strict`** (graft from product-first) is shown on every non-proven verdict, with up to three reasons and fix-it nudges. Examples: `\def\R{\mathbb R}` → `\newcommand{\R}{\mathbb{R}}`, and "remove unused `\usepackage{foo}`". On sample 2, 17 papers are blocked only by `\def` and have no local style files [M].
- **Exit codes stay as today** (0 = no known blocker, 1 = blocker), so there is no fixture churn. The new flag `--require-proof` exits 4 unless the verdict is `Proven_*`. JSON gains `tier`, `reason`, `loc`, `contract` and `why_not_strict`. product-first's 0–4 exit-code rewrite is rejected.
- Certificate tokens follow A2/C1 (`docs/v27/REALIGNMENT_PLAN.md` §4).

### D.2 Wiring in `Compile_contract.check_ready_to_compile` (`latex-parse/src/compile_contract.ml`)

1. Run `parse C` over the closure.
2. Look up the configuration contract, or request it (§D.3).
3. If `in_strict` holds, run the extracted `decide`; the result is the verdict.
4. Otherwise run today's pipeline (`latex-parse/src/compile_evidence.ml` `verdict_state`, PREMISE-CERTIFIED/REJECTED) and relabel it `LIKELY-*`. Package contracts (B.1) feed this tier from M1 onward.

**The belt runs in shadow and never overrides.** If a `latex-parse/src/compile_gate_checks.ml` detector disagrees with a PROVEN verdict, the verdict stands. The disagreement is logged as an **F-defect candidate**, which blocks release until triaged. product-first's downgrade rule is rejected: it would make the shipped verdict something other than `decide`, and the theorem would stop describing the product.

### D.3 Real time

| event | cost | shown meanwhile |
|---|---|---|
| body keystroke, configuration cached | re-lex the damaged chunk + fold from the nearest `par`/env checkpoint with early cutoff on state equality (`decide_incremental`) | PROVEN verdict, updated |
| preamble edit to a cached configuration | hash lookup | — |
| new configuration | ~2.3 s trace+dump, then solo probes of used names (median 85) at ~0.11 s ÷ workers: a few seconds [M] | `PENDING (predicted …)` from package contracts, labelled heuristic |
| newly typed, unattested cs | one probe batch, then solo confirm, < 1 s [U] | `PENDING` |
| a Turing token typed | same pass (parse failure) | badge flips to `LIKELY-*` with `why_not_strict` |

**Owner-visible consequence.** PROVEN for an uncached configuration needs **pdflatex available to the attestation service**. Only the configuration's preamble and probe documents are compiled, never the body. Without it, the tier is capped at the shipped cache, which is close to 0 because 200/200 configurations are distinct (see §H, decision 1).

---

## E. Measurement

- **North Star.** Strict-tier coverage on a **virgin** sample, `#{PROVEN verdict = oracle} / N`. It is always shown beside `strict_wrong`, which counts false-READY, false-NOT-READY, **and wrong reason or location**. `strict_wrong` must be 0 and is published **with its 95% upper bound**: 0/k ≈ 3/k, which is about 30% at k = 10 (graft from product-first). The docs say that a small k is weak evidence. The false-READY and false-NOT-READY parts of `strict_wrong` are what the bridge corollary covers under `Faithful`; the wrong-reason-or-location part is covered by no theorem and is measured only (the probes and the differential compare message class and line; §0).
- **Exactness evidence is carried by the generated differential**, not by the virgin count.
  - At least 10,000 random `L_S` documents per release are drawn over the attested contracts, weighted toward boundaries (mode switches, arity, clashes, nesting, dynamic contexts), graded by the pinned oracle and reported per E-code.
  - Any disagreement is an F-defect: it blocks the release, adds a CORRECTIONS row, and the affected rule is frozen out of the tier until fixed.
  - Baseline from the spike: 299/300 (1 false-READY, the `$$` lexer case), then 998/1000 (0 false-READY, 2 false-NOT-READY) [M].
  - The differential runs locally or nightly, not in pure spec-drift, because CI has no TeX (the OPEN-101 lesson in `docs/v27/PROJECT_STATE.md`).
- **Two coverage columns.**
  - *cache-only*: close to 0 until farm-scale.
  - *with on-demand attestation*: the honest strict number.
- **Heuristic block.** In `docs/v27/PROJECT_STATE.md` §1, generated by `scripts/tools/gen_project_state.py`: "heuristic: premise-certified 88/200 (s2), certified-but-fails 8/102", plus LIKELY-FAIL precision and recall. It is never called proven.
- **Standing regression battery** (graft from product-first). Today's CLI prints `READY … PREMISE-CERTIFIED tier=lp-core` on **9 of 12** minimal failing documents [M]:
  - `\frac` in text, undefined cs, undefined env, `$\frac{1}$`, `\newcommand{\text}`, missing graphic, `≈`, cleveref-before-hyperref, blank line in `align`.
  - M0 re-creates them as fixtures: only one spike document survived *(scratch-only)*, so they were rebuilt from their descriptions. They live in `corpora/strict_battery/`, graded under the pin by `scripts/tools/gen_strict_battery.py`, which writes `corpora/strict_battery/manifest.json`.
  - Every one must become PROVEN NOT-READY with the right E-code by M3.
- **Sample hygiene.** Sample 2 has now been used for configuration statistics, ceiling sets and package ranking, so it is **design-seen**. Rankings use frame∖eval. The headline number comes from **sample 3** (frame offset 720, ranks 721–920; ranks 401–600 were planned here first, but offsets 400–719 are the OPEN-110 fixer window, so OPEN-118 moved it), drawn and graded only after every graded artefact had been re-graded under the frozen oracle image (ADR-012 decision 7). It is sealed for measurement only (OPEN-119): it is never used for configuration statistics, ceiling sets or package ranking. Sample 4 is held in reserve.
- **Expected trajectory (honest).**
  - M0 publishes 0/200.
  - Upper bounds from sample 2, based on root-only or regex scans: 51/200 Turing-free with no local style; ~11–22/200 at top-80 packages with article/amsart; 13/200 after intersecting with LP-Core text. Construct-level greedy: 500 constructs → ≤8, 1,000 → ≤15, 2,000 → ≤24 [M].
  - **No real virgin paper has yet been shown in the strict tier.** The published proven number goes 88 → 0 and then grows.

---

## F. Build plan

> ⚠ **SUPERSEDED from M1 slice 2 on by [ADR-015](adr/ADR-015-static-proven-tier-on-translated-engine.md)
> (accepted 2026-09-29; banner added 2026-09-30, the plan below is unchanged history).** The per-name
> admission of M1 slice 2 (OPEN-120) and M3's structure, definer and on-demand attestation plan are
> replaced by ADR-015 D2 (a Coq translation of the pinned pdfTeX, names admitted by a Coq-proven sound
> abstract interpreter). The plan of record is ADR-015 D3's foundation spike (OPEN-123). M2's kernel on
> `main` is not faithful and must not be wired as it is (OPEN-124).

Each milestone ships alone. The measured effect is stated as the thing to publish.

| # | size | deliverable | proof work | measured effect to publish |
|---|---|---|---|---|
| **M0** | S (days) | ADR-012; three-tier docs (proven-exact / heuristic / impossible) incl. `COMPILATION_GUARANTEE.md`; `verdict` type + renderer; all READY → `LIKELY OK (heuristic; premise-certified)`; `--require-proof`; **closure-scoped boundary scan** (`Unsupported_feature` over the closure of `latex-parse/src/compile_contract.ml` + the A.1.4 additions + local `.sty`/`.cls` detection) with `why_not_strict` + nudges; 13-doc battery as fixtures; PROJECT_STATE heuristic block | `in_strict := false` stub | proven 88 → **0/200**; PROVEN-that-fails 8/102 → 0 (vacuously); boundary reasons on s2 (105 Turing, +44 local style [M]); **0 exit-code / fixture changes** |
| **M1** | M | contract generator v1 (`gen_contract.py`: INITEX kernel, config trace + final dump, `.fls`, solo probe harness with timeouts, typed lattice, key families, catcodes, unicode, decl templates, closure self-check); package contracts for top classes + packages ranked on frame∖eval; `check_contracts_reproducible.py` (byte-identical, nightly/local) | none | heuristic LIKELY-FAIL gains load-order, class×package, option-clash, fontspec-under-pdfTeX, unicode classes: precision/recall on frame; battery: how many of the 9 flip to LIKELY-FAIL; batch/solo agreement; closure self-check pass rate |
| **M2** | M | Coq kernel `L_S0`: `proofs/Strict/{Syntax,Contract,Semantics,Decide,FrontEnd}.v`: text, par, groups, math, scripts, `NCmd` with contract signatures, E0–E7, E11; extraction + regen gate; configuration = `article`, no packages; generated differential v1 | `runs_deterministic`, `strict_decider_exact`, `parse_exact`, `in_strict_dec`, `strict_ready_iff_pdflatex` (+ premise-shape gate), all Closed | differential ≥10k docs, 0 disagreements per E-code; battery cases expressible in kernel decided; real virgin coverage ≈0 (published anyway) |
| **M3** | M–L | structure + definers: environments with dynamic contexts, lists, theorems, `NDef` family with `definer_rules`/`decl_templates`, acyclic user macros, counters, keys (`TyKeyExpanded`), E8–E10, E12–E13, `fatal_aux_independent`; **on-demand configuration attestation service** (cache by hash) replacing the fixed `article` config; closure-wide parse | `expand_terminates`, `subst_preserves_L_S`, `strict_fatal_iff`, `fatal_aux_independent` | **first real strict number** on sample 3, both columns + UB95; full 13-doc battery PROVEN NOT-READY with right E-code; `\c@theorem`-via-class and `\selectlanguage{\english}` decided when in grammar |
| **M4** | M–L | sub-grammars: tabular/array column specs, `&`/`\\` counting, graphics extension search, layout side conditions, capacity limits | alignment rules | Δ strict coverage; packages/constructs ranked by **marginal** strict coverage |
| **M5** | M | real time: `decide_incremental` into the serving path + LSP badges/nudges; `PENDING (predicted)` from package contracts; latency gate (ROADMAP §1 Principle 9 bands; OPEN-104 style recorded cold/warm) | `decide_incremental` | keystroke latency cold/warm; prediction-vs-attestation error rate (revtex×tabularx must be predicted wrong-and-caught, never PROVEN) |
| **M6** | L (farm) | prediction layer at scale: pairwise ordered use-site matrix for top-N (~0.5M probes, ~13 CPU-h [U]); `.bbl` dialect (bst boilerplate as hash-attested inert blocks) | none | prediction accuracy; `.bbl` unlocks up to 16/51 ceiling papers [M] |
| **M7+** | per item | grammar widening by measured marginal coverage (algorithm/algorithmic, cleveref, natbib, …); each widening = rules + probes + ≥1000 differential docs | per new primitive | Δ coverage at 0 disagreements |

**Ordering rationale.**
- The honesty fix ships first (M0).
- The contract generator is a data-only milestone that already improves the heuristic tier (M1), before any proof. The first proof milestone then consumes real, attested contracts.
- Real-time can move ahead of M4, since the decider is a fold.

---

## G. Risks and the trusted base

### G.1 Risks

1. **Faithfulness is empirical.** A finite probe set stands in for all argument contents, which is a parametricity assumption. The spike found 3 F-defects in 1,300 docs over 28 commands. Expect more, especially in moving arguments (fragile commands in `\section`/`\caption`), tabular cells, and aux/TOC round-trips.
   - Mitigations: context-typed argument kinds; probes that discriminate error class; a release-blocking differential; freeze-on-disagreement.
2. **Coverage is small for a long time** (0 → ≤24/200 upper bounds; tikz is in 68/200, algorithm in 57/200). The number must be published anyway.
3. **"Without compiling" weakens.** PROVEN needs on-demand attestation because 200/200 configurations are unique. This is an owner decision.
4. **Composition is unsound**, as measured. It is contained by construction: package contracts cannot reach PROVEN.
5. **Oracle definition.** rc vs PDF, 3-pass, restricted shell-escape (OPEN-053), and the pdfmanagement orphans in the laptop TeX Live, which ADR-012 decision 7 retires by freezing the oracle as CI's digest-pinned image. A contract is only as good as the oracle it was generated under.
6. **TL drift.** A `tlmgr update` invalidates every contract (keyed by the fmt hash), as intended; regeneration is mechanical.
7. **Generator bugs.** Every spike stage needed a fix: log wrapping, control-word space eating, a missed robust shape, BSD `seq`, zsh `echo`. Mitigations: the byte-identical regeneration gate, the closure self-check, and adversarial review of the generator first (C-30).
8. **Proof engineering.** A contract-parameterised `parse_exact` is hard. There are also the `nat`-pow Qed blow-up and extraction-to-`int` preconditions to handle.
9. **Non-eqtb state** (streams, global boxes, `\pdf*` objects) is not traced by `\tracingassigns` [U]. Configurations whose `load_outcome` depends on it are caught by the load compile. Use-time effects are caught only by probes and the differential.

### G.2 Trusted base (listed verbatim in the docs)

Anything a PROVEN verdict depends on that Coq does not check:

| # | component | status |
|---|---|---|
| T1 | pdfTeX binary, `pdflatex.fmt`, the TL2026 tree at the pin (hash-pinned in every contract) | the oracle; trusted by definition |
| T2 | **`Faithful`**: each `Runs` rule and each contract entry models pdflatex | named Coq premise; attested by solo probes + differential; never proved |
| T3 | the oracle protocol (flags, ≤3 passes, PDF required, shell-escape mode) | written down; the same predicate for probes and metrics |
| T4 | contract generator (trace/`.fls`/`\meaning` parsing, probe design, error-class classification, solo confirmation, timeouts) | regeneration-diffed; closure self-check |
| T5 | contract DB integrity and the JSON → Coq-record reader | content-hashed; reader to be extracted and proved [U]; until then trusted |
| T6 | FS snapshot + the kpathsea / `\graphicspath` / extension-search model | trusted |
| T7 | byte source (file reading, UTF-8 handling before `parse`) | trusted |
| T8 | Coq kernel, extraction (`ExtrOcamlNatInt` non-negativity, OPEN-096), OCaml compiler/runtime | trusted |
| T9 | verdict renderer / CLI glue (a non-proven verdict can never print PROVEN) | trusted, unit-tested |

**Not** in the trusted base for a PROVEN verdict: composition of package contracts (it cannot reach PROVEN), and any heuristic detector (it cannot override).

---

## H. Open decisions for the owner

*Answered 2026-09-26. The owner's decisions are recorded verbatim in [ADR-012](adr/ADR-012-contract-bounded-proven-tier.md); the questions are kept below as they were put.*

1. **On-demand attestation.** May the attestation service run pdflatex, on the configuration preamble and probe documents only and never the body, for uncached configurations?
   - **Yes:** strict coverage is bounded by grammar breadth.
   - **No:** PROVEN is limited to the shipped cache, which is close to 0 because 200/200 configurations are distinct. Everything else stays `PENDING (predicted)`.
2. **Vendored `.cls`/`.sty`** (41/200 papers ship a class). Should they be admitted by content hash, like TL files, or excluded from the strict tier? Admitting them fits the vision, since the contract is generated from the file, but it puts the author's file into the trusted oracle side.
3. **Preamble definers interleaved with loads** (91/200). Should they be part of the configuration key, which is sound but gives lower cache reuse? Or should M3 require every user definer to come after the last load, widening later?
4. **Exit codes.** Keep 0/1 and add `--require-proof` (recommended; no churn), or adopt a tiered 0–4 scheme in a later major version?
5. **Benign `\def`** (undelimited, non-recursive, Turing-free body; +17 on s2 [M]). Admit it as a def-style definer (M7+), or hold the owner's stated boundary strictly? This design holds it until you decide.
6. **Wrong reason/location counts as `strict_wrong`.** This is stricter than "zero false-READY" and matches "exact". Confirm.
7. **Sample 3 timing.** Draw it only after the pdfmanagement oracle repair (recommended), with sample 2 formally marked design-seen.
   - *Answered differently from the recommendation (ADR-012 decision 7):* the oracle is frozen as CI's digest-pinned TeX Live image, run locally via a container; the laptop TeX Live is not the oracle; every graded artefact is re-graded once under it and the diffs published as an oracle-baseline change; sample 3 is drawn and graded only after that.
8. **Release gate.** Confirm that any differential disagreement blocks a release. Otherwise the word "exact" cannot be printed.

---

## I. As built

### I.1 M0 (2026-09-26)

What the M0 pull request implemented, with where to find it. The numbers are
not restated here; each lives in the artefact named.

| deliverable | where |
|---|---|
| verdict type and the only renderer; only `Proven_*` can print PROVEN | `latex-parse/src/verdict.ml`, `latex-parse/src/verdict.mli`, test `latex-parse/src/test_verdict.ml` |
| `--compile-check` tier line and why-not-strict lines, frozen token lines unchanged | `latex-parse/src/validators_cli.ml` |
| LP-Foreign reported as its own reason (`T0_lp_foreign`); FOREIGN rendered whenever an LP-Foreign construct occurs anywhere in the closure (not only at the root); a `.bbl` finding is *bbl dialect (M6)*, never FOREIGN; the exit code is unchanged in M0, and a FOREIGN with exit 0 says so | `latex-parse/src/compile_contract.ml`, `latex-parse/src/validators_cli.ml` (`tier_verdict`), `latex-parse/src/strict_boundary.ml` |
| `--require-proof` (exit 4 unless proven; always 4 in M0) | `latex-parse/src/validators_cli.ml`, test `latex-parse/src/test_verdict.ml` |
| closure-scoped boundary scan, `--strict-boundary FILE` | `latex-parse/src/strict_boundary.ml`, measured by `scripts/tools/measure_strict_boundary.py` into `corpora/real_roots/strict_boundary_sample2.json` |
| standing battery | `corpora/strict_battery/`, graded by `scripts/tools/gen_strict_battery.py` |
| strict-tier North Star and heuristic block | `scripts/tools/gen_project_state.py` from `corpora/real_roots/proven_coverage_sample1.json` and `corpora/real_roots/proven_coverage_sample2.json` (field `verdict_tier`); sample 3 joined on 2026-09-27, see I.3 |

**Machine consumers of `--compile-check` and how each was kept working.** The
`MODEL-CONNECTED` line, the `READY\t`/`NOT-READY\t` token line and the indented
reason lines are printed exactly as before; the new lines come after them.
`scripts/tools/diff_real_roots.py` scraped reason tokens over the whole output,
so it now stops at the first `TIER` line (on output without a `TIER` line this
is the old scrape, byte for byte); `scripts/tools/gen_proven_coverage.py` also
records the tier tokens and refuses output without them. Every other consumer
reads the exit code, the `MODEL-CONNECTED` line or lines that start with `T0`
to `T5`, and the new lines match none of those.

### I.2 M1 slice 1: the contract generator (2026-09-27)

Data only: nothing reads a contract yet. Signature probes (the typed lattice,
§B.2 `signature`) are slice 2; this slice ships the probe harness alone.

| deliverable | where |
|---|---|
| generator, one configuration per run | `scripts/tools/gen_contract.py generate` |
| probe harness (solo, batched, error classes) | `scripts/tools/gen_contract.py probes` |
| reproducibility gate, with kill-tests of the completeness guards and the review repros | `scripts/tools/check_contracts_reproducible.py` (local/nightly) |
| parser unit tests on recorded logs, and completeness checks of the committed kernel file and contracts | `scripts/tools/check_gen_contract_parsers.py` (required `spec-drift`, with kill-tests in `check_gate_selftests.py`), fixtures in `corpora/contracts/parser_fixtures/` |
| committed contracts, kernel file, probe demonstration | `corpora/contracts/` (see its `README.md`) |

**Where TeX runs.** Every job runs in the image named by `TEX_IMAGE` in
`.github/workflows/tex-oracle.yml`; the generator reads the reference from that
file. It starts one long-lived container per invocation and runs each job with
`docker exec`, in a fresh directory (never a reused name: a directory re-created
under the same name reached the container stale through the VM mount, measured)
mounted at a fixed container path. The laptop TeX Live is never used. The work
directory must sit under `$HOME`, because colima mounts only that.

**Environments.** The container carries the graders' environment
(`diff_real_roots.py`, `gen_strict_battery.py`: `SOURCE_DATE_EPOCH=0`,
`openin_any=p`, `openout_any=p`, private `TEXMFHOME`/`TEXMFVAR`; since C-91
the oracle imposes exactly this on every graded run, shell graders included,
through `_oracle.graded_env`, and on both backends the engine's WHOLE
environment is an allow-list, the image's own plus these variables, through
`_oracle.engine_env`), log-width
settings that change no outcome, and `FORCE_SOURCE_DATE=1`, which the graders
do NOT set. Three environments derive from it: *forced* (as is: `\year` is 1970,
so name-set runs are byte-reproducible), *grading* (without
`FORCE_SOURCE_DATE`: the real clock, the oracle's own), and *second date*
(another forced date). The load outcome and the probes are attested under
*grading*; the name set is generated under *forced* and checked against
*grading*. Review defect: `\ifnum\year>2000 \lpundefinedyy\fi` loaded under the
forced date and failed under the graders'.

**How each §B.2 field is generated.**

- `pin`: the engine banner, the image reference, `uname -m` inside the image,
  and the sha256 of `pdflatex.fmt` and of `texlive.tlpdb`.
- `kernel`: every name defined in format state (a job after `\everyjob`),
  committed under `corpora/contracts/kernel/`, cached locally by fmt hash AND
  the generator's source hash (a behaviour change can never reuse a stale
  kernel; the source hash is never written into a committed file, where a
  comment edit would invalidate every contract, C-68).
  - Candidates come from four independent sources: every string of the
    shipped `pdflatex.fmt`'s string pool (parsed from the format itself; every
    multiletter name in a format's hash table is a pool string, so this is a
    superset by construction); the engine's primitives (below); every name the
    INITEX run of `pdflatex.ini` assigns, plus every name a replay of
    `\everyjob` assigns (the INITEX run intercepts the final `\dump`, because
    `\everyjob` runs before any traceable line of a job); all 256
    one-character names and the null name.
  - Membership comes from the shipped format: each candidate, then every name
    referenced from a dumped meaning, is dumped with `\meaning` in format
    state until no new name appears. The INITEX run is not trusted for
    membership because an INITEX rebuild does not reproduce the shipped
    `pdflatex.fmt` byte for byte (six build times tried, none matched).
  - **Completeness is checked by TeX's own counter, not by any list the
    generator built.** A job asks `\csname` for every candidate (inside
    groups), which enters a name TeX's hash table does not hold and leaves one
    it holds alone; `\tracingstats` prints TeX's `cs_count` at the end. So
    count(with the candidates) − count(without) is the number of candidates
    NOT in the table, and count(without) minus the covered number is the
    number of table entries the candidates MISS. It must be 0, else the
    kernel is incomplete and so is every contract built on it.
  - **Primitives** are derived from the engine alone: a virgin INITEX
    (`pdftex -ini -etex -translate-file=cp227.tcx`, the fmtutil flags, nothing
    read) dumps a format whose hash holds exactly the primitives; its string
    pool gives candidates, a second virgin INITEX run tests each with
    `\ifcsname`, and the number found must equal the virgin dump's own
    multiletter count. The one-character primitives are found by enumerating
    all 256.
  - Date-dependent names (whose format-state meaning changes with the date)
    are found by a second format-state dump under the second date.
- `load_outcome`: the configuration plus `\begin{document}\end{document}`,
  under `-interaction=nonstopmode -halt-on-error`, in the grading environment
  and with the oracle's pass protocol, `run_to_fixpoint` (to the first rc 0 in
  at most 3 runs, then one confirming run, in one directory). A fatal records
  the last run's first `!` message, its error class, the pass count, the first
  pass's rc, and the load segment of the trace run in which it occurred. The
  same protocol under the forced date must agree, or the contract is
  incomplete (`date_dependent_load`). Review defect: a definer that writes to
  the `.aux` loaded on pass 1 and failed on pass 2.
- `files_read`: the `.fls` INPUT lines of the forced run's first pass, minus
  those of an empty format-state job, minus job-local files. Each file carries
  its sha256.
- `defined_names`: a trace, then a dump, on every pass the protocol can run.
  - **Pass histories.** The oracle's protocol runs up to 3 passes until one
    completes, then one confirming pass: `F^j S S` (j < 3) or `F F F`, where
    S is a pass that completed and F one that failed. A pass's state at body
    start depends only on the files earlier passes wrote, so the states the
    protocol can grade are those after the histories `''`, `F`, `S`, `FF`,
    `FS`, `FFS` (passes 1 to 4; `protocol_histories`, derived in the parser
    gate from `Tex.fixpoint` itself by running every rc sequence through it).
    Each history is run as a tree of job directories: the pass after `h`
    runs on a copy of the files the passes of `h` wrote, and an F pass is
    the same document failing (`\errmessage`) just before `\end{document}`,
    so it writes what the configuration writes at `\begin{document}` and not
    what it writes at `\end{document}`. Re-review 2 (defect 1): the previous
    version checked passes 1 and 2 of an all-completing run only, and a
    counter the `.aux` carries from pass to pass (`thirdB`) defined a name
    from pass 3 on, which the protocol grades after `F S`.
  - **Three environments.** Every pass of every history is run under the
    forced date with job name `job` (the reference), under the graders' real
    clock with `job`, and under the real clock with a second job name.
    Re-review 2 (defect 3): the date and job-name checks ran on pass 1 only,
    and a definer that writes `\the\year` or `\jobname` to the `.aux` changed
    the state on pass 2.
  - Pass 1 traces every assignment from the first line to after the
    begin-document hooks, with a marker before every load. The trace is
    repeated on every pass of every history in all three environments,
    because a later pass reads what an earlier one wrote:
    `\usepackage{lastpage}` defines `\r@LastPage` only on pass 2, from
    `\newlabel{LastPage}` in the `.aux`, and that name is a token of no file
    (re-review defect 1); and a job named otherwise creates other names (l3's
    `\csname` lookups of `__file_seen_<jobname>.aux:`).
  - The dump takes the body-start `\meaning` of every name of the UNIVERSE: the
    kernel's candidates, every name any trace pass assigned, every name token
    of the files read, of the definers and of the files the job itself wrote
    (`.aux`, `.out`, ..., with their `\csname ...\endcsname` literals), and
    every one-character name and the null name. Each
    is inside an `\ifcsname` guard, in a catcode regime where any byte string
    can be written inside `\csname`; names holding the regime's reserved bytes
    or line feeds go through `\lowercase` with placeholder bytes.
  - The same hash-count check runs at body start against the universe: a name
    the universe misses would be called undefined without having been asked.
    It runs on every pass of every history in all three environments
    (`coverage_passes`, 18 records; pass 1 of the reference is also
    `coverage`), each count seeded with the same files as the dump of that
    pass and labelled with the pass it describes. The first version counted
    on pass 1 only, so a name created from the `.aux` on pass 2 was outside
    every check and the contract still said `complete` (re-review defect 1,
    measured on `lastpage`); the second counted once more, seeded with pass
    2's files, i.e. on pass 3, but labelled it pass 2, and never counted
    pass 2 itself (re-review 2, defect 2).
    It found two such names in the five-package configuration before the
    file-token reading was widened (`\Gin@rule@*`, `\!!stringa`: a package's
    own catcodes make `*` and `!` letters); the reading now takes, after each
    `\`, every prefix of the non-space run that ends at a non-letter.
  - A trace record is read at EVERY `=` whose remainder reads as a value, not
    only the first (a name may contain `=`), and the null control sequence,
    which prints as `\csname\endcsname` (or `csnameendcsname` under
    `\escapechar=-1`), is read as the empty name. Each reading is dumped; a
    reading that names nothing where another does is a phantom and is not
    reported.
  - A name is listed iff its body-start meaning differs from its format-state
    meaning. Class `Undefined` means the configuration removed a kernel name.
  - `set_in` is the load segment of the assignment whose value the name keeps:
    a `restoring` record gives back the segment of the assignment it restores
    (values matched up to TeX's `ETC.` truncation), never the local assignment
    a group end undid. The restored value is looked up first in a per-name
    stack of the values local assignments replaced (innermost first), then in
    the name's history. The first version took the last history entry with the
    same printed value, which is the in-group assignment itself when that
    re-set the same value; MEASURED once: hyperref's `\WriteBookmarks` (set to
    `0` by hyperref, re-set to `0` in a begin-document group) read
    `begin_document`, and is `package:hyperref`. The trace shows no group
    levels, so two local assignments at one level of which the first re-sets
    the level's starting value are still attributed to that first one (same
    meaning; only the label can be off).
  - Traced names whose meaning at body start is back to the kernel's are
    listed in `reverted_names`. Primitive parameters the configuration
    assigned (`\baselineskip`, ...) are listed separately in
    `parameters_assigned`: the contract compares meanings, not values, so
    their values are not recorded.
  - Every pass of the reference is compared with its pass 1: a name-set
    difference makes the contract incomplete (`pass_dependent_state`, naming
    the pass and history); a meaning that differs while the name stays
    defined is recorded in `pass_dependent_meanings` and flagged on the name.
    So a configuration whose `.aux` defines a name on a later pass
    (`lastpage`, `thirdB`) is reported incomplete, with the name, rather than
    described by its pass-1 state. Two runs of the same pass (the S and F
    documents of one history) must agree too (`nondeterministic_state`).
  - Each pass under the real clock is compared with the same pass under the
    forced date: any difference outside the kernel's date-dependent names
    makes the contract incomplete (`date_dependent_state`).
  - Every job is named `job` (field `jobname`), and some meanings hold the job
    name. Each pass under the second job name is compared with the same pass
    under `job` (both real clock): a name-set difference makes the contract
    incomplete (`jobname_dependent_state`), and the meanings that differ are
    listed in `jobname_dependent_meanings` and flagged on the name, so a
    consumer compares meaning hashes under `job` (re-review LOW item b). No
    name is translated between job names, so a configuration that defines a
    name holding the job name is incomplete (`glossaries`:
    `__file_name=job.glsdefs`). The kernel file lists the format-state
    meanings that change with the job name the same way
    (`jobname_dependent_names`).
  - **Known limits (re-review 2, recorded, not fixed).** (a) An F pass here
    fails at the end of the body; a real failing pass fails somewhere in it,
    so its `.aux` holds the begin-document writes plus whatever the document
    wrote before the failure. The two extremes (fails at once: F; completes:
    S) are checked, not the states between, which depend on the document
    (M2's per-document check). (b) The second job name is one name
    (`lpotherjob`); a configuration that tests for one particular job name
    other than `job` is not excluded. (c) The real clock is the clock of the
    generation run; a configuration that changes state on one date only is
    not excluded. Repro of each: the `jobD` / `dateC` definers of
    `check_contracts_reproducible.py` with `job`/`2000` replaced by the
    specific value.
- `meaning`: one of `Undefined`, `Relax`, `Primitive`, `Char`, `MathChar`,
  `Register`, `Font`, or `Macro` with the fields `long`, `protected`,
  `outer`, `robust`, `ltcmd_spec`, `params` and `arity_hint`. `arity_hint` is
  the static `#n` count and is only a hint.
- `catcodes` and `active_chars`: the differences from format state at body
  start.
- `unicode`: an `\ifcsname u8:…` sweep of U+0080..U+FFFF (minus surrogates),
  cross-checked against the `u8:` names in the closed world.
- `counters`: each counter with its `\theX` and its `cl@X` reset list.
- `key_families`: from the `\KV@<family>@<key>` names.
- `declared_options`: from the `\ds@<option>` names.
- `self_check`: a separate run. `\ifcsname` must agree with membership on a
  seeded 1% sample of the whole universe (members AND non-members; the first
  version sampled members only, so it could never see a false absence), on
  every name referenced from a body-start meaning, and on any `--use-names`.
- `complete_scope`: what `complete` attests. It is the configuration's name
  set only. It attests no document's own names: all committed contracts have
  no use-names, and M2 must run a per-document check (the names a document
  uses) before a contract backs a PROVEN verdict about that document.
- `provenance`: the generator's semantic version and the sha256 of every job
  `.tex` and of every forced-environment job log (trace, dump, self-check).
  **Deviation from §B.2:** no generator source hash is written into a
  contract, because a comment edit would then invalidate every contract (the
  C-68 lesson); the version is bumped by hand when output changes on purpose,
  and the reproducibility gate catches a change that was not.

**When a contract is incomplete.** `complete` is true only if all of the
following hold. Otherwise `incomplete_reasons` lists every failing check.

- The kernel is complete (its hash count, its primitive count).
- The load succeeded, under the pass protocol, identically under both dates.
- The trace parsed and tracing was never switched by the configuration.
- No name changed meaning without a traced assignment; every defined name's
  surviving assignment is in the trace.
- No universe name is defined in format state yet missing from the kernel.
- No name was unwritable into a dump.
- The dump primitives were intact.
- TeX's hash count at body start finds no name outside the universe, on
  every pass of every pass history (passes 1 to 4), in all three
  environments.
- Every trace pass ran clean, and every F pass failed at the forced failure.
- The body-start name set is the same on every pass of every history, under
  the real clock (state, not only names) and under a second job name.
- The `u8:` sweep agreed with the names.
- The self-check passed.

**How the parsers read TeX's log.**

- `cp227.tcx` prints a line feed literally, so trace records and dumped
  meanings can run over several log lines. Trace records are re-joined
  across those lines. Dumped meanings are framed by an end sentinel.
- The escape character is tracked from the trace itself. The class-loading
  code runs with `\escapechar=-1`, where a one-byte name is either the active
  character or the control symbol; an `into` is attributed only to the
  readings whose known value is the preceding `changing` record's.
- A `!` line counts as an error only when TeX's location context follows it,
  in the solo classifier and in the batched one alike.
- A job that leaves no log is an infrastructure failure, never a TeX outcome.

**Measured (2026-09-27, under the image, arm64).**

- **Kernel: 23,519 names** (the first version had 23,435 and missed 84; it
  lost none). The 84 are: the reviewers' 24 (14 pdfTeX primitives, among them
  the mark primitives, whose meaning prints `\topmark:`, and `\nullfont`,
  whose meaning is a font; 10 names assigned only by `\everyjob`), 9 more
  `\everyjob` names (the `sys_if_shell…` conditionals), one more primitive
  (`\pdfoptionpdfinclusionerrorlevel`), and 50 names holding `=` that the
  first-`=` parser cut short (`\__int_compare_=:NNw`, `\__file_name=…`,
  `\c__text_purify_\=_A_tl`, `\OT1\=`, …).
  - Candidates: 32,579 format pool strings, 27,700 INITEX-traced names, 29
    `\everyjob` names, 554 primitives, 257 one-character and null names;
    33,780 after the closure.
  - TeX's hash in format state holds 29,447 multiletter names (29,438 at the
    format's own `\dump`, plus 9 that `\everyjob` creates in every job); the
    candidates cover all 29,447, uncovered 0. Kill-tests: dropping `topmark`
    from the candidates gives uncovered 1, dropping the reviewers' 24 gives
    24.
  - Primitives: 551 multiletter, equal to the virgin dump's own count of 551,
    plus `\ `, `\/` and `\-`; every one is defined in format state.
  - Date-dependent kernel names: the six `c_sys_{year,month,day,hour,minute}`
    and `c_sys_timestamp_str` constants.
  - Job-name-dependent kernel meanings: none. `\c_sys_jobname_str` and
    `\g_file_curr_name_str` are `\let` to the `\jobname` primitive in format
    state, so their meaning does not hold the name. At body start four
    meanings do (`\@curr@file`, `\@curr@file@reqd`, `\g_file_curr_name_str`,
    `\l__file_tmp_tl`: the last file read, the `.aux`); `amsart` has the
    last two.
- **Three contracts, all complete.**

  | configuration | defined names | reverted | parameters assigned | universe | hash entries at body start, pass 1 / passes 2-4 (every history, all covered) | self-check (sampled from the universe, of which members; + referenced) | size |
  |---|---|---|---|---|---|---|---|
  | `article` | 762 | 118 | 19 | 34,577 | 29,846 / 29,847 | 346 (243) + 10,736 | 167 KB |
  | article + amsmath, amssymb, amsthm, graphicx, hyperref | 9,215 | 733 | 26 | 57,452 | 38,909 / 38,911 | 575 (313) + 14,992 | 1.9 MB |
  | `amsart` | 1,979 | 248 | 25 | 38,325 | 30,931 / 30,932 | 384 (249) + 11,377 | 398 KB |

  Re-review 2 regeneration (generator version 4, every pass of every pass
  history in three environments): no defined name was added or removed, no
  meaning, `set_in`, pass-dependent or job-name-dependent meaning changed.
  The universe grew by 3, 6 and 3 names (later-pass traces, in the other
  environments: e.g. `__file_seen_lpotherjob.aux:`), none defined at body
  start. All 18 counts of each contract find 0 names outside the universe;
  under the forced date every pass after the first holds the same count
  (the previous version's "last pass" count, 29,847 / 38,911 / 30,932, was
  in fact pass 3's). Generation time: 17-20 s (`article`), 26-34 s
  (`amsart`), 70-81 s (five packages).

  Re-review regeneration (generator version 3): no defined name was added or
  removed and no meaning changed. The last-pass count holds 1-2 more entries
  than pass 1 in each; all are in the universe (the later-pass trace added 1,
  2 and 1 names, the job-written files 1, 16 and 2 name tokens) and none is
  defined at body start. One `set_in` changed (`\WriteBookmarks`, above).

  Each self-check had 0 mismatches; each load needed 2 runs (success, then
  the confirming run). The first version's contracts under-reported
  `defined_names` in all three (by 4, 70 and 10) — every missing name holds a
  `=`: `\__file_name=<file>`, hyperref's `\PU\=`, `\PD1\=-A`, … — and listed
  bogus `reverted_names` (`__file_name`, `csnameendcsname`, `PU\`, `PD1\`).
  Two `set_in` values change, both measured correct in the trace:
  `amsart`'s `\@tempb` keeps the class's value (a begin-document group
  changed and restored it), and hyperref's `\~` is set by hyperref (the
  begin-document entry was the active `~`).
  - Pass-dependent meaning: `\ReFiCh@1` (rerunfilecheck's checksum of the
    `.aux`) in the five-package configuration.
- **A fourth contract with a fatal load.** article + cleveref + hyperref records a fatal load outcome. Its message is `cleveref must be loaded after hyperref`, and it is attributed to segment `begin_document`, not to the cleveref load.
- **Byte-identical regeneration.** Two independent runs of each contract, each
  from a kernel rebuilt from INITEX, gave identical bytes, and so did the
  kernel file.
- **Re-review defect 1, measured.** Before the fix,
  `gen_contract.py generate --class article --package lastpage` gave
  `complete: true` with `\r@LastPage` absent (pass-1 count 29,921 entries,
  uncovered 0). After: the later-pass trace puts `\r@LastPage` in the
  universe, the pass-2 dump finds it defined where pass 1 did not, and the
  contract is incomplete with `pass_dependent_state: ... ['r@LastPage']`;
  the last-pass count is 29,923 entries, uncovered 0. With `\r@LastPage`
  dropped from the universe, the last-pass count reports uncovered 1 while
  the pass-1 count still reports 0: the pass-1 count alone cannot see it.
  The synthetic shape (a definer's `\AtEndDocument` writing
  `\expandafter\gdef\csname lpq7\endcsname{}` to the `.aux`) behaves the
  same: incomplete naming `lpq7`, and uncovered 1 on the last pass only when
  it is dropped. The committed contracts were not affected (as the re-review
  predicted): each stays complete with 0 uncovered on both passes.
- **Re-review 2, measured (2026-09-27, under the image, arm64).** Before
  the fix (generator version 3) each of the reviewer's synthetic shapes gave
  `complete: true`. After:
  - `thirdB` (a counter the `.aux` carries defines `\lpthird` from pass 3 on):
    incomplete, `pass_dependent_state` on pass 3 after `FS` and `FF` and pass
    4 after `FFS`, naming `lpthird`; nothing on pass 2.
  - `thirdB2` (the name is `lpt\number\lpc`, built in a group with tracing
    off; `lpt2`/`lpt3` dropped from the universe): TeX's count reports
    uncovered 0, 0, 0, 1, 1, 1 on the histories `''`, `F`, `S`, `FF`, `FS`,
    `FFS`, labelled passes 1, 2, 2, 3, 3, 4. Undropped, the later-pass trace
    names `lpt2` and `lpt3`.
  - `dateC` (`\the\year` written to the `.aux`): incomplete,
    `date_dependent_state` from pass 2 on, naming `lpgrade`; pass 1 shows
    nothing, which is what the pass-1 check saw.
  - `jobD` (`\jobname` written to the `.aux`): incomplete,
    `jobname_dependent_state` from pass 2 on, naming `lpnotjob`.
  - Real packages: `hyperref` complete; `lastpage` incomplete naming
    `r@LastPage` (passes 2, 3, 4 after `S`, `FS`, `FFS`; not after `F`,
    since it is written at `\end{document}`); `glossaries` incomplete (job
    name: `__file_name=job.glsdefs`; one name outside the universe on every
    pass, as before).
- **Kill-tests and review repros** (`check_contracts_reproducible.py`, every
  invocation): the hidden-`\def` definer trips both the tracing-toggle check
  and the self-check; the hash count sees one name dropped from the kernel
  candidates, the reviewers' 24 dropped, and one name dropped from a
  contract's universe; the null control sequence is defined as the empty name;
  `\lpa=b` is defined and `\lpa` is not reported; a group-local `\def` undone
  at the group end does not move `set_in`; the `.aux`-writing definer is a
  fatal load on the confirming pass; the `\year` definer is a fatal load
  under the real clock and flagged `date_dependent_load`; the reviewers' 24
  names as use-names on plain `article` give 0 mismatches; `lastpage` and the
  `lpq7` definer are each incomplete, naming the pass-2 name, and each with
  that name dropped from the universe is seen by the pass-2 count
  (uncovered 1) and not by the pass-1 count (0); and the four re-review 2
  shapes above (`thirdB`, `thirdB2`, `dateC`, `jobD`) come out as stated.
- **Surprises.**
  - The `amsfonts` lazy files (`umsa.fd`, `umsb.fd`, the msam/msbm metrics) are read at the first math-mode use of anything in article + amssymb, not at `\mathbb` in particular.
  - `amsart` already reads them in its load run.
  - amssymb removes the kernel's robust inner names `\angle `, `\hbar ` and `\rightleftharpoons `.
  - No configuration changes a catcode at body start.
  - `amsart` changes the active `~`.
  - All three configurations define 349 `u8:` slots.
  - hyperref defines 171 `Hyp` keys, where the spike counted 161.
- **Probe harness.** 30 sampled public macros of the five-package contract, plus `\mathbb` and `\frac`, gave 80 solo probes. The results are in `corpora/contracts/probes/`.
  - Solo probes now run under the grading environment and the oracle's pass protocol: 19 are ok (2 runs each: success, then the confirming run) and 61 are fatal (3 failing runs). No error class changed from the single-pass version.
  - Solo and batched polarity agreed on 80 of 80, with 0 timeouts; the batch now counts an error only with TeX's location context, as the solo classifier does.
  - Each solo probe took 0.74 s on average (all its runs) on 4 workers, against the spike's 0.11 s per run on 6 workers.
  - 24 of the 80 probes stop on `Command … unavailable in encoding OT1`: hyperref defines those names, but they cannot be used in this configuration. A name being defined is not the same as it being usable, and this is what slice 2's signatures must record.
  - The static arity of `\mathbb` is 0, because it takes its argument by lookahead. This is the §B.2 warning, measured.

**Open.**

- The committed contracts are arm64. CI's tex-oracle job runs the same multi-arch digest on amd64, which is a separately built image. Whether its `pdflatex.fmt`, and so every contract, is byte-identical to the arm64 one is **not measured**. Until it is, the reproducibility gate stays local and refuses (exit 2) on an architecture that differs from the contract's.
- The error-class table is a first cut. It is normalised from the first `!` line.
- Not generated yet, deferred to slice 2 or later: `lazy_files` (the probe harness records first-run `.fls` deltas per probe, but no contract field), `environments`, per-mode `u8:` coverage, `decl_templates`, `definer_rules`, `load_delta` kinds, `limits` and `graphics`.
- The §B.2 attestation of `files_read` (re-run with the file hidden; the expected fatal must appear) is not implemented.
- `complete` is configuration-scoped (above); the per-document self-check is M2's.
- The file-token reading of the universe is an over-approximation checked by the hash count, not a proof by itself; a configuration whose count is not 0 is reported incomplete rather than guessed.

### I.3 Sample 3 drawn (2026-09-27)

The virgin sample of §E, drawn at frame offset 720 (OPEN-118 moved it off the
OPEN-110 fixer window) and graded once under the pinned image, at a `main`
commit. It is sealed for measurement only (OPEN-119). The numbers are not
restated here.

| deliverable | where |
|---|---|
| graded rows and the frame manifest | `corpora/real_roots/results_sample3.json`, `corpora/real_roots/manifest_sample3.json` (`scripts/tools/diff_real_roots.py --offset 720 --record`) |
| strict-tier and heuristic rows | `corpora/real_roots/proven_coverage_sample3.json` (`scripts/tools/gen_proven_coverage.py`) |
| closure boundary scan (measurement only, never used for ranking) | `corpora/real_roots/strict_boundary_sample3.json` (`scripts/tools/measure_strict_boundary.py`) |
| publication, with samples 1 and 2 beside it and the 10 repo-named ids split out | `scripts/tools/gen_project_state.py` into `docs/v27/PROJECT_STATE.md` §1 |
| staleness, claim and cell checks; oracle fingerprint check | `scripts/tools/check_project_state.py`, `scripts/tools/check_oracle_pin.py`, kill-tests in `scripts/tools/check_gate_selftests.py` |

### I.4 M2 phase 1: the Coq kernel of L_S0 (2026-09-27)

The kernel is proved and attested. Nothing in the product uses it: the CLI's
strict tier is still the M0 stub, and `--require-proof` still exits 4 on every
document. Ledger row: OPEN-121 in [PROJECT_STATE.md](PROJECT_STATE.md).

| deliverable | where |
|---|---|
| node grammar, token stream (`flatten_doc`), the exact bytes given to pdflatex (`render`) | `proofs/Strict/Syntax.v` |
| contract record, a parameter of every theorem (`c_defined`, `c_sig`); fatal reasons E0, E1, E3, E4, E5, E6 | `proofs/Strict/Contract.v` |
| the declarative semantics `Runs`: 42 constructors, one per construct and failure mode, each commented with its probe family `S0/<constructor>` | `proofs/Strict/Semantics.v` |
| the decider (`step` iterated by `run`; `decide`), membership `in_strict_doc`, and the theorems | `proofs/Strict/Decide.v` |
| `Faithful` (a `Definition`) and the bridge `strict_ready_iff_pdflatex` | `proofs/Strict/Bridge.v` |
| extraction and its regeneration | `proofs/Strict/Extract.v`, `scripts/tools/regen_strict_kernel_extract.sh`, committed as `latex-parse/strict/strict_kernel_extracted.ml` (checked by `scripts/tools/check_extract_identity.py`) |
| harness driver (trusted, T5: builds the contract record from the committed files) and unit tests | `latex-parse/strict/strict_decide.ml`, `latex-parse/strict/test_strict_kernel.ml` |
| probe-attested signatures | `scripts/tools/gen_strict_signatures.py`, `corpora/contracts/strict/article-s0-signatures.json` |
| rule probes (with the branch matrix and the bound family) and the generated differential v2 | `scripts/tools/strict_differential.py`, `scripts/tools/_strict_s0.py`, `corpora/strict_s0/` |
| pure gate over the kernel and its evidence, and the home of RULE R-INERT (spec-drift, 22 kill-tests) | `scripts/tools/check_strict_kernel.py` |

**Theorems** (all `Qed`; `Print Assumptions` is Closed for each, registered in
`scripts/tools/check_print_assumptions.py`, which also pins the bridge's
statement textually so that `Faithful` stays its only premise about the
world):

- `strict_decider_exact`: for a strict document, `decide C d = ProvenReady`
  iff `Runs C init (flatten_doc d) Compiles`, and `decide C d =
  ProvenNotReady r l` iff `Runs … (Fatal r l)`. Proved from `run_sound` and
  `run_complete`, a refinement in both directions.
- `runs_deterministic`: proved by induction on `Runs` itself, not through the
  decider.
- `runs_total` and `decide_total`: a strict document always has an outcome,
  so the decider never answers `NotStrict` inside the tier.
- `in_strict_dec`.
- `strict_ready_iff_pdflatex : Faithful oracle_ok C -> in_strict_doc C d ->
  (decide C d = ProvenReady <-> oracle_ok (render d))`, and its NOT-READY
  corollary `strict_not_ready_pdflatex`. Both are about READY iff compiles
  ONLY: the reason and line of a NOT-READY are exact against `Runs`, and
  agree with pdfTeX's first error by the probes and the differential
  (0 disagreements), not by a theorem (§0). The body of `Faithful` is pinned
  by coqc `Print`, by a kernel convertibility check against fully qualified
  names (C-87), and by `check_strict_kernel.py` check 10; both corollaries' types
  are pinned by kernel conversion against fully qualified statements and
  Bridge's field list by `Print Module` (C-88).
- Not a tautology, measured: changing one case of `step` (a paragraph break in
  math reported as E3 instead of E6) makes `run_sound_n` fail to compile.

**The fragment.** Characters (letters, digits, `. , ; : ! ? ( ) / + - =`),
spaces, paragraph breaks (a blank line or `\par`), brace groups and stray
`}`, the four math delimiters, `^`/`_` with a character or a group argument,
and control words (ASCII letters) with no argument. A control word is decided E1 when it is
outside the configuration's closed world, and is otherwise inside the tier
only if it has a signature. The configuration is `article` with no packages.
The fragment is BOUNDED (C-86): brace nesting at most 200 and at most 20,000
tokens (`Decide.v` `max_brace_depth`, `max_tokens`, part of `in_strict_doc`).
MEASURED under the pinned oracle: 253 nested groups compile and 254 give
"TeX capacity exceeded [grouping levels=255]" in text, math and script
groups; a formula of 1,000,000 characters, and 100,000 occurrences of
`\Longleftarrow`, `\arcsin`, `\dots` or `\mathstrut` in one formula, give
"[main memory size=5000000]". Before the bound the kernel answered PROVEN
READY on such documents. The margins are attested per name (families R-NEST-*
and R-BIG-* below) and for the structure (rule-probe family BOUND); that
different names' memory costs ADD UP in one document is INFERRED, not
measured.

**Why the semantics runs on tokens, not on the tree.** TeX executes a token
stream, and the tree nesting is not TeX's nesting. The byte-level lesson of
the semantics-first spike is a rule of `Runs`, not a property of a lexer: `$`
outside math looks at the next token, so an empty inline formula printed as
`$$` opens display math (`R_dollar_display_open`). Likewise `{}}` is a group
and a stray brace, `$x$$y$` is two inline formulas, and inside a math brace
group TeX is in non-display math even within a display.

**Rendering.** `render` puts a line feed after every token except a space and
`$`, so pdfTeX's `l.N` locates the token that failed; the differential checks
the line of every fatal. The header comment of `proofs/Strict/Syntax.v` says
why each inserted line feed is harmless.

**Signatures (generator version 3, C-85).** A defined control word gets
`text` in {material, noop, fatal E3} and `math` in {noad, noop, fatal E3,
fatal E6} only through five stages (`scripts/tools/gen_strict_signatures.py`,
docstring):

0. **RULE R-INERT** (stated and implemented in
   `scripts/tools/check_strict_kernel.py`, applied by the generator and
   re-applied by the gate to every admitted name): the name's `\meaning` at
   body start, and the meanings of every name of letters and `@` its
   expansion texts reach (transitively; 1,110 meanings for the 400
   candidates), are read from the pinned image. A name is not inert, and
   never admitted, when it is a conditional primitive (`\if*`, `\else`,
   `\fi`, `\or`, `\unless`), an expansion-control primitive (`\expandafter`,
   `\noexpand`, `\futurelet`, `\csname`, ...), a prefix (`\immediate`,
   `\global`, ...), an interaction-mode changer (`\nonstopmode`, ...), an
   I/O, diagnostic, tracing, code-table (`\catcode`, ...), deferred-execution
   (`\aftergroup`, `\everypar`, ...) or definition primitive, a register, a
   name `\let` to a structural character; or a macro whose expansion text is
   empty (transparent to expansion), has unbalanced conditionals, or whose
   expansion closure reaches a primitive of the state-changing classes
   (`\tracingall` reaches `\tracingstats` through `\loggingall`,
   `\tableofcontents` reaches `\input` and `\write`). The closure does not
   follow names holding other characters (`\T1\IJ`, `\?-cmd`): it is a
   screen, not a proof, and the probes below remain the behavioural check.
1. **Base probes**: the 15 of version 2 (X in text and math next to each
   construct the kernel models, and the two look-ahead probes of C-84).
2. **Follower, display-follower and repetition families**, 43 documents per
   name: X immediately followed by every token class of the fragment in text
   and in math (every one of its 74 characters, space, blank line, `\par`,
   braces, `$`, `$$`, `\(` `\)` `\[` `\]`, `^`, `_`, an undefined word,
   `\end{document}`, end of file); X right after a `$` in display math
   (D-FOLLOW-*: the position `Semantics.display_bad_follower` reads with
   expansion, tex.web §1197); X 300 times in text, in math, alternating with
   a character, in 300 paragraphs, groups, formulas and displays; X at the
   nesting bound (alone and at every one of the 200 levels) and repeated to
   the token bound in one paragraph and in one formula.
3. **Admission**: exactly one of the 12 hypotheses makes the EXTRACTED
   decider agree with the oracle on all 58 probes (verdict, message class,
   line).
4. **Interleaving**: seeded documents interleaving all admitted names (text
   names in text, with and without characters between, across paragraphs and
   in groups; math names in inline and display math and across formulas), at
   least 300 occurrences each, graded against the kernel with the final
   signature set; a disagreement is reduced by delta debugging to a minimal
   set of names, all of which are rejected, until a round agrees.

The candidates are a rule, not a list: the article closed world's control
words minus `par`, `begin` and `end`, in sha256 order, the first 400.
MEASURED (generator version 3): 130 admitted, 270 rejected (83 by R-INERT,
184 by the base probes, 3 by stage 2, 0 by interleaving; 24 interleaving
documents in one round, 0 disagreeing). 5,743 documents were graded for
this run; the 6,000 base-probe grades of version 2 were reused for
byte-identical documents under the same oracle provenance (the tool refuses
reuse across any provenance difference). Admitted classes: fatal E3/noad 50,
material/noad 53, noop/noop 20, noop/fatal E6 2, noop/noad 2, material/noop
1, material/fatal E6 1, noop/fatal E3 1. Version 2 admitted 150; the 20 it
admitted and version 3 does not are the whole finding of the adversarial
review (C-85): `\empty`, `\CurrentOption`, `\UnusedTemplateKeys` (empty
expansion), `\iftrue`, `\immediate`, `\nonstopmode`, `\tracingall`,
`\loggingall`, `\tracingnone`, `\hideoutput`, `\tableofcontents`,
`\titlepage`, `\flushright`, `\endflushright`, `\endlist`, `\endverse`,
`\footnotemark` (R-INERT); `\theenumiii` and `\LinkTargetOff` (transparent
after a display `$`: D-FOLLOW-DOLLAR compiles); `\cong` (exceeds main memory at the
token bound: R-BIG-MATH gives "main memory size"). Version 3 admits no name
version 2 rejected.

**Evidence.**

- Rule probes (`corpora/strict_s0/rule_probes.json`): 510 graded documents,
  510 agree with the oracle; every one of the 42 constructors is used by at
  least one agreeing probe. Of them, 393 form the BRANCH MATRIX (every
  innermost frame x every token class, and for `$`, `^`, `_` x every follower
  class including every admitted signature pair, undefined and end of file),
  covering all 230 cells the grammar admits in the tier; the 352 cells
  membership excludes (a script without its argument) are covered by 396
  documents the extracted decider places outside the tier. 9 BOUND documents
  at the bounds agree; 3 one past them are outside the tier.
  `check_strict_kernel.py` derives the look-ahead tokens from the `Runs`
  conclusions, the token and frame classes from `Syntax.v`/`Semantics.v` and
  the signature classes from the signature file, so a new look-ahead rule or
  token class without matrix coverage fails the gate (kill-tested).
- Generated differential v2 (`corpora/strict_s0/differential_v2.json`):
  4,000 seeded documents (seed 2), 4,000 of 4,000 agree with the oracle on verdict, message class and line (line agreement covers only the classes that have an l.N: E0 has none, so its 543 documents are compared on verdict and message class only): READY 1,572, E0 543, E1 429, E3 616, E4 127, E5 608, E6 105; 0 oracle timeouts or infrastructure failures; exact one-sided 95% upper bound on the disagreement rate 0.075% overall and 0.19% on READY verdicts, OVER THIS GENERATOR'S DISTRIBUTION. Of the 4,000, 100 put an admitted name right after a `$` in display math and 21 an undefined one, 298 have at least 100 tokens and 86 at least 300 (runs of repeated names; 31 of those are READY). A first run of the same size, made with a generator bug that let text-fatal and math-fatal names into clean documents (a helper shadowed by a second function of the same name), also agreed 4,000 of 4,000; it is not committed because the fixed code does not reproduce it; 40 of 42 constructors are used (`R_dollar_display_eof` and `R_mclose_inline_bad` only by the token-level rule probes). Sized at 4,000, not 10,000, because the shared oracle was loaded (about 2 documents per second).
  The upper bound is a bound over the documents THIS generator draws, not
  over L_S0 (C-85): version 1 drew no `$` in display math followed by a name
  and no repeated name, and its 1,200 of 1,200 coexisted with both classes of
  wrong verdict below. A class version 2 does not draw is equally unbounded.
- Findings of the evidence, each an F-defect fixed at its source:
  - C-83 (semantics): `R_dollar_display_eof` said a `$` ending a display at
    the end of a file reads past the end; pdfTeX appends an end-of-line to
    the last line, so the look-ahead meets a space.
  - C-84 (contract): `\expandafter` passed 13 probes as noop/noop and read the
    token after the next.
  - C-85 (contract, found by adversarial review): 6 admitted names are
    transparent after a display `$` (false NOT-READY with a wrong location:
    `$$z $\empty $$$$$` compiles), and a name attested once per occurrence can
    consume a global resource (`\tableofcontents` twenty times: model READY,
    oracle "No room for a new \write", false READY). Fixed by stages 0, 2 and
    4 above, the branch matrix and the generator's new shapes; both
    reviewers' scripts re-run: 0 of 130 admitted names disagree in the
    display-follower repro, and of the 50 adversarial documents 32 agree and
    18 are outside the tier (they use names no longer admitted).
  - C-86 (semantics): the kernel had no capacity bounds (false READY at 254
    nested groups and on memory exhaustion); fixed by the bounded fragment.

**Deviations from §C.3, and what is not done.**

- No parser: documents are trees, printed by `render`. `parse`, `parse_exact`
  and the bytes-level form of the bridge are phase 2 (done: §I.5);
  `no_turing_construct` is not done.
- The fatal-reason set is phase 1's (E0, E1, E3, E4, E5, E6). E2, E7 and E11
  need environments, arguments and Unicode, which the fragment does not have.
  Unclosed math at `\end{document}` and a missing `\end{document}` are
  labelled E5 (stack discipline).
- `complete_scope` (§I.2): the contract attests the configuration's name set,
  not a document's. In phase 1 every E1 verdict of the differential is itself
  graded by the oracle; the per-document self-check before a PROVEN verdict is
  still to do, with the wiring into the product.
- A signature is attested in the probed contexts, under the rule R-INERT
  screen, and in the interleavings; a context none of them builds is covered
  only by the differential. Letters and digits after a name are probed one by
  one (FT-CHARS, FM-CHARS) but in one document, so a look-ahead that silently
  swallows one character without changing the outcome is not observable
  (and does not matter to the verdict: READY iff compiles).
- The kernel's own signature generator (`gen_strict_signatures.py`)
  duplicates M1 slice 2's `contract_signatures.py` (branch
  `feat/v27165-contract-signatures`); the two must converge onto one
  signature source before M3 (OPEN-121).

### I.5 M2 phase 2: from bytes to the proven decision (2026-09-28)

Phase 1 decided documents given as trees and printed by `render`. A user's
file is arbitrary bytes. Phase 2 closes that gap for L_S0: a verified reader
from bytes to the kernel's token stream, the front matter, and the proven
decision on the bytes themselves, with the line of a NOT-READY. It is proved
and attested, and still wired into nothing but `strict_decide.exe`'s file
mode (the CLI's strict tier stays the M0 stub until M3). Branch
`feat/v27165-strict-bytes`, STACKED on `feat/v27165-strict-kernel`. Ledger
row: OPEN-121.

| deliverable | where |
|---|---|
| the lexical contract `lexcon` (catcode of every byte, `\endlinechar`, the structural names), a parameter of every theorem; the declarative reading `LexFile` (TeX Live's first-line directive `FirstLine`, its line splitting `Lines`, TeX's states N/M/S per line `LineLex`, the line bound `LinesLex`); the executable `lex`; `lex_exact`, `lexfile_deterministic` | `proofs/Strict/Lexer.v` |
| the front matter `Prologue`, the body `Body` (kernel tokens with their lines), `Parse`; the executable `parse`; `parse_exact`, `parse_deterministic` | `proofs/Strict/Front.v` |
| membership `in_strict_bytes` (decidable), the decider `decide_bytes`, the declarative location `Determined`/`ReportedLine`, `decide_bytes_exact`, `decide_bytes_not_strict_iff`, `determined_threshold_unique` | `proofs/Strict/DecideBytes.v` |
| `FaithfulBytes` (a Definition premise over bytes, stated against `Parse` and `Runs`) and `strict_ready_iff_pdflatex_bytes`, `strict_not_ready_pdflatex_bytes` | `proofs/Strict/BridgeBytes.v` |
| the diagnostic `explain` (first offending byte and construct; not proved, checked against the verdict on every evidence file) | `proofs/Strict/Explain.v` |
| extraction, separate from phase 1's (which stays byte for byte, so the phase-1 evidence stays fresh) | `proofs/Strict/ExtractBytes.v`, `scripts/tools/regen_strict_bytes_extract.sh`, `latex-parse/strict/strict_bytes_extracted.ml` (checked by `check_extract_identity.py`) |
| the lexical contract, dumped from the pinned image at body start of `article`; its structural names READ from phase 1's renderer (`Syntax.v`), not written | `scripts/tools/gen_strict_lexical.py`, `corpora/contracts/strict/article-s0-lexical.json` |
| driver: `--bytes` (JSON lines) and file mode `strict_decide.exe FILE.tex` (PROVEN-READY / PROVEN-NOT-READY reason l.N, and E0 with no line since pdfTeX reports none / NOT-IN-FRAGMENT byte offset and construct; exit 0, 0, 3) | `latex-parse/strict/strict_decide.ml`; unit tests `latex-parse/strict/test_strict_bytes.ml` |
| byte-level generators, probe families and differential | `scripts/tools/_strict_bytes.py`, `scripts/tools/strict_differential.py --bytes-rules / --bytes N`, `corpora/strict_s0/bytes_probes.json`, `corpora/strict_s0/bytes_differential.json` |
| pure gate over the reader, its evidence (every summary count recomputed from the per-file records) and the pin of `BridgeBytes.v`'s whole code (spec-drift, 24 kill-tests) | `scripts/tools/check_strict_bytes.py` |

**Theorems** (all `Qed`, `Print Assumptions` Closed, registered in
`check_print_assumptions.py`, which also pins both bytes corollaries'
statements, printed and by kernel conversion of their types against fully
qualified statements, `FaithfulBytes`' printed body and its kernel
convertibility, and `Print Module BridgeBytes` = exactly `FaithfulBytes` and
the two corollaries, as C-87 and C-88 do for `Bridge.v`; MEASURED on a build
with a `Time`-prefixed shadow `in_strict_bytes := False` in BridgeBytes.v:
both printed statement pins still pass, both type pins and the field list
fail):

- `lex_exact : lex L b = ts <-> LexFile L b ts` (both directions; reading is
  total, a byte outside the fragment is a `RBad` token, never a failure), and
  `lexfile_deterministic`.
- `parse_exact : parse L b = Some ks <-> Parse L b ks`, `parse_deterministic`.
- `in_strict_bytes_dec`.
- `decide_bytes_exact`: for a file in the fragment with parse `ks`,
  `decide_bytes C b = ProvenReady <-> Runs K init (toks_of ks) Compiles`, and
  `decide_bytes C b = ProvenNotReady r ln <-> exists l, Runs K init (toks_of
  ks) (Fatal r l) /\ ReportedLine K ks (Fatal r l) ln`.
- `decide_bytes_not_strict_iff : decide_bytes C b = NotStrict <-> ~
  in_strict_bytes C b`.
- `strict_ready_iff_pdflatex_bytes : FaithfulBytes oracle_ok C ->
  in_strict_bytes C b -> (decide_bytes C b = ProvenReady <-> oracle_ok b)`,
  and its NOT-READY corollary. As for phase 1, the bridge covers READY iff
  compiles only; the reason and the line are exact against `Runs` and
  `ReportedLine` and agree with pdfTeX by the probes and the differential.
  LINE agreement is over the classes that have an `l.N` (E1, E3, E4, E5,
  E6): E0 (rc 0, "No pages of output.") has none, so the driver prints an
  E0 without a line (file mode and `--bytes` JSON), an E0 record carries
  none, and an E0 agrees only when the oracle reports none either
  (`strict_differential.agrees_bytes`; the bytes PR's review, LOW-1: the
  first driver printed the proved `ReportedLine` of an E0, a line pdfTeX
  never gives, and the agreement rule never read it).

**The line of a NOT-READY, declaratively.** `Runs` gives a reason and the
INDEX of a token; pdfTeX prints `l.N`, the line its reader stands on, which
can be after that token (C-84: after a `$` in display math TeX reads and
expands the next token first). The definition needs no knowledge of which
rule fired: `Determined K ts n o` says every stream sharing the first `n`
tokens of `ts` has outcome `o`; the reported token is the `k` with
`Determined (S k)` and not `Determined k` (unique by monotonicity:
`determined_threshold_unique`), i.e. the last token the outcome depends on;
the reported line is that token's line (a kernel token's line is the line of
its last raw token: `\end{docu%` newline `ment}` in math is reported on the
line of its `}`, MEASURED), or 0 when no prefix determines the outcome (no
`\end{document}`: "Emergency stop", no `l.N`). `decide_bytes` computes it with
`rd`, the number of tokens `run` read, and the proof shows the two agree.

**What the reader models, each rule measured** (the constructors cite
`probe L0/<constructor>`): TeX Live ends a line at LF, CR and CR LF (CR alone
MEASURED; CR LF CR LF is one blank line; LF CR is two lines); a last line
without a terminator is a line; trailing spaces are trimmed and
`\endlinechar` (13, category 5) appended; states N/M/S as tex.web §343-356
(spaces and tabs collapse and are skipped at a line start and after a control
word; a blank or spaces-only line is `\par`; a comment discards the rest of
its line and the end-of-line character, any byte allowed in it); control
words (maximal letters) and the four control symbols `\( \) \[ \]`.
OUTSIDE (never a verdict): a byte of category 4, 6, 9, 13 or 15 (`&`, `#`,
`~`, bytes 1-8, 11, 12, 14-31, 127, 0 and every byte >= 128), TeX's `^^`
notation (anywhere, after the escape character and after a control word's
letters), any other control symbol (including `\ ` and `\` at a line end), a
line over 10,000 bytes, a file over 1,000,000 bytes, a first line starting
with `%&` (C-89), and a kernel stream ending with `$` (MEASURED: `$$x$%` at
the end of a file is "Emergency stop", not the "Display math should end with
$$" of `R_dollar_display_eof`, which was attested with the end-of-line space).
After `^`/`_` TeX's math scanner skips spaces (§1151), so they are not in the
kernel stream (`B_space_script`).

**The front matter** (MEASURED): any blank lines, spaces, tabs, comments and
`\par` before `\documentclass`, between `}` and `\begin`, and nothing between
`\documentclass` and its brace other than what the reader drops (a line end
after a control word, spaces, a comment); `\documentclass{art%` newline
`icle}` is the same token list and compiles. A blank line after
`\documentclass` ("Paragraph ended before \@fileswith@ptions was complete")
or `\begin` is outside. **After `\end{document}` pdfTeX reads nothing**
(MEASURED: every byte 0-255 on its line and later lines, a 300,000-byte next
line, `\zzundefined`, `^^`, `}`, `$`, another `\begin{document}` all give rc
0); the one effect of its line's tail is TeX Live's 200,000-byte buffer (a
300,000-byte tail on that line gives rc 1), which the 10,000-byte line bound
covers.

**Evidence** (the pinned oracle; `check_strict_bytes.py`):

- `bytes_probes.json` (seed 2): 3,907 files, 2,167 graded and 2,167 agree with the oracle on verdict and message class, and on the LINE for every class that has an `l.N` (READY 826, E0 42, E1 94, E3 150, E4 67, E5 821, E6 167; 0 timeouts or infrastructure failures); 1,740 outside by design, every one decided NOT-IN-FRAGMENT (the reader's outside rules, 139 near-misses (every outside construct in each reader state among them), and the phase-1 MATRIX-OUT documents re-laid out). Every constructor of the reader and the front matter is used by an agreeing graded probe except the outside rules (used by files decided outside) and `LL_nullcs` (unreachable under the article contract); the reader's branch matrix (N/M/S x every catcode class present) and the kernel's 230-cell matrix are covered at the byte level. The 501 graded phase-1 rule probes appear four times each: as rendered, with lines joined, joined through comments holding any byte, and with mixed CR/CR LF/LF line ends, padding, front-matter and `\end{document}` variants and bytes after it. `R_dollar_display_eof` is exercised by no byte-level file: its only byte-level path, a stream ending with `$`, is outside the fragment (above)
- `bytes_differential.json` (seed 5): 5,000 files in the fragment, 2,500 phase-1 generated trees re-laid out (joined, comment-joined, mixed) and 2,500 generated directly as byte strings (105 direct candidates that fell outside the fragment were replaced and are counted), 5,000 of 5,000 agree with the oracle on verdict and message class, and on the line for every class that has an `l.N` (READY 2,007, E0 465, E1 544, E3 705, E4 208, E5 831, E6 240; 0 timeouts or infrastructure failures); the 139 near-misses are all NOT-IN-FRAGMENT; exact one-sided 95% upper bound on the disagreement rate 0.06% overall and 0.15% on READY, OVER THIS GENERATOR'S DISTRIBUTION, not over L_S0 (C-85). A class of files the generators do not draw is not bounded.
- The tree decider (phase 1, with its harness line computation) and the bytes
  decider (proved location) give the same verdict, reason and line (E0's
  not compared: it has none) on all 897 phase-1 renderings.
- Both files were RE-RUN under the pinned oracle after the review's LOW-1
  (the E0 records' lines removed at the driver); every graded record's
  verdict, oracle grade and agreement and every graded count is unchanged
  (the only record differences are the 42 + 465 E0 lines, now none); the
  differential's near-miss set is now the generator's current 139 (the
  first run drew 103, before the last near-miss families were added), all
  NOT-IN-FRAGMENT. `check_strict_bytes.py` recomputes each record's agreement from
  its stored oracle tuple and model verdict and every count of the summary,
  `by_class`, `by_family` and the stated bound from the records (LOW-3); a
  flipped `agree` under an unchanged summary fails it (kill-tested).

**Findings of phase 2**, each an F-defect fixed at its source before any
evidence was committed:

- C-89 (reader): TeX Live's first-line directive `%&` — `%&latex` loads the
  DVI format, rc 0 and no PDF, a false READY the reader (which read the line
  as a comment) would have given.

**Deviations and what is not done.**

- The fragment's bytes are phase 1's characters (`safe_char`) plus spaces,
  tabs, line ends, comments of any bytes, and the text after
  `\end{document}`; widening the character set (quotes, brackets, UTF-8) is
  grammar widening (M7+), each with its probes.
- `^^` and the other outside constructs are excluded conservatively (TeX needs
  a third byte for `^^`; with `\endlinechar` appended there always is one).
- `LL_nullcs` is unreachable under the article contract (every buffer ends
  with `\endlinechar`), and `LL_end` is reached only after a control symbol
  consumed it (outside); the gate derives both facts from the data.
- The structural names come from phase 1's renderer; for another
  configuration (M3) the class comes from its contract.
- Not wired into `validators_cli` (M3), no per-document closed-world check yet
  (as phase 1), and no `no_turing_construct` corollary yet.
