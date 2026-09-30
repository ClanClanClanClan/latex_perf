# Design: the contract-bounded proven tier

**Status:** approved design, adopted by [ADR-012](adr/ADR-012-contract-bounded-proven-tier.md) on 2026-09-26, which records the owner's answers to §H verbatim. Milestones M0 and M1 slice 1 (§F) are implemented. M2 phase 1, the Coq kernel of the fragment L_S0 (§I.4), and M2 phase 2, the decision on the BYTES of a file with its verified reader (§I.5, a stacked branch), and step 2 slice A, commands with one argument that run it (§I.6, stacked on phase 2), are proved and attested, but no product verdict uses them: the CLI's strict tier is still a stub, so nothing a user sees is proven yet. Programme ledger row: OPEN-116 in [PROJECT_STATE.md](PROJECT_STATE.md).

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

**`oracle_ok` is clock-independent on the fragment: MEASURED, and enforced by a rule (OPEN-118 known limit (b), 2026-09-28).** The protocol sets `SOURCE_DATE_EPOCH=0` but not `FORCE_SOURCE_DATE`, so `\year`, `\month`, `\day` and `\time` follow the container's clock, and a document that branches on them could grade differently on different days. That would make `Faithful` (bytes → outcome) a claim about the day of grading, not about the bytes. The experiment graded the documents under three clocks through `_oracle.run_to_fixpoint` itself: the protocol as it is (the real clock, 2026-09-28/29), and two forced dates that differ in every field (1971-02-03 04:05 and 2049-11-28 23:59 UTC, each with `FORCE_SOURCE_DATE=1`). It used a scratch-only wrapper around `graded_env`, and the protocol was not changed. The documents were every probe-family document of the 130 admitted names (130 × 58 = 7,540), the 24 interleaving documents, the 510 graded rule probes, and the first 600 documents of the v2 differential (seed 2). Every regenerated differential document matched its recorded `tex_sha256`. That is 8,557 unique documents and 18,622 fresh grades, 0 of them infrastructure failures or timeouts. For the 7,049 signature-only documents, the normal-protocol grade came from their committed evidence, which was graded on an earlier day. Across the three clocks, 0 documents differ in rc, PDF, first error, line, or the PDF's bytes with its dates and `/ID` removed (for the 7,049 documents whose normal grade is committed evidence, which records no PDF digest, the byte comparison covers the two forced clocks only). Each of the 1,601 committed records that has a fresh normal-protocol grade (1,508 documents, some recorded more than once) matches that grade exactly. Positive controls show the instrument sees a clock dependence: `\ifnum\year>2025 \undefined\fi` is rc 1 today and in 2049 but rc 0 in 1971, and `\ifnum\time>600` behaves the same way. `\today` changes only the PDF. Rule R-CLOCK of `check_strict_kernel.py` (check 11, pure, three kill-tests) keeps this true for the next signature file. The date is not pdfTeX's only per-run input: the review of this experiment MEASURED `\pdfrandomseed` seeded from the real time on every run (so `\pdfuniformdeviate`/`\pdfnormaldeviate` differ per run), the timer `\pdfelapsedtime`, and `\pdffilemoddate` returning a file's real modification time even with `FORCE_SOURCE_DATE=1`; `\pdfcreationdate` is pinned by `SOURCE_DATE_EPOCH=0`. So the rule covers every RUN-DEPENDENT primitive: it fails if an admitted name is one of `\year`, `\month`, `\day`, `\time`, `\pdfrandomseed`, `\pdfsetrandomseed`, `\pdfuniformdeviate`, `\pdfnormaldeviate`, `\pdfelapsedtime`, `\pdfresettimer`, `\pdffilemoddate` (itself or `\let` to one), or if its recorded expansion closure (the same one R-INERT uses) reaches one of them or one of the kernel file's `date_dependent_names`. Only these primitives are hand-listed. No admitted closure reaches any of them today. Known limits: the screen limit of §I.4 (a name made of non-letter characters is not followed), and a name BUILT at run time (`\csname year\endcsname`) is not followed either; both are closed only by ADR-013's token-exact closure. **Merged into step 2 (C-94..C-98 branch, 2026-09-30):** the rule reads the closure exactly as the step-2 R-INERT does (every reading of a printed name, the closed world, the active characters; C-96) and applies to the nine one-argument commands of `article-s1-arg-signatures.json` as well as to the 84 phase-1 names; none of the 93 reaches a run-dependent primitive or a date-dependent name. The one-argument commands were NOT part of the clock measurement above (it predates them): for them the clock-freedom is the static rule only.

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
measured. **Superseded by C-94 (§I.6):** the brace bound was a PROXY for
TeX's grouping level, exact only while every frame was a brace; slice A let a
formula open inside an argument and the proxy broke. The bound is now on
`Decide.groups` (every frame one TeX group, an argument frame its command's
measured `g`) over every state of the run (`Decide.peak <= max_groups` =
200), plus names of at most 100 letters.

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
- Generated differential v2 (`differential_v2.json`, superseded by `corpora/strict_s0/differential_v3.json` in step 2, §I.6; in git history):
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

### I.6 Step 2, slice A: commands with one argument (2026-09-28)

The fragment widens from argument-free control words to control words that read
ONE brace argument and run it (text or math), for configuration `article`. It
is proved and attested and, like phases 1 and 2, wired into nothing but
`strict_decide.exe` (the CLI's strict tier is still the M0 stub). Branch
`feat/v27165-strict-args`, stacked on `feat/v27165-strict-bytes` (PR #623).
Ledger row: OPEN-122.

**What pdfTeX does, and so what the semantics says.** pdfTeX reads the whole
argument from the file before it runs any of it. MEASURED under the pinned
oracle: `\textbf{x`/`\zzundef`/`y`/`}` on four lines gives "Undefined control
sequence" on the line of the closing brace, not of `\zzundef`; with a blank
line inside instead, "Paragraph ended before \text@command was complete", also
on the closing brace's line (the text font commands re-read their argument with
a macro that is not long); `$\mathrm{x`/blank line/`y}$` gives "Paragraph ended
before \math@egroup was complete" on the blank line itself (the macro that
reads the argument from the file is not long). So an error inside an argument
is reported where the file reader stands. `Semantics.v` says this with two new
relations, used by every rule that stops pdfTeX:

- `Stops fs p r l ts out`: outside every argument the run stops with `Fatal r
  l` (`Stop_now`); inside one the error is DEFERRED and the tokens are scanned
  from the offending one on (`Stop_defer`).
- `Scans sc p ts out`: TeX's argument scanner. It counts braces until the
  outermost argument closes (`SC_close_last`: the deferred reason, at that
  brace), and a paragraph break inside an argument that is not long wins
  (`SC_par_outer`: at the break, when the outermost argument was read from the
  file by a non-long macro; `SC_par_short`: E6 at the brace, when an argument
  that was open at the deferral re-reads it with a non-long macro).

A one-argument command's signature (`Contract.v` `asig`) has a longness (`long`,
`short_inner`, `short_outer`) and a behaviour per mode: stop before reading the
argument (`now`), read it and stop (`after`), or read it and run it in a group
of a mode (`run`: text, text in restricted horizontal mode — an hbox, where
`$$` is an empty formula and LaTeX's `\[` opens nothing — or math). New `Runs`
rules: `R_arg_{text,math}_{now,after,run}`, `R_close_arg`, `R_par_short`,
`R_dollar_restricted_open`, `R_mopen_display_restricted`; every phase-1 rule
that stops pdfTeX now concludes through `Stops` (names unchanged). The frame
`FArg` records an argument while it runs. Membership adds `wfa`: every
one-argument command is followed immediately by its `{`, and every argument
closes before `\end{document}` and before the end of the stream (MEASURED:
otherwise pdfTeX reads on past what the fragment models — "File ended while
scanning use of"); `Explain.v` reports it as `WArgForm`.

**Theorems** (all `Qed`, `Print Assumptions` Closed; 25 capstones registered in
`check_print_assumptions.py`, three new: `scans_deterministic`,
`stops_deterministic`, `decide_total`): `strict_decider_exact` (both
directions), `runs_deterministic` (on `Runs` itself; `scans_deterministic` and
`stops_deterministic` likewise on the relations), `runs_total` and
`decide_total` (the totality proof carries an invariant: the braces `wfa`
counts are the brace frames down to the outermost argument, `arg_depth`),
`in_strict_dec`, and on bytes `lex_exact`, `parse_exact` (reader unchanged),
`in_strict_bytes_dec`, `decide_bytes_exact` (the location machinery `rd` counts
the scanner's tokens: `rd_scan`; `rd_stable`/`rd_unstable`/`rd_never` re-proved
for the deferral), `decide_bytes_not_strict_iff`,
`determined_threshold_unique`; both bridges. The bridge pins (statements,
bodies, fully qualified convertibility, module fields, sentence allow-lists)
are UNCHANGED and pass: `Bridge.v`, `BridgeBytes.v` and every name their
pinned statements and bodies mention are unchanged; what changed is the
content of `Runs`, `in_strict_doc` and `in_strict_bytes`, which the pins
reference by name (deliberately: a pin of a premise's name is what lets the
semantics widen without re-pinning, and C-87/C-88's shadowing shapes stay
excluded by the fully qualified convertibility checks).

**Signatures (generator `gen_strict_arg_signatures.py`, version 1).** The
candidates are a rule (`check_strict_kernel.arg_candidates`, re-applied by the
gate to the recorded meanings of every closed-world control word): the
control words whose meaning at body start, through one robust wrapper, is a
macro with parameter text exactly `#1`, minus the phase-1 names. Stages:
R-INERT, base probes (36 per name, every token on its own line so the LINE
separates "at the name", "at the break" and "at the closing brace"), follower
/ display-follower / repetition / bound probes (the command nested 200 deep,
repeated to the token bound, and with an argument of the token bound's size),
admission (exactly one of 306 hypotheses agrees on every probe),
interleaving (all admitted commands nested in each other with the phase-1
names inside), and CONTEXT (every phase-1 name inside a carrier of each mode an
argument opens that phase 1 never probed: restricted horizontal mode, text
inside math). MEASURED (generator version 1, the pinned image, a private
container): 166 candidates; 83 rejected by R-INERT, 72 by the base probes
(their argument is a counter, a dimension, a font name, a condition, or it is
stored and not typeset: `\author`, `\date`, `\markright`), 4 by stage 2
(`\fbox`, `\frame`, `\underline` nested 200 deep exceed "[grouping
levels=255]": each level opens more than one TeX group; `\numberline` after a
display `$` moves the error line to its argument's brace: TeX's look-ahead
EXPANDS a non-robust macro, which reads its argument), 0 by interleaving (9
documents), 0 by context (484 documents: all 121 phase-1 names in an hbox
argument, in text and in math, agree); 7 admitted, all of one class — long,
run with material in an hbox in text, run in an hbox in math: `\mbox`,
`\centerline`, `\leftline`, `\rightline`, `\llap`, `\rlap`, `\clap`. 3,932
documents graded. The near-misses name mechanisms the model does not have
yet: an argument that runs INLINE in the current math list (`\pmod`; its `$`
closes the formula instead of meeting a group), code after the argument that
runs in whatever mode the argument left (`\underbar`: "Missing $ inserted" at
an unclosed `$`, not "Extra }"), and the display-`$` expansion of a
non-robust argument macro (`\numberline`).

**C-92 (R-INERT).** The meaning closure of RULE R-INERT did not follow LaTeX's
robust wrappers (`\X` = `\protect \X  `, the code being the meaning of the name
"X "), so a robust name's own code was never screened. Following it (phase-1
generator version 4) rejects 9 names phase 1 had admitted: `\bf`, `\it`,
`\sf`, `\tt`, `\eminnershape`, `\labelitemfont` (reach `\afterassignment`
through `\@defaultunits`) and `\centering`, `\raggedleft`, `\labelenumiv`
(reach `\immediate` through `\GenericError`); 121 remain. The same rule
excludes the text font commands (`\textbf`, `\emph`, `\textit`, ...) from
slice A.

**Evidence** (the pinned image, run in a private container of it: the shared
container accumulated other agents' `/tmp/gs_*` files, which #622's state
check refuses; `LP_ORACLE_WORKROOT`; `check_strict_kernel.py`,
`check_strict_bytes.py`):

- Rule probes (`rule_probes.json`, generator version 3): 1,426 documents, 680
  graded, 680 agree; 746 outside the tier by design. Every non-dormant
  constructor of `Runs`, `Scans` and `Stops` has an agreeing family that
  exercises it; 7 are DORMANT under this contract (no admitted command is
  `short_*`, `now` or `after`: `R_arg_{text,math}_{now,after}`,
  `R_par_short`, `SC_par_outer`, `SC_par_short`), which the gate derives
  from the signature files. The branch matrix now has the argument heads
  (`arg.textr`, the only payload mode admitted), the argument commands as
  tokens (only `{` as a follower is in the tier) and as followers of every
  look-ahead, and the scanner's cells `scan|<token>|k1/k2|<longness>`: 301
  in-tier cells and 537 excluded ones covered. The slice-A families come
  after the phase-1 ones so the phase-1 probes, and their byte-level
  re-layouts, are byte for byte what they were: 475 grades reused.
- Generated differential v3 (`differential_v3.json`, seed 3): 3,000 of 3,000
  agree on verdict, message class (checked against the fatal EVENT: for an
  error inside an argument, the offending token) and line (the LOCATION: the
  outermost argument's closing brace): READY 1,030, E0 410, E1 339, E3 631,
  E4 80, E5 445, E6 65; 502 documents defer an error inside an argument
  (`Stop_defer`), 727 close an argument that ran (`R_close_arg`), 415 open
  math in an hbox; exact one-sided 95% bound 0.10% (0.29% on READY), over
  THIS generator's distribution (C-85).
- Byte-level probes (`bytes_probes.json`): 5,975 files, 2,847 graded, 2,847
  agree (verdict, message, and line for every class with an l.N); 3,128
  outside by design, all decided outside; 0 `explain` mismatches; the tree
  decider and the bytes decider give the same verdict, reason and line on
  all 1,414 renderings; 1,238 grades reused.
- Byte-level differential (`bytes_differential.json`, seed 6): 3,500 of
  3,500 agree (READY 1,353, E0 347, E1 367, E3 669, E4 110, E5 533, E6 121);
  399 files defer an error inside an argument, whose argument spreads over
  lines (the direct generator writes commands with `_strict_bytes.Direct.argcmd`);
  82 directly written files fell outside and were replaced; the 139
  near-misses are all outside; bound 0.086% (0.22% on READY), over this
  generator.
- Findings: no semantic disagreement on any graded document. The harness
  had three defects, each found by a dry run with a provisional contract
  BEFORE any document was graded: the matrix completer gave up after a
  deferral (the argument stayed open, so the probe fell outside the tier),
  a generated hazard could land between a command and its brace, and a deep
  nest plus an argument crossed the brace bound. C-92 (above) is the one
  correction of a published claim.

**The payoff on real papers, measured.** The frame of `diff_real_roots.py`
(2,719 papers arXiv declares pdflatex with one toplevel, ordered by sha256 of
the id), offsets 0-399 (samples 1 and 2) and 2000-2718; never 720-919 (sealed
sample 3). MEASURED with the extracted decider on the ROOT file's bytes: 0 of
1,119 roots are in the fragment before this step (phase-1 signatures of
version 3, no argument signatures) and 0 after. 1,117 stop at the front
matter (the class is not a bare `article`, it has options, or the preamble
loads packages or defines anything: 22 roots load no package, the median
loads 16; the classes are `article` with options 293, `amsart` with options
219, bare `article` 181, `IEEEtran` 79, ...), 1 is over the size bound, 1
starts with `%&`. With the front matter replaced by the fragment's, 0 of the
bodies are in either. INFERRED from a regex census of the bodies: 1,118 use a
defined control word that has no signature (`\maketitle` 1,011, `\section`
975, `\label` 961, `\cite` 900, `\ref` 852, `\subsection` 816, `\in` 809,
`\frac` 797, `\bibliography` 778, `\caption` 720, `\left`/`\right` 719,
`\item` 716, `\cdot` 699, `\textbf` 696, `\mathcal` 677, `\alpha` 602), 1,043
an environment, 1,040 a character outside the set (`[`, `]`, `*`, quotes),
983 another control symbol, 953 `\\`, 916 `#` or `&`, 802 `~`, 710 a byte
over 127; 51 bodies have exactly one of these classes. Slice A's commands
occur in 126 bodies (`\mbox`), 40 (`\centerline`), 4 (`\rlap`), 1 (`\llap`).
So packages block first, then R-INERT, then the character set; and math
symbols such as `\alpha`, `\in`, `\cdot`, `\leq` are outside only because
phase 1 attested a 400-name sample of the ~2,000 control words (its selection
rule), which is the cheapest widening there is.

**Not done, and why: RULE R-INERT, not the semantics, blocks slices B-D.**
MEASURED (R-INERT with C-92's closure, meanings at body start from the pinned
image): not inert are `\section`, `\subsection`, `\subsubsection`,
`\paragraph`, `\footnote`, `\caption`, `\maketitle` and every text font
command (reach `\afterassignment` through `\@defaultunits`, the size code of
`\selectfont`); `\item`, `\begin`, the environments `itemize`, `enumerate`,
`center`, `quote`, `equation` and the math alphabets `\mathrm`, `\mathcal`
(reach `\immediate` through `\GenericError`, i.e. through their error path);
`\label` (`\catcode` through `\@makeother`), `\cite` (`\immediate`),
`\clearpage` (`\write`), `\mathbf` (`\input`), and the environment ends
`\enditemize`, `\endcenter`, `\endquote` (`\aftergroup`). Inert are `\par`,
`\newpage`, `\ref`, `\pageref`, `\end`, `displaymath`, `\frac`, `\sqrt`,
`\hat`, `\bar`, `\vec`, `\overline`, `\mbox`, `\fbox`, `\underline`,
`\centerline`.

- Slices B (sectioning, moving arguments), C (the list, quote, center and
  equation environments) and D (`\label`) are therefore outside the tier BY
  RULE until R-INERT distinguishes a terminal-only `\immediate\write` on an
  error path, and an `\afterassignment` consumed inside the same expansion,
  from the effects the rule exists for (C-85: `\tableofcontents`' twenty
  `\write`s). That refinement is step 3's first item; the semantics of this
  step (arguments, deferral, restricted mode) is what they then need.
- Environments also need the reader's `Body` to accept `\end{X}` for X other
  than `document`, and kernel tokens for `\begin{X}`/`\end{X}`: not started.
- The inert `\frac`, `\sqrt`, `\hat`, `\bar`, `\vec`, `\overline` read their
  arguments otherwise: `\frac` two macro arguments; the math accents, `\sqrt`
  and `\overline` through TeX's math scanner, INCREMENTALLY (an error inside
  is reported at its own line, like a script group). Each is a mechanism of
  its own, not a signature of this one; `\sqrt` also looks ahead for `[`.

**C-94: the capacity bound was a proxy, and the grammar outgrew it (BLOCKING,
found by an adversarial review of this step, 2026-09-29).** C-86 bounded the
fragment by BRACE depth (200), because 254 nested braces overflow TeX's
grouping levels. That was exact only while every frame of the state was a
brace. Slice A let a formula open inside an argument, and a formula is a TeX
group with no brace: `\mbox{$\mbox{$ ... x ... $}$}` holds two groups per
brace. MEASURED: 127 levels compile, 128 give "! TeX capacity exceeded,
sorry [grouping levels=255]" — at 128 braces, inside the old bound, where
the extracted decider said PROVEN-READY (and, with `\zzundef` innermost,
PROVEN-NOT-READY E1 for a document pdfTeX stops for another reason); the
reviewer proved it in Coq (the document is in the fragment, `decide` =
`ProvenReady`, `Runs ... Compiles`), so `Faithful` was false under the
committed signatures. `\llap{\(` and `{\mbox{$` (three groups per two
braces) are the same class. HOW THE PROBES MISSED IT: every nesting family
(R-NEST-*, A-R-NEST-*, the rule probes' BOUND, the generator's `nest`)
nested ONE frame kind; none interleaved kinds, and the proxy is exact on
every single-kind stack.

THE CLASS, AND THE FIX BY METHOD: a TeX capacity bounded through a proxy the
grammar can outgrow. Every capacity is now either bounded by an exact
account in the model's own terms or shown unreachable with a measured
margin:

- `Decide.groups fs` sums `frame_groups` over the frame stack: 1 for a text
  brace group, a formula (any of `$`, `\(`, `$$`, `\[`) and a math or script
  group; an argument frame is the `g` its command holds open (a new field of
  `Contract.v` `TRun`/`MRun` and of the frame `FArg`). `Decide.peak` is the
  largest `groups` over every state the run reaches (the run being `step`
  iterated as `run` iterates it; a stop halts pdfTeX, and the scanner that
  locates a deferred error opens no group). `bounded C ts` requires
  `peak C init ts <= max_groups` (200), `length ts <= max_tokens` (20,000)
  and every name at most `max_name` (100) letters. `peak_spec` proves peak
  is the maximum over `Reaches` (a declarative relation over `step`) and
  `strict_groups_bounded` that every reached state of a strict document
  holds at most 200 groups (both Closed, registered capstones: 27).
  `check_strict_kernel.py` pins the four definitions token for token.
- `g` is MEASURED per command and mode by the argument generator's stage G
  (version 2): the deepest brace nesting pdfTeX survives inside the
  argument, against the body's capacity measured the same way. Result:
  1 for the seven hbox commands; 3 for `\frame` (both modes) and for
  `\underline` in text (formula + math group + hbox), 1 for `\underline` in
  math. Both were rejected in version 1 BECAUSE the brace proxy was wrong
  for them (nested 200 deep they overflow); with the exact account they
  pass every stage, including the new stage 3b, and are admitted.
- The frame kinds and which kind can be pushed on which are read from the
  EXTRACTED model: `strict_decide.exe --frame-pairs` searches, through the
  extracted `step`, every token of the grammar (an exhaustive match over
  `tok` in the driver fails to compile if a constructor is added) from
  `init` to depth 4. Each pair (below, above) is probed by a stream that
  repeats it (a cycle through the pair) to EXACTLY 200 groups, which the
  model must decide and pdfTeX agree with, and to 201, which the model must
  put outside; and pdfTeX's own first overflow is searched, which must lie
  in [K + 1 - T, K + 1] (K the measured capacity, T the largest measured
  transient): an account that under-counts any kind fails that window, as
  the reviewer's document would (it overflows at 128 of its own model's
  "braces"). `measure_strict_capacity.py` writes `capacity.json`; the
  argument generator's stage 3b runs the same family for every candidate
  (A-CAP-*) as an admission condition; `check_strict_kernel.py` check 11
  requires every recorded pair probed, every constructor of the extracted
  `frame` type and every admitted command's argument frame (per mode) in
  some pair, and the search alphabet to cover every constructor of `tok`.

THE CAPACITY TABLE (the pinned image; `capacity.json`, `texmf`, `measured`,
`transients`, `table`, `usage`): see the rows below, filled from the
artefact.

| capacity (pdfTeX) | value in the image | the fragment's account | bound | measured at the bounds | margin | status |
|---|---|---|---|---|---|---|
| grouping levels | 255 (the body holds K = 254; `capacity.json` `measured`) | `groups` = 1 per frame, `g` per argument frame, over every reached state (`peak`) | `max_groups` = 200 | every one of the 321 model pairs, repeated to 200 groups, compiles/agrees; pdfTeX's first overflow is at 255 groups for 320 pairs and 254 for 1 (a paragraph start in vertical mode, transient +1): the account is EXACT | 254 - 200 - 8 (largest transient: the output routine at a page break or at `\end{document}`; `\[` 3, a paragraph start 1, none in math) = 46 | PROVED bound (Coq) + MEASURED exactness |
| main memory | 5,000,000 words | ~~through `max_tokens` and `max_groups`~~ — WRONG: argument copies make it depth x tokens; superseded by C-98 (below) | — | the 758,796 was a flat document, not the worst case | — | refuted (C-98) |
| main memory (C-98, C-104, C-105) | 5,000,000 words | `Decide.mem` <= `max_mem` = 2,000,000 over the base 435,796: every token its `c_cost` (a SLOPE over three counts past the base's high-water mark, seven contexts, every instrument on a page that never ships (C-105), plus letters x H_text and atoms x B_math), every argument's tokens its command's `as_copy` 3 | `max_mem` (Coq, `bounded`) | 1,695 account-checked records, pdfTeX within the account on every one (worst 0.972, `S:char-par`, the shape the token cost is taken from); the round-2 review's never-shipping documents 0.62-0.77 (2.34 under the C-104 account); 1,632,796 at most inside the fragment | 2.05x over the account's ceiling; C-104's "upper bound on every graded record" was true only of records whose pages shipped | MEASURED upper bound, not proved |
| dimensions (C-104) | a dimension is a signed 32-bit count of sp; max_dimen 16,383.99998pt on every scan | `Decide.dim`: per segment (paragraph at the top level), the tokens' `c_dim`, measured from TeX's box dumps with the boundary constants | `max_dim` = 8,000pt (Coq, `bounded`) | 164 dimension-bound documents compile, pdfTeX's box at most 0.996 of the account (`\hidewidth`); one more is outside | 2.05x to max_dimen | argued + MEASURED |
| string pool | 5,408,265 free at body start | every name pdfTeX reads enters it, defined or not; <= `max_tokens` names of <= `max_name` = 100 letters | `max_name` (Coq, `short_names`) | 1,939,424 (19,994 distinct 100-letter undefined names read whole as one `\mbox` argument; E1 agrees) | 2.8x | PROVED bound + MEASURED |
| strings | 467,099 free | <= `max_tokens` new names | via `max_tokens` | 19,741 | 23x | MEASURED |
| hash (multi-letter control sequences) | 15,000 + 600,000 | <= `max_tokens` new names | via `max_tokens` | 49,161 | 12x | MEASURED |
| buffer | 200,000 bytes | a rendered line holds at most `max_tokens` spaces/`$` and one token of <= `max_name` + 2 bytes; the bytes layer's lines are <= 10,000 bytes (`Lexer.max_line_bytes`) | `max_name`, `max_tokens`, `max_line_bytes` | 20,110 (19,998 spaces then a 100-letter name on one line; E1 agrees) | 9.9x | PROVED bound + MEASURED |
| input stack | 10,000 | one level per argument frame running, plus a constant | via `max_groups` | 401 | 25x | MEASURED |
| parameter stack | 20,000 | one per argument frame running | via `max_groups` | 200 | 100x | MEASURED |
| semantic nest | 1,000 | at most one per group (hbox, formula, math group) plus the paragraph | via `max_groups` | 200 | 5x | MEASURED |
| save stack | 200,000 | a few entries per group | via `max_groups` | 1,411 | 141x | MEASURED |
| font memory / fonts | 8,000,000 / 9,000 | the fonts the admitted commands and characters load: a fixed set | none | 627,721 / 40 | 12x / 225x | MEASURED |
| expansion depth | 10,000 (web2c default; not set in texmf.cnf) | recursion of `expand` within ONE command's expansion; nesting of frames and arguments goes through `main_control`, not through `expand` | none | not reported by pdfTeX; every admitted name is probed at the bounds (R-NEST-*, R-BIG-*, A-R-*, A-CAP-*) | not measured | ARGUED + probed |
| text input levels (`\input`), exception dictionary, hyphenation patterns, alignments, inserts | 15 / 8,191 / ... | the fragment has no `\input`, `\hyphenation`, `&`, `\insert` or float | n/a | n/a | n/a | unreachable by the grammar |
| pdfTeX's own (object table, PDF memory, destinations) | grown dynamically | pages bounded by `max_tokens` | none | the page-heavy probes (6,666 forced pages, C-86 review) compile | not measured | MEASURED (C-86) |

**C-96: RULE R-INERT's closure never entered expl3 code (D-2 of the ADR-013
design review), and `\meaning` text was parsed as if it were unambiguous
(D-3).** `body_tokens` took `\\([A-Za-z@]+)` of a printed expansion text as
its control words: `\hook_use:nnw` was read as `\hook` (recorded meaning
"undefined") and the walk stopped there, silently; and a meaning printed
`\protected\long macro:` (no space between the prefixes) did not match the
macro pattern, so `\par`'s own code — expl3, with paragraph hooks and a
conditional — was never read at all. Six admitted names reached `\par`. The
same shape as C-92: the published rule said "the expansion closure" and the
code computed a smaller set. FIX (`check_strict_kernel.body_readings`,
`meaning_kind`; generators' `dump_meanings` by the hex of each name, so any
name is dumped exactly): an expansion text is read by TeX's printing rules
(`print_cs`: a name of two or more characters is followed by one space, a
one-character name only when it is a letter), and because a printed text
can have several readings (names may hold spaces and backslashes;
category codes are not printed), EVERY reading is taken: every name of the
closed world the rules allow at a backslash, and the longest printed name
even outside it; a backslash with no reading is a character token; every
printed character that may be active at body start (the lexical
contract's catcode 13: `~`, `^^` notation, each byte of a non-ASCII
character) is followed to that active character's meaning. A reached
meaning of a kind the rule cannot classify REJECTS the name
(unresolvable), never ends the walk. Over-reading only adds names, so it
can only reject more. MEASURED (phase-1 generator version 5, the pinned
image): 212 of the 400 candidates are not inert (127 before); 34 of the 121
admitted names drop — `\IJ`, `\SS`, `\dots`, `\j`, `\textcompwordmark`,
`\textgreater`, `\textquoteleft`, `\textvisiblespace` reach `\immediate`
through `\GenericError`; `\bigskip`, `\ddag`, `\dospecials`, `\mathstrut`,
`\obeyedline`, `\sloppypar`, `\subitem` and 19 `\text...` symbols reach
`\afterassignment` through `\@defaultunits` (the font loader and `\par`'s
error path, e.g. `\bigskip` → `\vspace` → `\@restorepar` → `\par` →
`\msg_error:nnnn` → ... ; the walk also over-reads, e.g. the token `\[` of
``\catcode`\[`` in `\nfss@catcodes`, which is how a screen should err). 87
admitted, no new name. The one-argument candidates (the same fix makes
`\protected\long` macros with parameter text `#1` candidates): 184, 123 not
inert, 9 admitted (above). No probe or differential document had shown a
wrong verdict for a dropped name.

**LOW-1 of the review, recorded as a precondition.** An argument that runs
as a FORMULA inside an hbox (`\lefteqn` → `\rlap{$\displaystyle #1$}`) is
not a math group: a `$` in it closes the formula ("Extra }, or forgotten $"),
where a math-group payload (`PMath`, `R_dollar_group`) gives "Missing }
inserted". `Contract.v`'s `pay` does not distinguish the two. It is not live:
the one admitted math-payload command, `\underline` in math, runs its
argument as a math GROUP (TeX's `\underline` reads a math field), and its
A-M-DOLLAR probe agrees. A formula-payload command would fail that probe's
message class and be rejected at stage 1 (INFERRED from `_strict_s0.agrees`:
its E5 row for a `$` in math accepts "Display math should end with $$" and
"Missing } inserted", not "Extra }, or forgotten $"; no such candidate
reached stage 1 under the current selection). PRECONDITION
for admitting any command whose argument runs as a formula: split `PMath`
into a math-group and a formula payload, with the `$`, `\)` and `}` rules of
each.

**LOW-2 of the review: reuse provenance.** The evidence files named
`/private/tmp` files as the sources of reused grades, which nobody can
re-read. A reuse source is now a file COMMITTED to the repository
(`_strict_s0.committed_source`: `REV:path`, recorded with path, commit and
sha256); the local grade store is gone (a grade nobody else can read is
not evidence); `check_strict_kernel.py` / `check_strict_bytes.py` check 12
refuse any other source and verify the sha256 when the commit is present.
Every evidence file of this step was regenerated under the rule.

**Re-attested after C-94 and C-96** (the pinned image, a private container
of it; every reused grade from a committed evidence file, by path, commit
and sha256): `capacity.json` 321 of 321 frame-kind pairs agree at 200
groups, are outside at 201, and overflow in pdfTeX where the account says;
rule probes 737 of 737 graded agree (980 outside by design; dormant under
the contract: `R_arg_{text,math}_{now,after}`, `R_par_short`,
`SC_par_outer`, `SC_par_short` and now `R_cs_math_fatal`, since C-96 left no
admitted name that is fatal in math); differential v4 (generator version 4,
seed 4) 3,000 of 3,000 agree — 133 of its documents stack three or more
frame kinds past 50 groups and 40 sit at exactly 200; byte-level probes
3,064 of 3,064 (the L0-bounds family now at the group bound, and the
reviewer's shape one level past it among the near-misses); byte-level
differential (seed 6) 3,500 of 3,500. The reviewer's files `over128*.tex`
are NOT-IN-FRAGMENT ("capacity bound"); so are 101, 126 and 127 levels (the
bound is conservative: pdfTeX compiles 127); 100 levels are PROVEN-READY and
compile.

**C-98: the SAME class again, for main memory — the capacity table's own
numbers were never measured at the worst case (BLOCKING, round-2 review,
2026-09-29).** The table above said main memory was bounded "through
`max_tokens`" (758,796 words, 6.6x), measured on 20,000 flat characters.
But pdfTeX keeps a COPY of every argument a command is running, and a
command nested in an argument reads its argument out of the outer copy:
memory grows with DEPTH x TOKENS. MEASURED by the reviewer: 197 `\mbox`
levels around 6,427 `\frame{}` (19,983 tokens, 200 groups) were PROVEN-READY
and give "! TeX capacity exceeded, sorry [main memory size=5000000]"; 5,000
to 6,000 frames compile at 4.19M to 4.93M words; the real margin was ~1.05x.
The gate's "usage at most half the capacity" read the table's own
`max_used`, which was never measured at the worst case. This is the second
multiplicative miss in a row (C-94 was groups x frame kinds), so the METHOD
changed, not the instance:

- **Every capacity gets a worst-case account in the model's terms, each
  coefficient measured by an adversarial maximiser, and the bound goes into
  the Coq membership.** For main memory: `Decide.mem C ts = node_cost +
  held` (pinned). Every token costs its `c_cost`, a new field of
  `Contract.v`: the words its nodes and its running take. It is MEASURED
  per admitted name by the phase-1 generator's stage C (the name repeated
  4,000 times in text, in a formula and in a display, and again at the
  memory bound, until pdfTeX's report is within the account) [SUPERSEDED by
  C-104 below: per-occurrence figures under a high-water mark under-count,
  83 of the 84 math bound records had no report, and the account was 1.242x
  short on a reviewer's document; costs are now slopes, and the dimension
  bound was missing altogether]; every other
  token costs the structural stage's most per token, 18 words. Every token
  inside an argument also costs its command's `as_copy`, a new field of
  `asig`, MEASURED by the argument generator's stage G as the slope of
  memory over the tokens held: 2.01 words per model token for every admitted
  command (two TeX tokens per model token of the rendered form), rounded up
  to 3. `held` sums over EVERY argument the stream reads, an over-count of
  what is alive at once. `bounded` requires `mem <= max_mem` = 2,000,000
  words; with the 435,796 words pdfTeX reports at body start the account is
  2,435,796, under half of main memory. `strict_mem_bounded` (Closed,
  capstone 28).
- **The maximiser at the bound and one past it, for every admitted name and
  command, graded.** Phase 1 (stage 3c): each name repeated to the memory
  bound — the costliest, `\ddots` at 156 words, 12,819 times in one formula,
  reports 2,411,456 words, under the account's 2,435,770 and under half of
  main memory (2.07x) — and once more, which is outside. Slice A (stage 3c):
  for each command and mode, as many levels as the group bound allows (200,
  or 66 for `\frame` and for `\underline` in text), the costliest filler
  valid in a box (`\fmtversion`, 62 words) innermost and at the outermost
  level, tuned to `mem` within one token of 2,000,000; all 18 compile (the
  worst, `\underline` in math, reports 1,187,124 words); one more character
  is outside every time. The reviewer's file is NOT-IN-FRAGMENT ("capacity
  bound": its account is ~11.4M).
- **The other capacities, and why each is additive (no product term).** The
  string pool, strings and hash take one entry per NAME READ; a copy of an
  argument re-reads no name (the names are already in the hash): bounded by
  `max_tokens` x `max_name`. The input stack takes one level per running
  argument plus a constant for the macro being expanded, the parameter stack
  one per running argument, the semantic nest one per hbox, formula or math
  group plus the paragraph, the save stack a constant per group (a local
  assignment is saved once per group level, TeX's `eq_save`): each is
  bounded by the frames alive, i.e. by `max_groups`. The buffer holds one
  line; font memory the fixed set of fonts. Expansion depth is per command,
  not per frame. pdfTeX's own report of each, maximised over EVERY graded
  document (the pairs at 200 groups and their overflow searches, the
  transients, the usage documents, all memory worst cases and bound
  documents), is in the evidence files; check_strict_kernel.py recomputes
  that maximum from the records and fails on any capacity more than half
  used. MEASURED maxima (over documents at AND past the bounds): main memory
  2,411,456 of 5,000,000 (the `\ddots` bound document), string pool
  1,939,424 of 5,408,265, semantic nest 255 of 1,000, buffer 20,110 of
  200,000, hash 49,161 of 615,000, input stack 511 of 10,000, strings 19,741
  of 467,099, font memory 627,721 of 8,000,000, parameter stack 255 of
  20,000, save stack 1,793 of 200,000, fonts 40 of 9,000.
- **Gates recompute every derived number from primary records (M-1,
  M-2).** check_strict_kernel.py re-derives the token cost, every name's
  cost, every command's copy factor and cost floor (from the graded
  documents' reported memory), every command's groups `g` (from stage G's
  graded depths, not from the count stored beside them), the grouping
  capacity and the largest transient (from the recorded bisection steps),
  and the capacity maxima (from every record). The new
  check_strict_capacity.py (binary level, in ci.yml's build job) re-runs the
  extracted decider: the SET of frame pairs (not the count), the bytes, peak
  and verdict of every pair stream, and the bytes, memory account and
  verdict of every memory worst case and phase-1 memory document.
  Kill-tests: a pair dropped with its count decremented, a forged peak, a
  forged worst-case account, a consistent forged `g`, a forged low name
  cost, the memory bound dropped from `bounded`.

**R-INERT, LOW-4 of the round-2 review.** The closure now also rejects a
name whose expansion reaches a DEFINITION or an ASSIGNMENT primitive
(`\def` ... `\let`, `\global`, `\advance`, `\multiply`, `\divide`,
`\setbox`): `\gdef\mbox{x}` in a closure changes what a later token means.
Measured: 3 phase-1 names drop (`\thicklines`: `\let`, changes `\frame`'s
rule width; `\reversemarginpar`: `\global\let`; `\narrower`: `\advance`);
84 remain; no argument command is affected. KNOWN LIMITS of the screen
(none live today by the reviewer's TeX scan; the probes remain the
behavioural check): an assignment to a register or an internal parameter
written as `\dimen13=...` or `\hsize=...` is invisible in a printed meaning
(the register token reads as a value); an active character that is not
active at body start but is made active inside a closure; `^^`-notation
names read as `\^`; token lists run implicitly by primitives (`\everypar`
via `\indent`/`\leavevmode`, `\everyhbox` via `\hbox`, the output routine).

**Re-attested after C-98** (supersedes the counts of the paragraph "Re-attested
after C-94 and C-96" above; the pinned image, a private container; every
reused grade from a committed file): phase-1 signatures (generator version 6)
84 admitted, every one with a measured cost and at the memory bound; argument
signatures (version 3) 9 admitted, copy factor 3, costs 1 (`\mbox`) to 124
(`\frame`), 18 memory worst cases; `capacity.json` (version 2) 321 of 321
frame pairs at 200 groups, 201 outside, overflow in the account's window,
every bisection step and transient step recorded; rule probes 737 of 737
graded agree; differential v4 (seed 4) 3,000 of 3,000 (one generated draw
outside the tier, after an empty `$$` opened display math, replaced and
counted); byte-level probes 3,064 of 3,064 (the reviewer's memory file among
the near-misses, outside); byte-level differential (seed 6) 3,500 of 3,500.

**C-104: an UNMODELLED CAPACITY, dimensions (BLOCKING, round-1 review of
the C-98 fix, 2026-09-30), and the memory account was not the upper bound
C-98 said it was.** TeX stores a dimension as a signed 32-bit count of sp
(2^31 sp = 32,768pt) and adds widths without an overflow check (tex.web
`hpack`). REPRODUCED under the pinned oracle: `\[` and 3,277 `\quad` (50 a
line) `\]` was PROVEN-READY (3,282 tokens, 1 group, mem 59,076) and stops
with "! Dimension too large." at `\end{document}` (`<argument>
\box_wd:N \l_shipout_box`), rc 1, no PDF; 3,276 compile. The natural width
wraps negative, the squeeze of §1199 is skipped, the display's shift is
huge and LaTeX's shipout scans the page box's width. The failure depends
on the wrapped arithmetic (a display of 6,500 `x`, past 2^31 sp too,
compiles; `\mbox{` 3,300 `\quad` `}` in a paragraph compiles), so the
fragment EXCLUDES every document in which any dimension could get near the
limit, rather than modelling which overflows fail. Same class as C-94 and
C-98: a capacity with no account. The fix, by method:

- **The account (Coq, `Decide.v`).** `Contract.v` `c_dim : bool -> tok ->
  nat`, the dimensions in whole points a token contributes when it runs in
  math (`true`) or text; `Decide.dim` = the largest sum of `c_dim` over a
  SEGMENT of the run (`dim_run`: the tokens between two paragraph breaks
  read with no frame open, where TeX ends the paragraph; each token in the
  mode it runs in, the innermost frame's; up to where the run stops: a stop
  halts pdfTeX, and the scanner of a deferred error typesets nothing; a
  segment starts with a paragraph break's cost, a paragraph's indent and
  fill). `bounded` requires `dim <= max_dim` = 8,000pt, under half of TeX's
  largest dimension (16,383.99998pt, max_dimen, which every scan of a
  dimension checks). `strict_dim_bounded` (Closed, definitional, like
  `strict_mem_bounded`: that the account bounds pdfTeX is part of the
  attested premise `Faithful`). `Explain.first_wide` reports the first token
  past it ("capacity bound").
- **Why a segment's sum bounds every dimension (the argument; not proved).**
  Every dimension pdfTeX STORES or SCANS while it typesets a paragraph is a
  sum, each term with a coefficient of at most one, of the dimensions of the
  nodes the paragraph's tokens make, plus constants of the layout: an
  hbox's width is its items' sum and its height the largest; a vbox's height
  the sum; a script's shift at most its nucleus's height plus a font
  constant; a limit's width the largest of the operator's and the limits';
  a display's centring shift at most `\hsize` plus its width; a hyphen at a
  line break, one a line. A page holds at most one item past its goal. So
  if each token is charged at least the absolute sum of the dimensions of
  the nodes IT makes, plus what TeX inserts at its boundary with the token
  before, every dimension is at most the segment's sum plus constants under
  1,000pt, i.e. under 9,000pt < 16,383.99998pt. A glue's SETTING is not
  such a dimension, and it is NOT bounded by the account (C-105; the C-104
  text said "a glue's setting at most the box's target plus its natural
  width", which is false: the admitted `\negthickspace` has NEGATIVE
  stretch, three of it against five interword spaces leave +10 sp of
  stretch on a line, and a line forced by `\break` is set with a ratio past
  20,000, each interword glue millions of points wide, on an account of
  914pt; the round-2 review, reproduced). tex.web stores a setting as a
  RATIO (`glue_set`, a real; hpack §649-§667, vpack §668-§679); a set width is
  computed only when a box is shipped out (`hlist_out`/`vlist_out` and
  pdfTeX's `pdf_hlist_out`/`pdf_vlist_out`), clamped to plus or minus 10^9 sp
  by `vet_glue` (§625, §634), added to the output position and never stored
  in a node or scanned; pdfTeX's only size check at shipout ("Huge page
  cannot be shipped out", §641) reads the page box's STORED dimensions;
  §1146-§1148 replace the pre-display size by `max_dimen` whenever a line's glue
  is set; and the one place that folds a setting into a stored width, an
  alignment's spanned columns (§808-§810), is unreachable in the fragment (no
  admitted name or command makes an alignment). So a setting cannot make a
  dimension error; that rests on this reading of tex.web and on the rule
  probes' family GLUESET (lines with cancelling stretch forced by `\break`,
  set past a ratio of 20,000, and a display after such lines (§1146), all
  graded: they compile), not on the account.
- **The costs, MEASURED (`_strict_dims.py`; evidence
  `corpora/strict_s0/dims_s0.json`, `dims_s1.json`, by sha256).** TeX's own
  dump (`\showbox`, depth and breadth unlimited) of `\hbox{t}` in text and
  of `\hbox{$\<style> t$}` in each of the four math styles; per item the
  sum over EVERY node of the dump, nested boxes included, of |w|+|h|+|d|+
  |shift| (boxes, rules), |w|+|stretch|+|shrink| (glue, every order at its
  raw value), |kern|, the math nodes' surround, and a character's
  width+height+depth (`\fontcharwd/ht/dp` of its font, a second run), less
  the empty context. The BOUNDARY constants over every pair measured:
  B_text 3.194pt (the largest INV(ab)-INV(a)-INV(b) over every two of the
  text font's 128 codes and every name and command with every safe
  character, both ways: kerns and ligatures); B_math 5.555pt (every two math
  items, the eight atom classes among them, in the display and text
  styles: the largest inter-atom glue). `c_dim` in text = INV + B_text (0
  extra for a token that makes no node); in math = the largest INV over
  the four styles + atoms x B_math (atoms: TeX's `\showlists` of the
  noads). Structural tokens: a character its own (per character, text and
  math), a space the worst interword glue after any safe character (the
  space factor), a script the largest construction over every nucleus and
  style (34.667pt), a math group its box and one atom, `$`/`\[`/`\]` the
  display skips, a paragraph break `\parindent`+`\parfillskip`. A token
  that stops pdfTeX in a mode costs 0 there. The argument generator
  measures its commands with an empty argument (their contents are charged
  to their own tokens) and REJECTS a command any of whose boundaries or
  scripts exceeds the phase-1 constants (none did).
- **Attested at the bound.** Every admitted name with dimensions in a mode:
  one paragraph / formula / display of it with as many as the account
  allows, graded (agrees), with pdfTeX's own measure of the same material
  in one box (|wd|+ht+dp) within the account; and one more, outside
  (`dim_bound` of the signature file). The repetition families of both
  generators are cut into paragraphs and formulas within the bound
  (`Dims.segment`), the nesting families go as deep as both bounds allow,
  and `A-R-BIG-ARG` is an argument of empty groups (no nodes) at the token
  bound, `A-R-DIM-ARG` one of characters at the dimension bound. The rule
  probes' BOUND family adds a paragraph, a formula, a display of characters
  and a display of `\quad` at the bound and one past it, and the review's
  3,277-`\quad` display; the byte probes' L0-bounds hold the token bound in
  paragraphs of 399 characters and the line bound in braces and in spaces
  inside a formula (a 10,000-character line is one paragraph past the
  bound). The review's two files are NOT-IN-FRAGMENT ("capacity bound").
- **Coverage cost (measured, the fragment NARROWS):** a paragraph or formula
  now holds at most 614 `x` (text) / 498 (math); no admitted name or command was lost (84 names, 9 commands, as before); what narrows is the document: a paragraph of more than ~600 characters, a display of more than 719 `\quad` (a formula of more than 725), more than 7 `\hidewidth` or 22 `\centerline` in one paragraph, 100 levels of `\mbox{$`...`$}` (a `$` is charged a display's skips, since `$$` opens one), 199 nested scripts. The fragment's documents that were at the token bound in ONE paragraph or formula (R-BIG, the BOUND family, the byte bounds, the capacity usage documents) are now cut into paragraphs or formulas.

**The memory account was not an upper bound (MEDIUM x3 of the same review,
all REPRODUCED), and its gates did not check what they said.** (1) 19,000
adjacent `\ttdefault` in one formula: pdfTeX 860,536 words, 424,740 over
the base, against the account's 342,090 (1.242x), compiling; 12 of the 83
names' own bound documents and three display-limits shapes
(`\[(\sum^x_x)`x3,999`\]` 1.232x) likewise. CAUSE, measured: pdfTeX's report
is a HIGH-WATER MARK and the base document's already holds ~31,000 words
`\begin{document}` allocates and frees, so a document's report is
max(M0, B + c n) with B < M0; C-98 took (used - M0)/n, which is (B - M0)/n
+ c < c (`\ttdefault` in text: 8.17 at 4,000, 14.44 at 19,997), and missed
the memory a neighbour of another class adds (inter-atom glue) and that
TeX's hyphenation adds inside words (a rendered document never holds a
word; a file does). (2) 83 of the 84 math bound records had no pdfTeX report
(their grades were reused from a file that kept no statistics) and the
gate's within-account check skipped every such record. (3) The binary gate
checked only the bytes and token count of the phase-1 memory documents,
never their account or verdict; a PAST record's account forged inside the
bound, a forged at-bound cost, deleted bound records and a forged
structural record all passed. FIX, by method: every cost is the SLOPE of
pdfTeX's report over the count, at three counts (k1, 2 k1, 4 k1; k1 = 4,000,
or 1,000 units with scripts; lower when that would pass 1.8M words of
material), each difference of two reports widened by 1,000 words (pdfTeX
grows its variable-size memory 1,000 words at a time, so a report is up to
that much above the words in use: MEASURED, every report is a multiple of
1,000 there). A context whose second-largest level still reports only the
base proves only c <= slack / count, and the gate requires that bound under
the cost charged, with the slack MEASURED (the largest M0 minus the linear
intercept over every context past the mark: 34,260 words). Display contexts
are one box, whose width wraps past 2^31 sp and may stop the run, so they
hold at most 12,000pt of the name and reach past the mark with a ballast of
4,000 empty math groups (Ord atoms of no width) before it; the raw
class-pair instruments reach 2,590,536 words, under main memory. Five
contexts per name (text, formula,
display, and with a super- and a subscript in a formula and a display), plus
per letter it prints the memory of a letter in a hyphenated word
(H_text 3 words, a byte-level instrument) and per atom the largest
inter-atom excess over the 64 class pairs (B_math 17 words); the token
cost likewise over the structural shapes at three levels (19 words). Every
graded memory record must carry pdfTeX's report; pdfTeX's report must be
within the account on EVERY record (instruments, bound documents, worst
cases, and the review's five documents, now recorded); the binary gate
rebuilds every record (structural levels, contexts, bound and dimension
documents with their box instruments, review, stage G) and requires its
bytes, token count, memory and dimension accounts and verdict to be the
model's, one past a bound outside, and the report within the committed
account. The claims "EXACT account ... never a proxy" (Decide.v) and
"iterated until pdfTeX is within the account" (C-98) are withdrawn: the
memory account is an upper bound on every one of the 1,413 graded records
it is checked on (1,721 carry pdfTeX's report; stage G's are counted under a
raw contract and checked by the binary gate under the committed one; worst
0.933, the review's documents at most 0.693), not proved; the membership
bound leaves more than 2x (at most 1,112,259 words measured inside the
fragment, of 5,000,000). The binary gate now re-runs ~20M tokens of
documents (90-250 s of CPU); its kill-tests have their own 1,200 s bound in
check_gate_selftests.py.

KNOWN LIMITS (C-104): the dimension account's argument that every
dimension is a coefficient-one sum is an argument about tex.web, not a
proof, and its constants of the layout are covered by the headroom, not by
a measurement of each; per-token dimensions are measured in isolation per
style with pairwise boundaries, so an interaction of three tokens is bounded
only through the per-atom charge; the memory account is attested (every
graded record within it), not proved, and a context no instrument builds is
covered by the 2x headroom only.

**C-105: the memory account was still not an upper bound where a page never
ships, and the dimension argument's glue-setting clause was false (round-2
review of the C-104 fix, two MEDIUM, three LOW, all REPRODUCED).**

*Retention (MEDIUM).* pdfTeX frees a page's nodes only when the page ships,
and a page ships only when its material passes the goal. `\offinterlineskip`
(admitted) makes the interline glue `\lineskip` = 0pt, and paragraphs of
material without height then add nothing to the page: every paragraph's
nodes stay in main memory to the end. The review's document (`\offinterlineskip`
and 9,998 `\leavevmode` paragraphs) was READY with an account of 380,000
words and pdfTeX used 891,000 over the base (2.34x; `\thickspace` 1.91x,
`\frame{}` 1.19x). EVERY memory instrument had let its pages ship (the
structural shape `char-par` measured 0.2 words a token: its pages shipped
and freed it). The class: an instrument that frees what it should measure.
FIX, by method: (1) THE RETENTION REGIME (`_strict_capacity.RETAIN`,
`retain`): every memory instrument (structural shapes, class pairs, the
names' contexts, stage G's documents, the hyphenation bytes) is graded with
`\global\vsize\maxdimen`, `\baselineskip` 0pt and `\lineskiplimit`
-`\maxdimen` (so the interline glue is ALWAYS a new baselineskip glue with
its own specification, the most memory TeX spends between two lines, of
zero net height) and zero display skips (param glue: the same nodes).
MEASURED on the review's shape: 93 words an empty paragraph in the regime,
89 under `\offinterlineskip`, 47 inside a `\vbox` (a box is NOT an upper
bound: the main vertical list's allocation pattern costs more for the same
nodes, so the regime is the page itself). Every instrument must report ONE
page (`log_stats` "pages"; a level that shipped more is refused, never
used), and the binary gate requires every instrument's bytes to be the
model's rendering with `RETAIN` inserted. (2) The SHORTEST units that make
what a page keeps are structural shapes: a paragraph ended after each kind
of token that starts one (`char-par`, `group-par`, `inline-par`,
`paren-par`, `display-par`, `bracket-par`), an empty display
(`bracket-empty`, `display-empty`), a display after a character, an empty
formula; the token cost rises from 19 to 48 words (`char-par`, 0.972 of it).
(3) Two new contexts per name that runs in text, PAR (the name, then a
paragraph break) and XN (a character, then the name: it ends the paragraph
or the line the character started), and G-MEM-PAR / G-MEM-XN for the
argument commands; in them the name is charged the WHOLE unit (the other
tokens at 0), because what a page keeps of a paragraph is a pair effect of
the token that starts it and the token that ends it, and subtracting the
token cost (the largest over the shapes) would under-charge a paragraph
started by one name and ended by another. Costs: `\leavevmode` 19 -> 95,
`\quad` 37 -> 95, `\thickspace` 33 -> 105, `\break` 29 -> 56, `\mbox` 1 ->
121, `\frame` 122 -> 246; H_text 3 -> 5, B_math 17 -> 27 (the regime and
the class pairs now at 5,000/10,000 units: at 16,000 the largest had used
2,590,536 words, past half of main memory, which the capacity table never
saw because the class-pair records kept no statistics). (4) The worst cases
at the bound: R-KEEP-TEXT for every name that runs in text
(`\offinterlineskip`, then the name as a paragraph of its own, as often as
the fragment allows, and once more outside: 34 names, pdfTeX at most 0.648
of the account, 1,427,796 words) and `text:keep` for every argument command
(9, at most 0.609, 1,632,796 words: `\frame{}`, the most any graded
document in the fragment uses, of 5,000,000); the review's five documents
are recorded (R-REVIEW2-*) and within the account (0.62-0.77). WITHDRAWN:
C-104's "pdfTeX within the account on every one (worst 0.933)" and
"MEASURED upper bound" as stated there held only for records whose pages
shipped.

*Glue settings (MEDIUM).* The argument's clause "a glue's setting at most
the box's target plus its natural width" is withdrawn (above, "Why a
segment's sum bounds every dimension"): stretch of opposite signs cancels,
and the review's document (`x x x x x x$\negthickspace` x3`$\break`, four
times) is READY at 914pt and sets its lines with a ratio past 20,000. The
account bounds the dimensions TeX stores and scans; a setting is a ratio
computed into a width only at shipout, clamped, never stored or scanned
(the reading of tex.web above), attested by the rule probes' family GLUESET
(three documents at a ratio past 20,000, graded; model rendering puts a
space after every character, so the lines hold five and two characters).

*LOW.* (a) The review documents: the pure gate now requires EVERY one whose
names are admitted to be recorded, with a grade and pdfTeX's report (it
required 3 of 5 and skipped an ungraded one). (b) The class-pair
instruments are rebuilt by the pure gate (bytes and units, the complete
set), and every dimension measurement must be its plan
(`_strict_dims.plan_for` of its recorded names and commands): items,
nuclei, pairs, the chunks' boxes in order and each chunk's two instruments'
bytes (`check_strict_kernel.dims_plan_findings`). (c) The branch's C-100 is
C-104 (the spike holds C-100, C-102, C-103; main C-101); origin/main merged.
Kill-tests: two review documents dropped, one stripped of its grade, a
class-pair's units forged, the measurement's plan forged, an instrument
that shipped two pages, a name's R-KEEP dropped (pure), and `retain` made
the identity (binary: every instrument "other bytes than the model's in the
retention regime").

**Re-attested after C-105** (supersedes "Re-attested after C-104" below;
the pinned image, a private container; origin/main merged first):
phase-1 signatures (generator version 8) 84 admitted, token cost 48, H_text
5, B_math 27, costs up to 455 words (`\fmtversion`); 1,695 account-checked
records, pdfTeX within the account on every one (worst 0.972,
`S:char-par`); argument signatures (version 5) 9 admitted, 45 memory worst
cases (9 of them `text:keep`) within the account, at most 1,632,796 words;
`capacity.json` 321 of 321 frame pairs; rule probes 744 of 744 (GLUESET 3
of 3); differential v4 (seed 4) 3,000 of 3,000 (158 draws outside the tier
replaced); byte-level probes 3,076 of 3,076; byte-level differential (seed
6) 3,500 of 3,500. The review's documents under the C-104 account and this
one (pdfTeX's report over the base / the account): `\leavevmode` 2.345 ->
0.623, `\thickspace` 1.908 -> 0.648, `\quad` 1.591 -> 0.623, `\(\)`
1.939 -> 0.768, the mixed document 2.299 -> 0.624.

KNOWN LIMITS (C-105): the regime is argued to be the worst allocation of
what a page keeps (no page ships, a new glue specification between every
two lines) and MEASURED to be at least `\offinterlineskip`'s on the review's
shapes; pdfTeX's report is the extent of its memory (tex.web §639's
lo_mem_max and hi_mem_min), which depends on the ORDER of allocations and
frees, so an account of per-token costs is attested on the graded records,
not proved; units longer than the ones measured (three tokens and more
interacting) are covered by the per-token maxima and the 2x headroom only.

**Re-attested after C-104** (supersedes the counts of "Re-attested after
C-98"; the pinned image, a private container; every reused grade from a
committed file of this branch): phase-1 signatures (generator version 7)
84 admitted, every one with its memory cost (slopes over three counts in up
to five contexts; token cost 19, H_text 3, B_math 17 words) and dims
(`\hidewidth` 1,005pt the widest), 164 dimension-bound documents and their
box instruments, the review's five memory documents within the account;
argument signatures (version 4) 9 admitted (`\numberline` still rejected at
stage 2), dims 0-353pt in text, 36 memory worst cases (a filler of no
dimensions, `\break`, reaches the memory bound; the costliest, `\fmtversion`,
the dimension bound first) all within the account, at most 1,112,259 words;
`capacity.json` (version 3) 321 of 321 frame pairs at 200 groups and 201
outside, with streams kept within the dimension bound; rule probes 741 of
741 graded agree (the BOUND family with the dimension bound and the review's
3,277-`\quad` display outside); differential v4 (seed 4) 3,000 of 3,000
(158 generated draws outside the tier, now mostly by the dimension bound,
replaced and counted); byte-level probes 3,064 of 3,064 (the review's file,
byte for byte, among the near-misses, outside); byte-level differential
(seed 6) 3,500 of 3,500.
