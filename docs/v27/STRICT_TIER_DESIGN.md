# Design: the contract-bounded proven tier

**Status:** approved design, adopted by [ADR-012](adr/ADR-012-contract-bounded-proven-tier.md) on 2026-09-26, which records the owner's answers to §H verbatim. Milestone M0 (§F) is implemented; nothing is proven yet. Programme ledger row: OPEN-116 in [PROJECT_STATE.md](PROJECT_STATE.md).

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
- a new gate checks the corollary's *statement* textually, so that `Faithful` is its **only** non-structural premise.

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
   - Nor for any other name whose use changes a catcode or the group level, or takes the next token other than as a macro argument (review of 2026-09-27, C-82): `\obeylines`, `\obeyspaces`, `\dospecials`-style catcode changers, the `\@sanitize` users (`\index`, `\glossary`), `\string`, `\noexpand`, `\meaning`, `\aftergroup`, `\enddocument`, `\stop`, `\bgroup`/`\begingroup`. This list is not hand-maintained: since signature version 2 the **follow probe** (§I.4) attests, for every name and cell, that the token after the use is the next one executed with all 256 catcodes and the group level unchanged, and a name that fails it has no attested shape, so its uses are outside the tier. (`\dospecials` itself passes at body start in `article`: `\do` is `\noexpand` there, so it changes nothing.) Since signature version 3 (§I.4, round 2, C-90) the same probe also compares the group type, the conditional level and the kernel's allocation registers, reads the mode the use leaves (a use that leaves another mode composes only through an attested transition to the cell of that mode), and reads from `\tracingassigns` whether the use changed the meaning of any name a body can type; a use that allocates or redefines is outside the tier, as is one whose 300-fold repetition or whose run with every counter at 27 or −1 fails.
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
| `signature(name, mode, context)` | `allowed : Ok \| Fatal msg`, plus `args : [kind ∈ {req, opt, star}, argty, long]` | Candidates come from the ltcmd spec in the meaning, the `\@protected@testopt`/`\@ifstar` idioms, and the outer-sentinel arity probe (`\outer\def\STOP{}`, then `\cs{x}^n\STOP`). **A shape read is a hint, never attestation**: static `#n` arity disagreed with behavioural arity on **121/405 = 30%** of macros [M]. Payload lattice: `{a}`, `{1pt}`, `{equation}`, `{example-image}`, `{http://x}`, `[width=1cm]`, a counter name | **solo** `-halt-on-error` probes, **one variable each**, classified by *error class*, not rc. Positive probes: a well-typed use compiles, in T, in M, and in each context. Negative probes: wrong mode, `\par` in the argument (long-ness), a missing argument. **Batched probes are triage only**: batch-vs-solo polarity agreement was 142/143 [M]. A 15 s timeout guards against the MetaPost-support hangs [M]. **As built since signature version 2 (§I.4, C-82):** the sentinel attests only macro-parameter consumption, so every shape also needs a passing *follow probe* in every cell it is used in, argument types are read from three error-class witnesses, and every type is confirmed through the configuration's consumers (and, for TyLabel, processed at the use). **Since version 3 (§I.4 round 2, C-90):** what a use leaves behind is attested too (mode and transition, allocation, redefinition, repetition, counter values, page position), typeset types must survive a moving argument, TyLabel is a key, and numeric types must take other values |
| `environments` | begin-args, body mode, the context it pushes (list, float, alignment n, theorem, display) | `\X` and `\endX` both in `defined_names`, plus the same probe families | solo |
| `definer_rules` | pin-level semantics of each admitted definer | a probe table (13 probes [M]). Plausible hand rules are false at the pin: `\newcounter{lemma}` followed by `\newtheorem{lemma}` **compiles** (in the kernel only: under amsthm it is fatal, C-81), and `\newcommand` on a `\relax`-meaning name compiles [M] | the table is the attestation |
| `decl_templates` | per declaration command and **owner combination** (kernel / amsthm / amsthm+thmtools / ntheorem): the names it defines, `errors_if_defined`, and `requires` | fresh-name probe (`\newtheorem{zzq}[section]{Zzq}`), then a meaning diff of the zzq family, then collision probes. The amsthm+thmtools template differs, and it reproduces `Command \c@lemma already defined` [M] (graft from product-first). **Corrected by C-81 (measured at the pinned image, 2026-09-27):** it is not only amsthm+thmtools — amsthm ALONE already fails `\newcounter{lemma}\newtheorem{lemma}{Lemma}` (`Command \c@lemma already defined`; the kernel alone compiles it), and under amsthm+thmtools EVERY shared-counter `\newtheorem`, including `\newtheorem{thm}{T}\newtheorem{lemma}[thm]{L}`, is fatal on pass 1, and so is thmtools' own `\declaretheorem[sibling=thm]{lemma}` (amsthm alone compiles the shared form) | collision matrix |
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

- **North Star.** Strict-tier coverage on a **virgin** sample, `#{PROVEN verdict = oracle} / N`. It is always shown beside `strict_wrong`, which counts false-READY, false-NOT-READY, **and wrong reason or location**. `strict_wrong` must be 0 and is published **with its 95% upper bound**: 0/k ≈ 3/k, which is about 30% at k = 10 (graft from product-first). The docs say that a small k is weak evidence.
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
- **Sample hygiene.** Sample 2 has now been used for configuration statistics, ceiling sets and package ranking, so it is **design-seen**. Rankings use frame∖eval. The headline number comes from **sample 3** (ranks 401–600), drawn and graded only after every graded artefact has been re-graded under the frozen oracle image (ADR-012 decision 7). Sample 4 is held in reserve.
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
| strict-tier North Star and heuristic block | `scripts/tools/gen_project_state.py` from `corpora/real_roots/proven_coverage_sample1.json` and `corpora/real_roots/proven_coverage_sample2.json` (field `verdict_tier`) |

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
`openin_any=p`, `openout_any=p`, private `TEXMFHOME`/`TEXMFVAR`), log-width
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
- Not generated yet, deferred to slice 2 or later: `lazy_files` (the probe harness records first-run `.fls` deltas per probe, but no contract field), `environments`, per-mode `u8:` coverage, `decl_templates`, `definer_rules`, `load_delta` kinds, `limits` and `graphics`. Slice 2 (§I.3) generates `signature`, `environments`, `definer_rules` and `decl_templates`; the others are still open.
- The §B.2 attestation of `files_read` (re-run with the file hidden; the expected fatal must appear) is not implemented.
- `complete` is configuration-scoped (above); the per-document self-check is M2's.
- The file-token reading of the universe is an over-approximation checked by the hash count, not a proof by itself; a configuration whose count is not 0 is reported incomplete rather than guessed.

### I.3 M1 slice 2: signature probes (2026-09-27)

*Version 1 as first built. Its exactness test, its argument typing and its
gate were corrected by the adversarial review recorded in §I.4 (signature
version 2, C-82, and its round 2, version 3, C-90); where the two disagree,
§I.4 is current, and the measured figures below are version 1's.*

Data only: nothing reads a signature yet (M2 is the first consumer). Ledger row
OPEN-120.

| deliverable | where |
|---|---|
| signature probes, environments, definer table, batched triage | `scripts/tools/contract_signatures.py`, run as `gen_contract.py signatures --contract C` |
| the on-demand API for M3's use-based attestation | `contract_signatures.probe_names(contract, names, cells=…)`, CLI `gen_contract.py probe-names`; cached per (contract sha256, name, cell) |
| `\newtheorem` declaration templates per owner combination | `gen_contract.py decl-templates` → `corpora/contracts/decl_templates/newtheorem.json` |
| the committed `article` signature sidecar | `corpora/contracts/signatures/article.json` (schema `lp-contract-signatures/1`) |
| pure checks (unit tests; every attested shape re-derived from its own probe log; binding to the contract's sha256; in-gate kill-tests) | `scripts/tools/check_gen_contract_parsers.py` (required `spec-drift`), three new kill-tests in `check_gate_selftests.py` |
| regeneration and TeX kill-tests | `scripts/tools/check_contracts_reproducible.py --signatures [--signatures-sample N]` (local/nightly) |

**Storage.** The signatures live in a sidecar next to the contract, not
inside it. The sidecar names its contract by the sha256 of the contract's
bytes, so a regenerated contract with other bytes makes the sidecar stale
(the parser gate fails on it). Keeping the name-set contract unchanged means
`GENERATOR_VERSION` did not move and the four committed contracts still
reproduce as before; the sidecar carries its own `signature_version`.

**What a signature is, and how each part is attested.** Every fact is a
solo probe under the oracle's own predicate (grading environment, the pass
protocol, `-halt-on-error`, a fresh directory, a 15 s timeout per run),
classified by error class. The mechanism is an `\outer` sentinel,
`\outer\def\lpstop{}`: a macro that tries to take `\lpstop` as an argument
stops with `Forbidden control sequence found while scanning use of`
(class `forbidden_cs_use`, outcome `grab`); a `\futurelet` peek does not.

- *Scope.* Every control sequence a body can type under the body-start
  catcodes (read from TeX, not assumed): a run of catcode-11 bytes, or one
  byte that is not one, that is a member of the contract's closed world.
  2,148 names for `article`. A non-member is E1 and needs no signature.
- *Shape*, in the first cell (text, math, vertical, list, preamble) where a
  use compiles: the mandatory count (`\cs{a}^k\lpstop` stops grabbing at
  k = r); payload types by a search over the lattice, then minimised (a slot
  keeps a non-text payload only if `a` there fails, and that failure is
  recorded as its negative); **exactness**, attested by three probes: the
  canonical use compiles, the canonical use followed by `\lpstop` does not
  grab, and without its last mandatory argument it grabs; optional
  arguments at every position (a count argument: before mandatory argument
  j, `[a]` fills three mandatory slots unless an optional argument consumes
  it); a star flag at position 0; and a brace group taken only if present,
  as `\input` does (`\cs A{\lpstop}` grabs iff it is consumed: kind `gopt`).
- *Per cell* (`text`, `math`, `vertical`, `list`, `preamble`): the canonical
  use's outcome, `ok` or the fatal class and message; outside the base cell,
  `shape_checked` records that nothing more is consumed there.
- *Argument types.* A slot that accepts `a` is typed by what its payload is
  typeset as, one variable each: `a^b` (math-only material) and `$a$`
  (text-only material) in the text and math cells, giving TyText, TyMath,
  TyInherit, or TyLabel when both are accepted (the payload is not typeset
  by the use: a label, a key, a heading's table-of-contents text). Other
  slots are typed by the lattice payload that made the use compile: TyNumber
  `1`, TyDimen `1pt`, TyCounter (the configuration's first counter with
  `\theX`), TyFile `lpprobe` (`lpprobe.tex` and `lpprobe.sty` sit in every
  probe directory), TyCsName `\lpprobecs`, TyNewName `lpq` (both undefined),
  TyEnvName, TyKV `width=1cm`, TyUrl `http://x`. `a\par b` in the base cell
  gives `long`.
- A name whose shape no cell attests is `unresolved`, with every cell's
  outcome of the bare use: its uses are outside the strict tier. §B.2 allows
  this (signature coverage need not be complete; the name set must be).
- *Environments*: X letters with an optional `*`, `\X` and `\endX` members.
  Begin-arguments by the same method with head `\begin{X}` and body `a`
  (then `\item a`); body mode and pushed contexts from one-variable body
  probes (`a^b`, `$a$`, `\item a`, `a\par b`, `\caption{a}`, `a&b`).
- *Definer rules*: a table of 124 probes, each definer on targets derived
  from the closed world (the first name of each meaning kind), in the
  preamble and in the body.
- *Declaration templates*: per owner combination (kernel = `article`,
  `article`+amsthm, `article`+amsthm+thmtools) and `\newtheorem` form (plain,
  shared counter, within, `*`), the names the declaration defines are the
  difference of two COMPLETE contracts (the base, and the base with the
  declaration as a definer): the slice-1 completeness machinery, reused. Plus
  a collision matrix of solo probes.
- *Batched probes are triage only*: each name's solo probes are re-run in one
  nonstop document (each in a group after a marker); nothing in a signature
  comes from a batch.

**Measured (2026-09-27, under the image, arm64; the `article` contract).**

- **2,148 names**: 1,343 attested, 805 unresolved. By meaning kind: macros
  1,026 attested / 264 unresolved; primitives 78 / 468; registers 0 / 70
  (their use is an assignment, which has no brace form); math characters
  179 / 0; chars 17 / 3; `\relax`-meaning names 38 / 0; fonts 5 / 0. Most
  unresolved names fail in every cell before any argument (318 with
  `missing_number`, 56 `missing_open`, 46 `wrong_mode`), or take argument
  types outside the lattice (page styles, font encodings, column specs).
- Base cell of the attested: text 992, math 298, preamble 43, vertical 9,
  list 1 (`\item`). Mandatory counts: 917 take none, 234 one, 112 two, 55
  three, 25 four or more. 53 have attested optional arguments; 24 have a star
  flag (e.g. `\section`, `\\`, `\hspace`, `\vspace`, `\ref`, `\newcommand`),
  319 attested no star, 1,000 unknown (a zero-argument name whose starred
  use cannot be told apart by a grab). One `gopt`: `\input`.
- Typed slots: TyLabel 442, TyText 95, TyInherit 74, TyNumber 61, TyCsName
  31, TyDimen 25, TyMath 20, TyCounter 20, TyFile 5, TyNewName 4, untyped 66.
  Long: 252 slots long, 317 not, 128 whose `\par` fails for another reason.
- **The \meaning hint predicted the wrong mandatory count for 237 of 1,026
  attested names (23.1%)**; the spike measured 121/405 (30%). Examples:
  `\section` (hint 0, attested `[opt]{req}`, and a starred variant
  `*{req}`), `\AtBeginDocument` (hint 0, attested 1), `\DeclareRobustCommand`
  (hint 0, attested 2), `\"` (hint 0, attested 1).
- Cells: text ok for 993 attested names, math 1,148, list 990, vertical 989,
  preamble 494; every accepting cell outside the base re-checked its shape
  (4,705 of 4,705).
- **Environments: 30 of 41 attested.** Unresolved: `tabular`, `tabular*`,
  `array`, `picture` (argument types outside the lattice: column specs,
  coordinates, M4), `document`, `filecontents`, `filecontents*`, and the
  non-environments `L`, `csname`, `input`, `line` (a name X with `\endX`
  defined is not always an environment).
- **Probe counts and cost**: 49,052 solo probes (129,544 engine runs: 2 per
  compiling probe, 3 per failing one), 5.2 hours wall on 8 workers, measured
  while other work held the machine's load average between 100 and 300 (an
  unloaded run was measured at 0.13-0.16 s wall per probe on 6 workers, which
  puts the whole scope near 2 hours). One timeout: `\font` in the vertical
  cell (`\font\lpstop\par x` asks mktextfm to build a font named `x`, the
  §B.2 hang class).
- **Batched vs solo polarity: 41,151 agree, 1,167 disagree (97.2% of the
  conclusive), 6,610 inconclusive** (a batch that stopped or swallowed the
  marker). 881 disagreements are solo-fatal / batch-ok (a group, or error
  recovery, masks the failure) and 286 solo-ok / batch-fatal (an earlier
  probe of the same batch left state behind: e.g. `\newtheorem{lpq}` defined
  twice). The spike measured 142/143. This is why the batch is triage only.
- **Definer table (124 probes), surprises at the pin.** `\newcommand` on a
  `\relax`-meaning name compiles (confirming §B.2) while `\renewcommand` on
  the same name fails `Command \MessageBreak undefined`; `\providecommand` on
  a macro, a primitive or a chardef compiles (it keeps the old meaning);
  `\newcommand{\endlpq}` fails `already defined` although `\endlpq` is
  undefined, and so does `\providecommand{\endlpq}`; `\newcounter{lpq}` after
  `\newcommand{\lpq}` compiles; `\newenvironment` on a `\relax`-meaning name
  compiles; `\newtheorem*` in the kernel takes `*` as the theorem's name
  (`Command \* already defined`); `\theoremstyle` and
  `\DeclareMathOperator` are undefined in `article` (E1).
- **Declaration templates.** Kernel: `\newcounter{lemma}` then
  `\newtheorem{lemma}{Lemma}` compiles (confirming §B.2). **amsthm alone
  already fails with `Command \c@lemma already defined`**, not only
  amsthm+thmtools as §B.2 reads; the templates of the two amsthm
  combinations differ in the names they define (the plain form defines 8
  names under amsthm and 25 under amsthm+thmtools, among them `thmt@`,
  `l@zzq`, `ll@zzq` and `zzqautorefname`). **Under amsthm+thmtools every
  shared-counter form is fatal on pass 1**, including the common
  `\newtheorem{thm}{T}\newtheorem{zzq}[thm]{Zzq}`
  (`Command \c@zzq already defined`, measured with the counters `section`,
  `thm`, `enumi`, `page` and `equation`; thmtools v0.76 2023/05/04, amsthm
  v2.20.6). INFERRED, not measured: the kernel's own shared-counter form now
  defines `\alias@ctr@zzq` (the kernel template shows it), and thmtools'
  2023 code does not expect that.
- **Reproducibility.** `corpora/contracts/decl_templates/newtheorem.json` regenerated byte for
  byte (a full second run). The `article` sidecar was checked on a seeded
  sample of 60 names, each record identical (a full second run was not
  made: it takes hours here; every name's probes are independent of every
  other name's, which is what makes a sampled check meaningful). The
  `article` contract and the kernel file still reproduce byte for byte, and
  every slice-1 kill-test passes, plus eight signature kill-tests: a
  wrapper that reads as arity 0 is attested as one argument, `[opt]{req}`,
  a star flag with two variants, a delimited parameter unresolved, a
  peeked brace group as `gopt`, a text-only macro fatal in math, a
  non-member answered as E1 without a probe, and a cached answer without
  TeX.

**Known limits (recorded, not fixed).**

- Argument types are attested by one payload per type (a parametricity
  assumption, §G.1 risk 1); `\setlength{a}{a}` compiles (it typesets), so its
  slots are not typed as a length and a dimension, and the type stays
  unattested (None). The differential (M2) is what tests the assumption.
- Optional-argument positions and the star flag are attested in the base
  cell only; other cells check only that nothing more is consumed.
- The preamble cell's names are the body-start closed world; a name defined
  in the preamble and removed by `\begin{document}` is not probed there.
- Only `article` carries a full sidecar; `amsart` was not generated (the
  full scope takes hours on this machine under load).
- The sidecar is 4.5 MB (the probe log of every name is kept as evidence).

### I.4 Signature versions 2 and 3: the adversarial reviews of 2026-09-27 and 2026-09-28 (C-81, C-82, C-90)

An adversarial reviewer measured, under the pinned image, that version 1's
signatures were unsound in two ways (C-82) and its gate re-derived too little.
Ledger row OPEN-120 carries the numbers; this section the method.

**HIGH-1: exactness saw one way of taking a token.** The `\outer` sentinel
stops only a macro-parameter scan. A name that takes the next token another
way, or changes how the rest is read, passed `use` + `use\lpstop` as r = 0:
the reviewer's `use\lpundefzz` probe did not stop on `\lpundefzz` for 12 of
918 r = 0 variants. False READY: `\item x \string\end{itemize}` is fatal;
false NOT-READY: `x \index{a^b} y` compiles. **Fix: the follow probe**,
`\lpfsave <use>\lpfollow\lpnocs`, required in the base cell (a fourth
exactness fact) and in every other accepting cell (`shape_checked`).
`\lpfsave` records the catcodes of all 256 bytes and `\currentgrouplevel`;
`\lpfollow` is `\outer` (no macro can take it as an argument) and stops with
`! LPFOLLOW.` if both are unchanged, `! LPSTATE.` if not; `\lpnocs` is
undefined, so a use that defers or reorders the token after it stops there
instead. A name that fails it has no attested shape in that cell (outside the
tier), which covers the §A.1.4 catcode changers by measurement rather than by
a list.

**HIGH-2: TyLabel from one use in isolation, and a witness that toggled the
mode it tested.** Version 1 typed a slot TyLabel when both `a^b` and `$a$`
compiled. That held for payloads another command typesets LATER
(`\section[..]` through the .toc, `\title` through `\maketitle`, `\caption[..]`
through the .lof, `\markboth` through the running heads), and `$a$` inside a
math slot closed and reopened math, so `\pmod`, `\matrix` and `\cases` read as
not typesetting their argument and `\begin{math}`'s body as `either`.
**Fix:** three one-variable witnesses read by ERROR CLASS, so that only
typesetting counts as evidence: `a^b` (`missing_dollar` = typeset in text),
`\"a` (`math_accent` = typeset in math, without toggling it) and `a&b`
(compiles only where nothing is typeset, or inside an alignment, where `\"a`
shows math). Every type is then CONFIRMED: the payloads it admits must also
compile in a *consumer document* (`\title{t}` given; `\pagestyle{headings}`,
`\tableofcontents`, `\listoffigures`, `\listoftables` before the use;
`\maketitle`, a new page and `\leftmark\rightmark` after it; the oracle's
pass protocol); the plain payload `a` must compile there too, else the
type is refuted. A TyLabel payload must also be processed AT the use (`\lpnocs`
there is `undefined_cs`, not stored for later or discarded), each other
text-like slot is also set to `toc`/`lof`/`lot`, and a slot beside two or more
other text-like slots is not TyLabel at all (their joint values are not
attested). A refuted type is None with a `refuted` record naming the probe.

**Calibration.** The design's premises (each witness's class in each mode,
the follow probe on `\relax`/`\string`/`\noexpand`/`\expandafter`/
`\obeylines`/`\bgroup`, the consumer suite catching `\section[a&b]`,
`\title{a^b}` and `\markboth{a&b}`) are re-measured for every configuration
probed (22 probes, recorded in the sidecar); a configuration where one fails
is refused.

**MEDIUM-1: the gate re-derives the whole record.** The probe log now holds
every probe in order, with each fatal probe's message. `check_sidecar`
REPLAYS each name's and environment's derivation on its own log (a
`ReplaySession`: no TeX) and requires exactly the logged probes in the
logged order and a record identical in every field: status, shape, star and
the starred variant, per-cell outcomes, `shape_checked`, `follow`, content
kinds, argty and its refutation, long, negatives, optional positions, body
mode, pushes, attempts, bare-use outcomes. A definer row has no log: its
class must be its message's class, and the sampled TeX check re-runs the
whole table. In-gate kill-tests mutate each field of a committed record, and
seven new `check_gate_selftests.py` mutations undo each fix.

**MEDIUM-2: the reproducibility sample rotates.** Its seed is the
configuration plus a rotation (the commit by default, or
`--signatures-seed`); the 27 adversarial names of this review, four
environments, the calibration and the whole definer table are always
regenerated.

**LOW.** The declaration templates' `defines` now holds only the names that
carry the declared name; scratch and side effects (`@let@token`,
`thmt@tmp`, `cl@enumi`) are `incidental_defines`.

**Measured (2026-09-28, under the image, arm64; the `article` contract; a
full regeneration, 3.9 h on 8 workers while another track shared the
container).**

- 2,148 names: **1,312 attested, 836 unresolved**. Exactly 31 names moved
  from attested to unresolved, all by the follow probe, none the other way:
  the next token consumed or reordered (`undefined_cs`): `\string`,
  `\noexpand`, `\meaning`, `\do`, `\aftergroup`, `\afterassignment`,
  `\expandafter`, `\if`, `\ifcat`, `\ifdefined`, `\index`, `\glossary`,
  `\partokenname`, `\pdfprimitive`; never reached (`ok`): `\enddocument`,
  `\stop`; catcodes or group level changed (`lp_state_changed`):
  `\obeylines`, `\obeyspaces`, `\obeycr`, `\makeatletter`, `\ExplSyntaxOn`,
  the three `\ProvidesExpl*`, `\UseRawInputEncoding`, `\bgroup`,
  `\begingroup`, `\equation`, `\long`, `\outer`, `\protected`. Every other
  accepting cell passes its follow probe (0 accepting cells unchecked).
- Types: **TyLabel 442 → 115**. 313 candidate slots were refuted: 13 by the
  consumer document (`\section`/`\subsection`/`\subsubsection`/`\part`'s
  optional argument, `\title`, `\author`, `\date`, `\thanks`, `\markboth`,
  `\markright`, `\sectionmark`, `\addtocontents`'s text), 87 as stored or
  discarded (definer bodies, hook code, a branch not taken), 213 beside two
  or more other text-like slots. 9 former TyLabel slots are now TyMath
  (`\pmod`, `\matrix`, `\pmatrix`, `\cases`, `\bordermatrix`,
  `\displaylines`, `\lefteqn`, `\mathhexbox`×2). TyText 93, TyInherit 80,
  TyMath 29, untyped 368 (was 66).
- Environments 30 of 41 attested, as before; body mode `math` for `math`,
  `displaymath`, `equation`, `eqnarray(*)` (version 1: `either` for `math`),
  none for the list environments and `verbatim`.
- 57,027 solo probes (22 calibration, 56,881 name/environment, 124 definer),
  151,233 engine runs. Batch triage: 41,711 agree / 1,162 disagree / 7,394
  inconclusive / 6,614 skipped (follow and consumer probes). The sidecar is
  6.3 MB; the pure gate replays its 55,670 name probes in about a second.
- **The reviewer's own scripts, re-run against this sidecar** (w1-w8): the
  r = 0 look-ahead census (w6) finds **0 of 890** r = 0 variants not followed
  by the undefined-cs error (version 1: 12 of 918); the 205-probe re-check of
  a random sample (w2) finds 0 mismatches; the 35-name regeneration (w5)
  reproduces 35 of 35; every name of w1/w8 (`\string`, `\noexpand`,
  `\meaning`, `\do`, `\partokenname`, `\aftergroup`, `\obeylines`,
  `\obeyspaces`, `\index`) is now unresolved, so neither the false READY
  nor the false NOT-READY can be derived from the sidecar (the documents
  are outside the tier); w3's `\section[..]` and `\title` slots are untyped
  (`\caption` was and is unresolved); w7's `\pmod` argument is TyMath and
  `math`'s body is math.

- **Reproducibility.** The committed sidecar is the byte output of that
  full regeneration (not assembled incrementally). A second, independent
  run of `check_contracts_reproducible.py --signatures --signatures-sample 60
  --signatures-seed review-2026-09-28` regenerated 85 names (60 drawn, plus
  the 27 adversarial ones, two overlapping), 7 environments, all 124 definer
  rows and the calibration: every record identical. The same run
  reproduced the `article` contract and the kernel file byte for byte and
  passed every TeX kill-test, including the eight new ones (a macro that
  stores its argument, one typeset only by `\tableofcontents`, one that
  expands to `\string`, a message-only slot; and on the committed contract,
  the reviewer's `\string`/`\noexpand`/`\index`/`\obeylines`/`\aftergroup`/
  `\ifdefined` unresolved, `\pmod`/`\matrix` TyMath, `\section[..]` and
  `\title` untyped, `\label` TyLabel, `\addtocontents`'s text untyped).
  `newtheorem.json` regenerated twice, byte-identical.

**Known limits (recorded, not fixed).**

- The consumer suite is the configuration's own, at its default counters: a
  document that raises `tocdepth` makes `\paragraph[..]`'s optional argument
  a table-of-contents entry, and `\paragraph#0` is still TyLabel.
- Joint dependence is attested only for one other text-like slot at a time
  (over `toc`/`lof`/`lot`); lattice-typed slots are held at their payloads.
- `\setlength`'s slots are now TyInherit (`\setlength{a}{a}` typesets, and
  both witnesses behave as in the text they typeset); this is the §G.1
  parametricity risk, which only M2's differential tests.
- `\dospecials` stays attested: at body start in `article` `\do` is
  `\noexpand`, so it changes no catcode.

#### Round 2: signature version 3 (review of 2026-09-28, C-90)

A second adversarial review of version 2 found that every version-2 fix held,
and that five families of new holes had the same root cause: **a use attested
in isolation was taken to compose.** Composition needs what a use *leaves
behind*, and version 2 attested only that the next token runs next with the
catcodes and group level unchanged. Version 3 attests what a use leaves, or
puts the use outside the tier. The method changes are general. None of them
lists a name.

**HIGH-1: the mode after a use.** `\section`, `\par`, `\newpage`, `\item` and
every `\endX` list-ender leave the mode they found. So `x \section{a}\\ y` is
fatal although `\section` and `\\` were each attested in `text`.

The follow probe now compares, besides the catcodes and group level:

- the group type;
- the conditional level;
- the kernel's allocation registers;
- the mode (`v`/`h`/`m`, plus `\ifinner`), separately.

A change of the mode alone is `! LPMODE <mode>.`, recorded as the cell's
`mode_after`.

A new cell, `listv`, puts the use between paragraphs inside a list item.
There `\item` keeps the mode it found; in `list` it ends a paragraph.

A mode change composes only through a **transition**, (cell, mode after) →
follower cell: `text`+`v` → `vertical`, `vertical`+`h` → `text`, `list`+`v` →
`listv`, `listv`+`h` → `list`. A transition is attested only when two
conditions hold:

- the follower cell accepts the use with its own mode unchanged;
- a *transition probe* compiles: the use followed by the follower cell's own
  material, in the source cell.

Only then is the cell `shape_checked`, with `follower_cell` recorded. M2 must
read the next token in the follower cell. A mode change with no transition
(into or out of math, typesetting in the preamble) leaves the cell
unchecked. A name that has no checked cell at all is unresolved
(`no cell lets the use compose`).

**HIGH-2: TyLabel admitted fatal or deferred payloads.** TyLabel is now a
**key**: a run of catcode-11/12 characters. It admits no control sequence,
group, space or special character. The sidecar records this under
`argty_payloads`.

It is confirmed with two new sets of payloads in the consumer document:

- a punctuated key, `a:1-b.c`;
- keys that name something the configuration has: the lattice's counter and
  environment payloads.

`\value{enumi}` is `Missing number`, so `\value`'s slot is no longer TyLabel.
`\DeclareEmphSequence{a^b}` and `{a&b}` do not lex as keys, so the reviewer's
repros are outside the tier. The 75 slots whose log shows `\"a` as fatal
now have one payload set: `\"a` is not a key.

**HIGH-3: fragile commands in moving arguments.** Every typeset type
(TyText, TyMath, TyInherit) must also take a moving witness in the consumer
document. The witness is the payload `\lpfragile\lpfragilex`:

- `\lpfragile` defines `\lpfragilet`;
- `\lpfragilex` is `\ifx\lpfragilet\lpfragileo\else\number\lpfragileu\fi`.

Executed in order, the two are harmless. Expanded without being executed,
they are fatal:

- `\protected@edef`, `\write` and `\mark` expand the still-undefined
  `\lpfragilet`;
- a case change (l3text, `\MakeUppercase`) leaves an undefined token
  alone, but it expands `\lpfragilex` before the `\def` has run, and meets
  `\number` of an undefined name.

A slot written to the `.toc` or a running head, or case-changed, is
therefore not TyText.

The first witness, `\futurelet` alone, passed through `\MakeUppercase`.
The re-run's moving census found this: `\MakeTitlecase{a
\expandableinput{..} b}` and `\MakeTitlecase{a \refstepcounter{enumi} b}`
are fatal. The witness was replaced before the final regeneration.

A mandatory slot is also confirmed with every optional argument omitted.
`\section[a]{..}` only typesets its mandatory argument. `\section{..}` also
moves it. So `\section`'s mandatory slot is now untyped, and the reviewer's
`\section{a \footnote{a} b}` is outside the tier.

**HIGH-4: state carried from one use to the next.** Four general facts cover
it.

1. *Allocation* is in the follow probe's state. The registers are
   `\count10`–`\count20`, `\float@count` and `\count256`: every register that
   `\e@alloc` and `\extrafloats` advance at the pin (latex.ltx lines 331–450).
   `\tableofcontents`, `\listoffigures`, `\newwrite`, `\newlength` and
   `\newsavebox` therefore fail the follow probe.
2. *Redefinition.* `\lpfsave` switches `\tracingassigns` and
   `\tracingrestores` on for the use. The generator reads the NET change of
   every name a body can type between two markers, after the use's own
   groups are restored. Internal quantities (primitives and registers of the
   closed world) do not count. A new or changed name is a closed-world change
   the contract does not model, so the outcome is `! LPREDEFINES <names>.`
   and the use is unresolved. Examples: `\newlength{\x}`,
   `\DeclareRobustCommand`, `\appendix` (`\thesection`), `\centering` (`\\`),
   bare `\quote` (`\par`, `\makelabel`).

   A trace line of exactly 79 characters is ambiguous, because TeX wraps at
   79. The text is therefore split again at every record start. The markers
   are found in the raw log, and a trace without them fails closed.
3. *Repetition.* The canonical use is repeated 300 times in its base cell,
   and that must compile. This catches:
   - a definer outside the NDef set failing its second use (`\NewHook`,
     `\NewSocket`, `\NewTemplateType`, `\newcounteralias`);
   - `\over` twice in one formula;
   - a nesting (bare `\quote` ×7);
   - dead cycles (`\clearpage` ×100);
   - float exhaustion (`\marginpar`).
4. *Counter witness.* The canonical use must also compile with every counter
   of the configuration (`counters_set`) set to 27, and again to −1, before
   it. This catches `\fnsymbol`, `\Alph` and `\alph` on a large or negative
   value, and `\fnsymbol{page}`.

**HIGH-5: the vertical cell tested only the top of page 1.** The vertical
outcome is now also probed after a paragraph (`vmid:vertical`,
`x\par <use>\par x`). If the two differ, the cell records
`position_dependent` and decides nothing. `\vss` is the case: glue at the
top of a page is discarded. `\hss` in `vertical` starts a paragraph (a mode
change), and its transition probe `\hss z\par x` is fatal, so `\hss`
composes nowhere.

**MEDIUM.**

- *Space before an optional argument.* Each consumed optional position
  records `after_space`: whether ` [..]` (a space or newline first) is still
  taken. `\\`'s is (`\@ifnextchar` skips spaces), so M2 must parse
  `\\ [a]` as the optional argument. `a` is not a TyDimen, so that document is
  outside the tier. `None` means unknown, and a spaced `[` is then outside
  the tier.
- *Parametricity.* TyNumber must also take `0`, `-1` and `300`, and TyDimen
  must take `0pt`, `-1pt` and `1000pt`. Otherwise the slot is untyped:
  `\symbol{300}` is `Bad character code`.

**LOW.**

- The gate now binds these fields to the contract and its kernel file:
  - `config_key`, `configuration` and the whole `pin`;
  - the signature set, which must equal the scope of the recorded `letters`
    over the closed world, so adding `@` is seen;
  - the environments, `counters_set`, the lattice and the definer targets.
- It also requires every probe-design constant to equal this version's
  (`design_header()`): `cells`, `transitions`, `follow_probe`, `witnesses`,
  `consumers`, `sentinel`, `protocol`, `repeat`, `argty_payloads`.
- `\footnote`'s position-0 optional argument stays `count 0, further None`:
  M2 must treat a following `[` as outside the tier.

**Measured.** (2026-09-28/29, under the image, arm64, the `article` contract.
The figures come from a full regeneration: 7.2 h on 8 workers, in a
container shared with another track, at load 30–350.)

- **2,148 names: 1,197 attested, 951 unresolved.** 115 names moved from
  attested to unresolved, and none moved the other way:
  - 53 by redefinition. Examples: `\DeclareRobustCommand`, `\NewCommandCopy`,
    `\appendix`, `\centering`, `\raggedright`, `\counterwithin`,
    `\linespread`, the bare list starters `\quote`/`\center`/`\abstract`,
    and `\newcommand`/`\newenvironment` used as ordinary names (as NDef
    they go through `definer_rules`).
  - 26 by allocation. Examples: `\tableofcontents`, `\listoffigures`,
    `\listoftables`, every `\new<register>`, `\newlength`, `\newsavebox`,
    `\newcounter`, `\newtheorem` as a name, `\extrafloats`, `\addlanguage`.
  - 5 by the conditional level: `\iftrue` and the `\if?mode`/`\ifinner`
    tests.
  - 23 by repetition: the `\NewHook`/`\NewSocket` families, `\over` and
    `\atop`/`\choose`/`\brace`/`\brack`, `\clearpage`,
    `\cleardoublepage`, `\onecolumn`, `\twocolumn`, `\hss`, `\marginpar`,
    `\IncludeInRelease`.
  - 8 by the counter witness: `\Alph`, `\alph`, `\fnsymbol`,
    `\theenumii`, `\theenumiv`, `\labelenumii`, `\labelenumiv`,
    `\thempfootnote`.
- **Transitions.** 47 `text`→`vertical` and 48 `list`→`listv` transitions
  are attested (`\section` and its family, `\par`, `\newpage`, `\vfill`,
  the list-enders, `\item`). So are 501 `vertical`→`text` and 501
  `listv`→`list` transitions: every character-producing use starts a
  paragraph. There is 1 position-dependent vertical cell (`\vss`). 9
  accepting cells are unchecked.
- **Types.** 270 slots are refuted as TyLabel:
  - 189 sit beside two or more other text slots;
  - 65 store their payload;
  - 15 are refuted by the consumer document;
  - 1 is refuted by a key naming the configuration's counter (`\value`).

  9 typeset slots are refuted by the moving witness: 6 TyText (`\section`,
  `\subsection`, `\subsubsection`, `\paragraph`, `\subparagraph`,
  `\part`) and 3 TyInherit (`\MakeUppercase`, `\MakeLowercase`,
  `\MakeTitlecase`). 13 TyNumber slots are refuted by value (`\symbol`,
  `\mathhexbox`, `\sbox`, `\savebox`, `\usebox`, `\magstep`, …), and 1
  TyDimen slot (`\tmspace`).

  Totals: TyLabel 88, TyText 84, TyInherit 77, TyMath 29, TyNumber 26, TyDimen
  24, TyCounter 8, TyFile 5, TyCsName 1, untyped 326. Every one of the 58
  consumed optional positions is `after_space: true`.
- **Environments: 30 → 10 attested.** Still attested: `math`, `displaymath`,
  `equation`, `eqnarray(*)`, `minipage`, `lrbox`, `sloppypar`, `titlepage`,
  `theindex`. They left for two reasons:
  - Every list-based environment (`itemize`, `enumerate`, `description`,
    `center`, `flushleft`/`flushright`, `quote`, `quotation`, `verse`,
    `abstract`, `verbatim(*)`, `thebibliography`, `trivlist`, `list`,
    `tabbing`) ends with `\par` redefined. `\@doendpe` suppresses the next
    paragraph's indentation that way, and the redefinition fact sees it.
  - `figure`, `table` and their starred forms exhaust the float list under
    repetition.
- 73,630 solo probes (the 42-row calibration included) and 192,580 engine
  runs. Batch triage: 49,554 agree, 1,396 disagree, 9,917 inconclusive,
  12,597 skipped. The sidecar is 14.4 MB (the 300-fold repetitions are in
  its log). The pure gate replays it in about 9 s.
- **The reviewers' scripts, re-run against this sidecar (all under the
  image).**
  - Every repro of the review is now decided correctly or is outside the
    tier (24 documents). `x \section{a}\\ y`, `x \par\\ y` and
    `x \newpage\\ y` now compose through their transition to `vertical`,
    where `\\` is fatal. `\begin{itemize}\item\\ x\end{itemize}` is
    `\item` in `listv`, then `\\` is fatal there. All the other repros are
    outside the tier (an untyped or non-key slot, an unresolved name, a
    position-dependent cell).
  - Mode census: 4,632 checked cells, 0 whose mode after the use differs
    from the recorded one (version 2: 71 of 993 text uses left horizontal
    mode unrecorded).
  - Fresh-position test with the transition model (the follower judged in
    the follower cell): 1,167 and 1,120 pairs over two seeds, 0 mismatches
    (version 2: 15 of 917).
  - Vertical-checked uses followed by material, at the top and after a
    paragraph: 1,774 probes, 0 fatal (version 2: 2 of 988).
  - Moving census: typed slots × checked same-mode uses in the consumer
    document, 1,200 + 1,198 + 1,197 documents over three seeds, 0 fatal.
    The first version-3 run had 5. Three were the case-changers, which led
    to the new witness. Two were `\item[a \providecommand{a}[1][a]{a} b]`
    and `\item[a \nolinebreak[1] b]`: an unbraced `]` ends an optional
    argument, a grammar rule for M2 and not a type.
  - 300-fold repetition in the base cells: 1,215 variants, 0 errors. 2
    timed out at 15 s under load (`\IfFileExists`, `\include` in the
    preamble); re-run with a longer timeout, both compile (9.1 s and
    16.3 s).
  - Look-ahead census (w6): 0 of 847. Spot re-check (w2): 256 probes, 0
    mismatches. Regeneration (w5): 35 of 35.
- **Reproducibility.** The committed sidecar is the byte output of that
  full regeneration. An independent `check_contracts_reproducible.py
  --signatures --signatures-sample 60 --signatures-seed
  review-round2-final-2026-09-29` regenerated, record for record:
  - 110 names: 60 drawn plus the 52 adversarial ones, which now include the
    25 of this review, with two overlapping;
  - 7 environments;
  - all 124 definer rows;
  - the calibration.

  The same run reproduced the contract and the kernel file byte for byte.
  It passed all 56 TeX kill-tests (33 of them signature kill-tests), 16 of
  them new:
  - ten on synthetic macros, one per fix: a paragraph-ender, a definer, an
    allocator, a toc-moved slot, a case-changed slot, a counter-dependent
    use, vertical glue, a counter-named key, a value-dependent number, a
    spaced optional argument;
  - six on the review's own names on the committed contract.

  `newtheorem.json` was regenerated twice under version 3, and the two runs are byte-identical. Only `signature_version` changed from version 2.

**Known limits (recorded, not fixed).**

- Repetition attests one name repeated. It does not attest two names that
  share a resource. Examples: `\clearpage` and `\cleardoublepage` sharing
  dead cycles, or `\marginpar` and a float sharing the float list. Floats are
  the §A.1.5 `k_float` side condition, which M2 must count.
- The redefinition fact reads only names a body can type. A use that changes
  an internal macro another name later reads is caught only if the change
  shows in that other name's own probes or in repetition. `\appendix` is
  excluded because it changes `\thesection`, which is typeable. The generic
  case is §G.1's parametricity risk, which only M2's differential tests.
- A transition assumes that the state a mode-changing use leaves is the
  follower cell's state. Examples: after `\section`, `\@nobreak` and
  `\everypar` are pending; after `\item`, the label. The transition probe
  and the fresh-position re-run above test this, and do not prove it.
- Declarations that redefine a typeable name (`\centering`, `\raggedright`:
  `\\`) are now unresolved. An alias model (`\\` := `\@centercr`, whose
  own signature would then be needed) could readmit them.
- **Coverage cost, the largest single item.** The list environments are
  unresolved only because `\@doendpe` redefines `\par` until the next
  paragraph starts. The first readmission target is a transient-state model:
  attest that the redefinition is undone at the next paragraph boundary, and
  that the follower cell's probes run under it.
- `figure`/`table` wait on the §A.1.5 float count: repetition exhausts the
  float list.
- **Timeouts make three records load-dependent** (MEASURED: the two full
  regenerations differed on `\include`, `\pdfmapfile` and `\pdfmapline`
  only through 15 s timeouts). A timeout is never an attestation, so both
  outcomes are sound. But a record holding one may not reproduce byte for
  byte under another load, and the sampled check can then report it.
- **Rules M2 must apply**, recorded here because no signature field can
  carry them:
  - Inside an argument, a use whose cell record has `mode_after` is outside
    the tier: transitions are attested at top level only.
  - A typeset slot's payload runs in the slot's mode. This may be the inner
    one (`\mbox`). The moving census found no same-mode use that fails there
    (MEASURED), but no inner cell is attested.
  - An optional argument runs to the first unbraced `]`.
  - An untyped slot admits only its canonical payload.
  - A position-dependent cell decides nothing.
