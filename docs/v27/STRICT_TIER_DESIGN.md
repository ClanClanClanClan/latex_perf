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

**Which pdflatex is the oracle (owner decision of 2026-09-26, ADR-012 decision 7).** The oracle is frozen as CI's digest-pinned TeX Live image, the `TEX_IMAGE` digest in `.github/workflows/tex-oracle.yml`, run locally through a container. The laptop TeX Live is not the oracle, so the earlier plan to repair its pdfmanagement orphan files is superseded. Every graded artefact is re-graded once under the image and the diffs are published as an oracle-baseline change; sample 3 is drawn and graded only after that. The [M] figures in this document were taken under the laptop pin and are pre-baseline.

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
- `defined_names`: two passes.
  - Pass 1 traces every assignment from the first line to after the
    begin-document hooks, with a marker before every load.
  - Pass 2 dumps the body-start `\meaning` of every name of the UNIVERSE: the
    kernel's candidates, every traced name, every name token of the files read
    and of the definers, and every one-character name and the null name. Each
    is inside an `\ifcsname` guard, in a catcode regime where any byte string
    can be written inside `\csname`; names holding the regime's reserved bytes
    or line feeds go through `\lowercase` with placeholder bytes.
  - The same hash-count check runs at body start against the universe: a name
    the universe misses would be called undefined without having been asked.
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
    a group end undid.
  - Traced names whose meaning at body start is back to the kernel's are
    listed in `reverted_names`. Primitive parameters the configuration
    assigned (`\baselineskip`, ...) are listed separately in
    `parameters_assigned`: the contract compares meanings, not values, so
    their values are not recorded.
  - The dump is repeated on the later passes (in one directory) and under the
    grading environment. A name-set difference makes the contract incomplete;
    a meaning that differs between passes while the name stays defined is
    recorded in `pass_dependent_meanings` and flagged on the name.
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
- TeX's hash count at body start finds no name outside the universe.
- The body-start name set is the same on every pass and under the real clock.
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
- **Three contracts, all complete.**

  | configuration | defined names | reverted | parameters assigned | universe | hash entries at body start (all covered) | self-check (sampled from the universe, of which members; + referenced) | size |
  |---|---|---|---|---|---|---|---|
  | `article` | 762 | 118 | 19 | 34,573 | 29,846 | 346 (239) + 10,736 | 167 KB |
  | article + amsmath, amssymb, amsthm, graphicx, hyperref | 9,215 | 733 | 26 | 57,444 | 38,909 | 575 (299) + 14,992 | 1.9 MB |
  | `amsart` | 1,979 | 248 | 25 | 38,321 | 30,931 | 384 (252) + 11,377 | 398 KB |

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
- **Kill-tests and review repros** (`check_contracts_reproducible.py`, every
  invocation): the hidden-`\def` definer trips both the tracing-toggle check
  and the self-check; the hash count sees one name dropped from the kernel
  candidates, the reviewers' 24 dropped, and one name dropped from a
  contract's universe; the null control sequence is defined as the empty name;
  `\lpa=b` is defined and `\lpa` is not reported; a group-local `\def` undone
  at the group end does not move `set_in`; the `.aux`-writing definer is a
  fatal load on the confirming pass; the `\year` definer is a fatal load
  under the real clock and flagged `date_dependent_load`; the reviewers' 24
  names as use-names on plain `article` give 0 mismatches.
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
