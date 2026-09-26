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
| `defined_names` (closed world) | every name whose final meaning at body start differs from the kernel | pass 1: `\tracingassigns=1` over `\documentclass…\begin{document}`, with `\typeout` load boundaries and `max_print_line=1000000`. Pass 2: `\ifcsname`-guarded `\meaning` dump **after `AtBeginDocument`** (65 names assigned during load revert by body start [M]) | **closure self-check**: `\ifdefined` on a random 1% of the kernel∪contract universe plus every name the document uses must agree with membership. Any mismatch blocks the contract |
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
| `provenance` | generator sha, per-entry probe `.tex`/`.log` hashes, file sha256 list | written by the generator | a byte-identical regeneration gate |

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

## I. M0 as built (2026-09-26)

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
