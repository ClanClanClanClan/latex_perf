> **Repository note (2026-09-30).** Historical design draft, committed verbatim below this note as the owner
> read it when deciding ADR-015. It was written in a session scratchpad (design-adr013/ADR-013-draft.md, written by the ADR-013 design agent on 2026-09-29 (00:19 UTC)) and never
> committed there; the scratchpad was wiped, and this copy was rebuilt from the session transcripts: the
> agent's `Write` of the file plus its later in-place edits, replayed exactly (sha256 of the text below this note:
> `4b71385a9e5c675c53e54271c7b625a9afb120810c34869f86f0359d1f79fe3e`). Scratch paths it cites (`design-*/`, `m/`, `src/`, probe scripts) were not kept.
> **Status: superseded by [ADR-015](../ADR-015-static-proven-tier-on-translated-engine.md)**, which records what was
> decided; where a measurement below was later corrected, ADR-015 and `docs/v27/spike/H1-report.md` say so.

# ADR-013 (DRAFT) — Admission by attested effect, a multi-pass semantics, and per-document configuration attestation

**Status:** DRAFT design for owner review, 2026-09-29. Nothing here is implemented or committed.
**Extends:** ADR-012 and `docs/v27/STRICT_TIER_DESIGN.md` (§A.1, §B.2, §C, §I.4–§I.6).
**Related:** OPEN-116, OPEN-120, OPEN-121, OPEN-122; C-81 to C-92.
**Read from:** `origin/main` = `7bf85335`, and branch `feat/v27165-strict-args` = `266fa6db` (local worktree, read-only).

**Evidence tags.**
- **[M]** means measured for this draft on 2026-09-29. Each measurement went through `scripts/tools/_oracle.py` (`run_once` and `run_to_fixpoint`) on the pinned image, in a private container (`LP_ORACLE_WORKROOT=~/.cache/lp-oracle/adr013-work`), because the shared container fails `check_state` on stray `/tmp/gs_*` files. The scripts and results are scratch-only, next to this file: `probe.py`, `docs{1..4}.json`, `res{1..4}.json`, `census.py`, `analyze.py`, `census3.json`.
- **[I]** means inferred.
- **[R]** means read from the kernel source in the pinned image, `texmf-dist/tex/latex/base/latex.ltx` (LaTeX2e <2026-06-01>), or from the repository.

---

## 0. The proposal in eight sentences

1. **Replace R-INERT as the admission rule with R-EFFECT.** R-INERT is a static yes/no screen on what a name's definition *could* reach. R-EFFECT asks what the name *does*. A name is admitted when every effect it can have is one the Coq semantics models, and every input its control flow depends on is part of the modelled state.
2. **"Coverage of the probed paths" is not enough, and this design does not rely on it.** Section 1 shows seven measured documents that separate a probed path from an unprobed one on the same name: a counter value, a nesting depth, list state, the mode, a stored argument, a name's meaning changed by another name, and look-ahead across a line end. Sufficiency comes from two finite, static censuses over the name's exact code:
   - a **read/write footprint** (which state variables the control flow reads, and which ones it writes);
   - an **error-site census** (every place the code or the engine can stop).

   Traced probes then attest the behaviour at every cell of the partition that those censuses induce.
3. **Behaviour is data. Coq gains a generic machine for it, and no rule is written per name.** Each admitted name's behaviour is a small guarded-effect program, kept in the contract (§2.5). Coq gets:
   - one generic interpreter for that effect language;
   - an explicit abstract state `Σ#`: TeX mode, group and frame stack, list depth, counters with exact values, switches, the `\everypar` kind, stored argument slots, the meaning version of self-mutating names, the label, citation and toc tables, and a count of the resources used.

   A reachable cell that has no attested program puts the document **outside the tier**. It is never guessed.
4. **Passes are modelled exactly, by replaying `_oracle.run_to_fixpoint` in Coq.** The model runs up to three passes until one succeeds, then one confirming pass, and threads an explicit `aux` state (labels, citations, bibcites, toc entries) through them. This replaces the unproved `fatal_aux_independent` claim of §C.2. For the fragment, the independence lemma is then *proved* about the model, not assumed.
5. **Front matter is attested per document, on demand.** The key is the hash of the exact preamble. The attestation produces three things for the body:
   - the configuration contract;
   - the footprint censuses and `Σ#` schema of this configuration;
   - use-based behaviour programs, for only the names the body uses and only in the contexts it uses them.

   A cache keyed by each name's **footprint hash** (token-exact code closure plus every parameter it reads) lets behaviour transfer between configurations soundly (§4.3).
6. **The candidate universe is the whole closed world** of the configuration, ranked by frequency on the unsealed frame. Math symbols (`\alpha`, `\in`, `\leq`, …; 196 names of kind MathChar or Char in `article`) come first, because they are the cheapest.
7. **The payoff is honest and small until per-document configuration attestation exists.** The census estimates below are upper bounds on bodies only [I]:
   - 1,117 of 1,119 unsealed roots stop at the front matter;
   - even with everything this ADR proposes, *except* per-document configurations, other packages' names, UTF-8 and alignment, at most **4** bodies are covered;
   - a real first number needs configuration attestation, user `\newcommand`, UTF-8 and alignment together.
8. **Three defects were found while drafting and must be fixed first** (§1.1):
   - **the oracle's PDF check is stale across passes** [M];
   - **R-INERT's meaning closure silently stops at every expl3 name** [M+R];
   - **the closure reads `\meaning`, which cannot say which characters belong to a control-sequence name** [R].

---

## 1. What the measurements say (read this before the rule)

### 1.1 Three defects in the current instruments

**D-1. The oracle can report READY for a document whose confirming pass produced no pages.** [M]

`_oracle.run_to_fixpoint` never deletes `main.pdf` between passes. It then reports `pdf = pdf_path.is_file()` after the last pass. pdfTeX opens its output file only when it ships the first page, so a pass that prints "No pages of output." leaves the previous pass's PDF on disk.

- **Document Q1** (body `\expandafter\ifx\csname r@a\endcsname\relax x\fi\label{a}`):
  - per pass, `(rc, pdf on disk, "No pages")` reads `(0,T,F) (0,T,T) (0,T,F) (0,T,T)`: the document **oscillates**;
  - the protocol returns `rc 0, pdf true, passes 2`, which is READY;
  - yet its last log says "No pages of output.".
- **Current fragment: no wrong verdict follows.** Nothing in the fragment reads the aux file, so every pass behaves the same.
- **After any aux-reading construct is admitted:** this becomes a false-READY channel in the oracle itself (T3). It is outside the kernel's grammar today, but the semantics must speak about the corrected predicate.
- **Fix, before any `\ref` or toc work:** delete the PDF (through `oracle.remove`) before every pass, or require `Output written` in the *last* log. Then re-grade every artefact whose rows can have more than one pass. Expected diff: 0 cells on the current corpora [I].
- Ledger candidate: the next free C-id. A parallel branch appears to be using C-93 (its scratch trees are `~/.cache/lp-c93`), so check `grep "^| C-"` on every open branch first.

**D-2. R-INERT's closure never enters expl3 code.** [M+R]

- `body_tokens` splits meanings with `\\([A-Za-z@]+)`, so `\hook_use:nnw` is read as `\hook`. The recorded meaning of `\hook` is `undefined` (`article-s0-signatures.json` → `meanings["hook"] = "undefined"`), and `closure` stops there without raising `KeyError`.
- Six of the 121 admitted phase-1 names reach `\par` or `\endgraf`, whose meaning is expl3 code (`\scan_stop: \mode_if_horizontal:TF {… \hook_use:n {para/end} …`) [M: `closure()` re-run over the committed meanings]. The closure never saw that code, which contains a conditional (`\mode_if_horizontal:TF`) and the paragraph hooks.
  - `article` puts nothing in those hooks, so the rule's *outcome* is unchanged here [I].
  - Any package that uses `para/begin` or `para/end` (tagging, `lineno`, ...) would change it unseen.
- **The same shape as C-92:** the published rule said "the expansion closure", and the code computed a smaller set.

**D-3. `\meaning` output is ambiguous about names.** [R]

`\meaning` prints `\foo_bar` both for the control sequence named `foo_bar` and for `\foo` followed by the character tokens `_bar`. It also does not show catcodes. Any static analysis over printed meanings is therefore unsound as a matter of principle, not only in practice.

- The analyser of §2 must read a **token-exact dump**: one record `(kind, catcode, charcode or csname)` per token. This is produced inside TeX by an expl3 walk over each macro's replacement text (`\tl_analysis_map_inline:Nn`) or an equivalent `\futurelet`/`\string` loop.
- It must be calibrated on hand-built ambiguous cases.

### 1.2 Which inputs a name's behaviour depends on [M]

Each row is a pair of documents that differ in one variable. The name looks the same in both; the outcome differs. All were run under the oracle protocol, with every pass recorded.

| # | variable | compiles | fails (first error, pdfTeX `l.N`) | kernel mechanism [R] |
|---|---|---|---|---|
| P2 / P2b | **counter value** | 26 `\item` in the inner `enumerate` | 27 items: `Counter too large.` | `\theenumii` = `\@alph`, an `\ifcase` over 1..26, else `\@ctrerr` |
| Q5 / Q4 | counter value, other context | 26 `\footnote` in a `minipage` | 27: `Counter too large.` | `\thempfootnote` = `\alph` |
| Q9 / Q8 | counter value | 9 `\thanks` | 10: `Counter too large.` | `\@fnsymbol`: `\ifcase` 1..9 |
| P5b / P5, P6 | **nesting depth** | 4 nested `itemize` | 7 `itemize`, or 5 `enumerate`: `Too deeply nested.` | `\@listdepth`, `\@enumdepth` compared with constants |
| P10, P11 | **list state** | — | text before the first `\item`, or an empty list: `Something's wrong--perhaps a missing \item.` | switch `\if@newlist` |
| P3 / Q6, P4, P14, R12 | **mode / context** | `\section` inside `center`, after `\item`, in `\footnote`, in `\parbox` | inside `\mbox`: `Not allowed in LR mode.` | mode tests in `\@startsection` |
| Q10 | **stored argument** | — | `\maketitle` without `\title`: `No \title given.` | `\@title` holds an error sentinel until `\title` stores into it |
| R4 / R3 | **a name's meaning, mutated by another name** | `\title{a^b}` with no `\maketitle`: stored, never typeset | the same after `\maketitle`: `Missing $ inserted.` | `\maketitle` does `\global\let\title\relax` |
| R1 / R2 | the same | `\and` after `\maketitle` | `\and` before it: `Misplaced \crcr.` | `\and` becomes `\relax` |
| R6b / R6 | **look-ahead across a line end** | `\item`, blank line, `[$] x $`: text | `\item`, newline, `[$] x $`: `Extra }, or forgotten $.` (taken as the optional label) | `\@ifnextchar` skips spaces, and a single line end is a space |
| R7 / R7b | the same, for `\\` | `x\\ [2pt] y` | `x\\ [$] y $`: `Missing number, treated as zero.` | `\\` looks past the space for `[` |
| Q3 / Q2 | **argument content interacting with the name's own code** | `$\frac{a}{b}$` | `$\frac{a\over b}{c}$`: `Ambiguous; you need another { and }.` | `\frac`'s first argument runs in `\begingroup … \endgroup` on the **same** math list as `\over` |
| S1c / S1 | **the configuration** | kernel: two `\label`s in one `equation` | with `amsmath`: `Multiple \label's: label 'a' will be lost.` | `\label@in@display` tests `\df@label` |
| S6, S4 | **moving argument (write-time expansion)** | — | `\section{A\footnote{b}}` fails with or without `hyperref`: `Use of \@xfootnote doesn't match its definition.` | `\protected@write` `\edef`s the title, and the `\footnote` path is fragile there |
| R11 | **a global resource** | — | 16 × `\tableofcontents`: `No room for a new \write.` | `\newwrite` per call (C-85's 20 reproduced at 16) |

Documents that compile, as a baseline for §3: P1 (`\label{a}\ref{a}`), P1b, P1c (`\pageref`), P7/P8 (`\tableofcontents` with a `\ref` in a title), P12 (`\section *{A}`), P13 (`\cite` with no `.bbl`), P15 (`\label` inside `\mbox`), Q7 (`\label{a~b}\ref{a~b}`: I predicted a failure and was wrong), R5 (`\maketitle` twice), R8 (`\cite{a,,b}`, `\cite{}`), S2 (`\footnote` inside amsmath `\text`), S3 (hyperref, `$x^2$` in a title).

Not READY with rc 0, because the log says "No pages of output.": P9 (`\label` alone) and R9 (`\bibliography{zz}` alone).

**What this table rules out.** A rule of the form "probe the name in a few contexts with a few payloads, admit it if every probe agrees" is unsound for **every** structural name the task lists:
- `\item` depends on counters, depth and switches;
- `\section` depends on the mode and on its write-time expansion;
- `\label` depends on the configuration;
- `\title` depends on a meaning that another name mutates;
- `\frac` depends on list-sharing.

Probing only the success paths is unsound; probing every path that a traced probe happens to exercise is too. Something must also establish **which inputs exist**. That is the job of the static censuses in §2.

---

## 2. The admission rule R-EFFECT

### 2.1 The obligation to be discharged

For each name `N` and configuration `C`, `Faithful` needs, in effect:

> For every concrete TeX state `σ` reachable in the fragment and every argument list `a` in the grammar, pdfTeX's execution of `N a` from `σ` has the outcome, the typeset-material flag, the location and the abstract post-state that the model's program for `N` gives from `abs(σ)`, `a`.

Probes can only ever check finitely many `(σ, a)`. The design therefore splits the obligation into three parts.

- **(O1) The abstraction is exact.**
  - `N`'s control flow depends on `σ` only through the components `R_N` of `Σ#`, and on `a` only through the argument's lattice type and declared inspections (§2.4).
  - "Depends" includes every branch, every table lookup, every dynamic dispatch and every error site.
  - O1 is established by static census, checked against the traces.
- **(O2) The partition is covered.** For every cell of the finite partition that the guards induce on `R_N` × context × argument class, and that the fragment can reach, a solo probe attests the program's prediction. Guard constants (26, 9, 4, 6) are probed on **both** sides.
- **(O3) Effects are closed.**
  - Every effect `N` has on `σ` beyond its own dynamic extent is a write to a component in `W_N ⊆ Σ#`, with the value the program predicts. This is attested by a post-state dump in every probe.
  - Globally, over the admitted set `A`: every component *read* by some admitted name and *written* by some admitted name, `(⋃R) ∩ (⋃W)`, is in `Σ#` with an exact abstraction.
  - Anything read and written by no admitted name is a constant of the configuration, recorded at body start.

The residual premise (§2.7) is then: the static censuses are complete, TeX is deterministic, and one representative per cell stands for the cell. That last one is **parametricity within a cell**, and O1's argument-flow classification is what makes it true by construction rather than by hope.

### 2.2 The instruments (all generated, none hand-listed)

| id | instrument | output | checks |
|---|---|---|---|
| **I1** | **Token-exact code dump.** Every macro, token register and hook reachable from `N`, at body start, as `(kind, catcode, char/csname)` sequences; expl3 names are followed (fixes D-2, D-3). | the code closure `K_N`, closed under static reachability, including: `\csname` targets that constant propagation resolves; the contents of token lists that `K_N` executes (`\the\everypar`, hook token lists, sockets); the output routine and `\AtBeginDocument` hooks, which run on every page and at `\begin{document}` | calibration: hand-built ambiguous names (`\a_b` vs `\a`·`_b`); the dump's own token count against `\tl_count:N` |
| **I2** | **Static footprint analysis** over `K_N` with constant propagation: every conditional, `\ifcase`, arithmetic (`\advance`, `\multiply`, `\numexpr`, `\dimexpr`), `\csname`, `\string`/`\meaning`/`\detokenize`, `\uppercase`/`\lowercase`, delimited-parameter match, `\futurelet`/`\@ifnextchar` peek, and every assignment | `R_N` (state operands of branches, arithmetic and lookups), `W_N` (assigned components, with locality), the guard constants, the **argument-flow class** of each argument (§2.4), `D_N` (dynamic dispatches whose target is not constant) | **rejects** on anything it cannot classify: a dispatch on non-constant data that is not a declared table lookup, an unbounded loop not driven by the argument's own length, `\scantokens`, `\catcode` or `\endlinechar` changes that escape `N`, `\read`/`\openin` of user files, `\write18` |
| **I3** | **Error-site census**: every `\errmessage`/`\GenericError`/`\@latex@error`/`\PackageError` site in `K_N`, plus every **engine** error site of every primitive in `K_N`. The engine sites come from `print_err` in tex.web and pdftex.web: a finite table, generated once per engine pin. | each site mapped to (a) a model rule with an E-code, (b) an *unreachability reason* stated as an invariant of `Σ#` or of the grammar (for example, "`Arithmetic overflow` unreachable: counters ≤ 20,000 by the token bound"), or (c) **reject** | every E-code rule must have a probe that reaches the site; every unreachability reason must name the Coq invariant that implies it |
| **I4** | **Traced solo probes**: `\tracingcommands=3 \tracingmacros=2 \tracingassigns=1 \tracingrestores=1 \tracingifs=1 \tracinggroups=1 \tracingonline=0`, `\showgroups`/`\showifs` at the name's exit, and a post-state dump of every `Σ#` component (`\message{\the\c@…}`, switch states, `\meaning` of mutable names, `\currentgrouplevel`, `\currentiflevel`, `\lastnodetype`) at a sentinel after the use | the executed-effect log per probe, and the post-state per probe | (i) every executed conditional and error site is in I2/I3's census, else **the analyser is wrong: reject and file a defect**; (ii) every executed assignment is local-and-restored within `N`, or in `W_N`; (iii) no pending `\aftergroup`/`\afterassignment` token or open conditional outlives `N`; (iv) the post-state equals the program's prediction |
| **I5** | **Partition enumeration**: the cells are the product of `R_N`'s guard partitions (from I2's constants), the context abstraction (§3.1), and the argument classes (§2.4). Probes are generated per reachable cell, with both sides of every guard constant | the behaviour program's table (§2.5) | the extracted decider agrees with the oracle on verdict, message class and line on every probe (as in §I.4 stage 3) |
| **I6** | **Global closure over the admitted set**: `(⋃_{N∈A} R_N) ∩ (⋃_{N∈A} W_N) ⊆ Σ#`, recomputed whenever `A` grows; plus the existing interleaving and CONTEXT stages and the generated differential (≥ 10k, with generators for every new shape) | pass/fail | a name whose write enters another admitted name's read set, while the component is not in `Σ#`, blocks both names |

R-INERT is **kept as a triage pre-filter** (its fast answer "reaches nothing" is still correct as a sufficient condition once D-2 is fixed). It is never the reason a name is *rejected* when R-EFFECT can admit it.

### 2.3 Effect classes

| class | example (kernel, [R]) | status |
|---|---|---|
| local assignment inside a group `N` opens and closes | `\begingroup … \endgroup` in `\label`; `\frac`'s `\begingroup#1\endgroup` | admitted, no state |
| local assignment to the *current* group (persists to its end) | `\bfseries` changes the font of the enclosing group | admitted only if the component is read by no admitted name's branch, arithmetic or error site (I6); else it enters `Σ#` (for example `\f@encoding` if an admitted name dispatches on it) |
| `\afterassignment`/`\aftergroup` whose token fires within `N`'s extent | `\@defaultunits` (`\afterassignment\remove@to@nnil`, consumed by the assignment the same macro performs) | admitted; I4(iii) checks it never escapes |
| a deferred token that escapes into later input | `\@doendpe` sets `\everypar` for the next paragraph after a list | admitted only as a `Σ#` component "everypar kind" ∈ a finite set of attested token lists, each of which is itself a behaviour program run at the next paragraph start |
| global counter arithmetic | `\stepcounter`, `\refstepcounter` | `Σ#` counters, exact `nat` values; reset lists (`\cl@X`) from the contract |
| global switch | `\global\@newlistfalse`, `\@nobreaktrue` | `Σ#` booleans |
| global store of argument data | `\gdef\@title{#1}`, `\protected@xdef\@currentlabel{…}` | `Σ#` slots, holding a token list from the grammar (or the sentinel "unset") |
| global meaning change of an admitted name | `\global\let\maketitle\relax` (and `\title`, `\author`, `\and`, `\thanks`) | `Σ#` meaning version per name, each version a separate behaviour program; R1–R4 are exactly this |
| `\write` (non-immediate) or `\immediate\write` to `\@auxout` | `\label` → `\newlabel`; `\addcontentsline` → `\@writefile{toc}`; `\cite` → `\citation` | modelled aux entry of a fixed schema (§3.2), whose payload is the argument's **write image** (§2.4) |
| terminal/log messages | `\@latex@warning`, `\typeout` | ignored, **provided** their expansion cannot fail: every expanded payload has a type whose write image is total (keys of characters only) |
| `\errmessage` through any LaTeX error macro | `\@noitemerr`, `\@ctrerr`, `\@toodeep` | a fatal with an E-code (`-halt-on-error` stops at the first error); location = the file reader's line, by the existing `Stops`/`Scans` machinery |
| allocation of a finite engine resource | `\newwrite` in `\@starttoc` (R11), `\newinsert`, the float list `\@freelist` | `Σ#` resource counters with the engine limit; the probe at limit and limit+1 is part of I5 |
| page-builder interaction | `\insert` (footnotes), `\mark`, floats, penalties | admitted only under the layout side conditions of §A.1.5, with the output routine's code in `K_N` and its error sites in I3 |
| code-table, reading-state, interaction, shell, `\scantokens`, reading user files | `\catcode` that escapes `N`, `\endlinechar`, `\nonstopmode`, `\write18`, `\input{user}` | **rejected** (FOREIGN or heuristic) |

### 2.4 Argument-flow classes (O1 for arguments)

I2 classifies every argument position of `N` by where its tokens go. An argument whose tokens reach two or more classes carries every class's obligations.

| class | meaning | what the grammar and the model do | example |
|---|---|---|---|
| **Exec(f)** | the tokens run once, in a frame of kind `f`, at the use site | the kernel runs the argument recursively; `f` ∈ {simple group, semi-simple group on the *same* list (FSemi, new), math group, hbox group, vbox/parbox, footnote (internal vertical, insert), heading paragraph}. Every admitted token must be attested in every frame kind it can reach (the CONTEXT stage, generalised) | `\mbox`: hbox; `\frac` #1: FSemi (Q2); `\footnote`: insert |
| **Exec^n(f)** | the tokens run *n* times | `n` attested by trace (count of span markers); every effect inside must be idempotent or guarded (amsmath guards `\stepcounter` with `\iffirstchoice@`) | amsmath `\text` (`\mathchoice`, n = 4) |
| **Moving** | the tokens are `\protected@edef`'d into a write or a mark | allowed only if every name inside is **moving-safe**: robust, protected, or an unexpandable primitive/char whose write image is itself. S6 (`\footnote` in `\section`) is the counterexample that makes this necessary. The write image is computed by a Coq function `image : list token -> list byte`, and its **re-read** is a separate lemma (§3.2) | `\section`'s title and optional argument; `\caption` |
| **Stored(s)** | the tokens are stored in slot `s` and replayed later by another name in another context | slot `s` ∈ `Σ#`; the grammar types the payload by the *replay* context(s), not the storing one | `\title` → `\maketitle` (Q10, R3) |
| **Key** | the tokens become part of a control-sequence name or a file name (`\csname r@#1`) | typed `TyLabel`: characters of an attested set only (C-82's lattice); lookups are into a `Σ#` table | `\label`, `\ref`, `\cite` |
| **Inspected(P)** | a conditional or delimited match looks *at* the tokens | admitted only when I2 can state the finite partition `P` (empty vs non-empty; first token is `[`/`*`/other) and I5 probes every block | `\@ifnextchar`, `\@ifstar`, `\@citex@checkblank` |
| **Discarded** | the tokens are dropped | typed "any balanced text in the grammar" | `\label`'s gobbling inside `\addcontentsline` |

**Look-ahead is an inspection of the *following* input.** `\@ifnextchar` skips spaces, and a single line end is a space (R6), so the grammar's shape for `\item` is `\item ␣* [opt]?`. The reader must decide the optional argument across a line end, and not across a blank line. The phase-1 FOLLOWER family gets space-then-`[` and newline-then-`[` members.

### 2.5 The behaviour program: what the contract carries per name (and why Coq stays generic)

Each admitted name gets, in the contract, a **guarded-effect program** in a small language `Eff` that the generator selects the same way stages 3 of §I.4 and §I.6 select a signature: the one hypothesis consistent with every probe.

```
prog  ::= case  guard₁ ⇒ body₁ | … | guardₙ ⇒ bodyₙ     (* guards partition R_N; exhaustive *)
guard ::= mode ∈ M | frame_top ∈ F | switch s = b | counter c ⋈ k | depth d ⋈ k
        | slot s = unset | meaning_ver n = v | resource r ⋈ k | next_token ∈ T
body  ::= [] | eff ; body
eff   ::= fatal E_k                  (* location by Stops/Scans *)
        | material | open f | close f | run_arg i f | run_arg_n i f n
        | step c | reset c | set s b | store slot i | replay slot f
        | set_meaning n v | set_everypar k | alloc r
        | aux_write schema (image arg i | current_label | page)
        | read_label i | read_cite i        (* typeset the aux-table value or ?? *)
        | take_opt | take_star            (* look-ahead consumed *)
```

- **`Contract.v`** gains `c_prog : name -> meaning_version -> option prog`.
- **`Semantics.v`** gains one generic family of constructors that interpret `Eff` over `Σ#`. That is about 25 rules, one per `eff` × failure mode, each probe-tagged `S1/Eff/<eff>`.
- **Not written in Coq:** no name, counter or constant. The guard constants (26 for `\@alph`, 4 for enumerate depth, 16 write streams) are **data**, bound by probes at k and k+1.
- **Counter representations** (`\arabic`, `\alph`, `\Alph`, `\roman`, `\Roman`, `\fnsymbol`) are Coq functions over `nat` with a domain predicate. Their domains (1..26, 1..9, …) are contract data read from I2, and their error sites are I3 rows.
- **The decider stays a fold**, so `decide_incremental` (M5) keeps its shape.

A document that reaches a `(name, meaning version, cell)` with no program, or a guard left undefined, is `NotStrict`. This is the same principle as today: an unattested use leaves the tier; it is never guessed.

### 2.6 Worked admissions (what each listed command needs, [R] + [M])

- **`\alpha`, `\in`, `\leq`, `\cdot`** (kind MathChar/Char, 196 in `article`):
  - the footprint is empty except `\fam`/mathcode (constants);
  - the phase-1 signature class "fatal E3 / noad";
  - no new mechanism. The only reason they are absent is the 400-name sample of §I.4.
- **Text fonts** (`\textbf`, `\emph`, `\bf`):
  - `\afterassignment` is consumed internally (I4(iii));
  - the writes are to the current group's font, which no admitted name branches on (I6), until an encoding-dispatching name is admitted;
  - `\emph`'s `\ifdim\fontdimen\@ne\font>\z@` reads the *font* (a finite set of font states reachable through admitted names), so `Σ#` gains an "emph parity" (upright/italic).
- **`\frac`** (Q2):
  - #1 is Exec(FSemi) and #2 is Exec(the same list after `\over`);
  - the grammar forbids generalised-fraction tokens (`\over`, `\atop`, `\above`, `\choose`) and unbalanced `\left`/`\right` inside either argument;
  - both are already excluded, because none of them is admitted.
- **`\sqrt`, `\hat`, `\bar`, `\vec`, `\overline`:**
  - they read their argument through TeX's math scanner, incrementally, so an error inside is reported at its own line (§I.6); that needs a new argument-reading mode `ScanMath` alongside `Scans`;
  - `\sqrt` inspects the next token for `[` (Inspected);
  - all are inert under R-INERT.
- **`\label`** (Key + aux_write):
  - `R` = {`\@currentlabel` slot, config hooks}, `W` = {aux};
  - with amsmath, `\df@label` is in `R ∩ W` (S1), so `Σ#` gains "labels pending in this display ∈ {0, 1}" for that configuration only;
  - its R-INERT failure (`\catcode` via `\@makeother`) must be looked at in the trace: if the catcode change is inside `\label`'s own group and restored, the class is "local assignment inside a group `N` opens" and it is admitted.
- **`\ref`, `\pageref`:**
  - read_label; the text is the aux table's first or second field, or `??`;
  - `\@setref` always ends with `\null` [R], so E0 never depends on the aux file (P1: pass 2 has pages) [M];
  - the page field is a numeral whose *value* is layout-dependent but whose *shape* (a digit string) is fixed, so the model abstracts it as `PageNum`.
- **`\section` family** (Moving title, look-ahead `*` and `[`):
  - `R` = {mode/frame (P3), `\c@secnumdepth` (constant), `\if@noskipsec`, `\if@inlabel`, `\everypar` kind}, `W` = {section counters (exact), `\@currentlabel`, `\if@nobreak`, `\everypar` kind (`\@afterheading`), aux (toc entry)};
  - error site: `Not allowed in LR mode` → E3 when the frame top is hbox (P3).
- **`\item`** and `itemize`/`enumerate`/`description`:
  - `R` = {depth counters, `\if@newlist`, `\if@inlabel`, the counter values used by `\theenumi…iv`};
  - error sites: `\@toodeep` (depth guard), `\@noitemerr` (P10, P11), `\@ctrerr` via `\@alph`/`\@Alph` (P2), `Lonely \item` (frame guard);
  - `W` = {counters, switches, `\everypar` kind, `\@currentlabel`};
  - the optional label is Inspected with space-skipping look-ahead (R6).
- **`\begin{X}`/`\end{X}`:**
  - a generic mechanism: X is a Key into the contract's environment table (E2 on a miss);
  - `\@currenvir` joins `Σ#` (E5 on a mismatch);
  - the body mode and context come from the environment's program.
- **`\cite`** (+ `.bbl`):
  - Key-list, Inspected by `\@citex@checkblank`, `\immediate` aux_write `\citation` (re-read as `\@gobble`), read_cite;
  - the `.bbl` is **part of the closure** (A.1.1) and is parsed under the same grammar;
  - `thebibliography` is a list environment, and `\bibitem` aux_writes `\bibcite`;
  - a missing `.bbl` is a warning (R9), not E10.
- **`\maketitle`, `\title`, `\author`, `\thanks`, `\and`:**
  - Stored slots, meaning versions (R1–R5), and a counter guard for `\thanks` (Q8).

### 2.7 Soundness argument and its residual premises (stated as the trusted base will state them)

**Claim.** If I1–I6 pass for every admitted name, then for every document in the fragment and every reachable state, pdfTeX executes each admitted name as its program says. The argument has three steps:

1. **O1.** The name's control flow reads only `R_N` and the argument's class-determined information. Such a read is a branch, an arithmetic operation, a lookup, or an error site, and I2 and I3 enumerate them over the token-exact closure.
2. **O2.** The program was selected on, and agrees with, at least one probe per reachable cell. Within a cell, pdfTeX's control path is the same, because every branch point's operands are cell-determined. The effects on non-`Σ#` state are unobservable to every admitted name (I6), so one probe per cell attests the cell.
3. **O3.** The post-state dump confirms the writes. I6 confirms that nothing written escapes into another admitted name's decision without being modelled.

**Residual premises** (these join T2/T4 in §G.2; each is attested, none is proved):

- **P-1: the censuses are complete.** I2 and I3 see every read, branch and error site of `K_N`. Mitigations:
  - token-exact dumps;
  - rejection on anything unclassifiable;
  - I4(i) cross-checks every executed conditional and error site against the census, so any miss seen in any probe is a defect found;
  - adversarial review of the analyser first (C-30).
- **P-2: implicit engine reads.** A primitive reads engine parameters it does not name (`\par` reads `\hsize`, `\parshape`, `\hangindent`; math reads `\fam` and the font tables). These affect *layout* and can reach an *error* only through the I3 engine sites. Examples: `Dimension too large`, `Arithmetic overflow`, `Infinite glue shrinkage…`, `Insufficient symbol fonts`, the float and insert limits. So P-2 reduces to "every engine error site reachable from `K_N` is in I3", which is a finite, generated table per engine pin. Layout-driven sites (page builder, output routine) stay behind the §A.1.5 side conditions and the stress probes (many pages, footnote-heavy pages, split footnotes).
- **P-3: determinism and no hidden state.** pdfTeX is deterministic given its input files, the format, the environment and `SOURCE_DATE_EPOCH`, and the oracle already allow-lists these (C-91). Non-eqtb state (`\pdf*` objects, `\global\setbox`, open streams) is covered by `\tracingassigns` only in part [U, §G.1 risk 9]. **I4's calibration must include one known example per state kind** and fail the generator if the tracer misses it.
- **P-4: representative-per-cell for arguments.** Parametricity holds because an argument can only be Exec'd (then the kernel decides its own tokens recursively), Moved (then the write image is a function the model computes), Stored (then it is replayed and decided at the replay), Keyed (then its characters are typed) or Inspected (then the partition is explicit). Any other flow is rejected by I2. This is what turns C-85/§G.1 risk 1 ("a finite probe set stands in for all argument contents") from a hope into a structural claim. It is still a claim about I2's classification (P-1).

**What is still empirical, stated plainly.** The static analyser is trusted-base code (T4) over a Turing-complete macro language. It is allowed to be incomplete in the direction of *rejecting*, and must never be incomplete in the direction of *missing a read*. A missed read is exactly the kind of defect C-92 and D-2 are. The three defences against it are:
- the dynamic cross-check I4(i);
- the global R∩W closure I6;
- the release-blocking differential with generators for every guard boundary.

None of them is a proof. The owner asked for a perfect system. The honest statement is that it is perfect **relative to** P-1 to P-4 and to `Faithful`, which are named, pinned and attested, and that every counterexample in §6 is now caught by a named instrument rather than by luck.

---

## 3. What enters the Coq state, and the multi-pass semantics

### 3.1 The abstract state `Σ#` (added to `Semantics.v`'s `state`)

| component | domain | read by (examples) | exact? |
|---|---|---|---|
| TeX mode | {V, internal V, H, restricted H, M, display M} | `\section` (P3), `\item`, `\\` | yes (6 values; today's frames already imply it) |
| frame stack | today's frames + FSemi, FBox, FVBox, FInsert, FEnv(name), FList(kind) | E5, context guards | yes |
| list depth, enumerate/itemize depths | `nat` ≤ engine/format limits | `\@toodeep` (P5, P6) | yes |
| counters | name ↦ `nat` (reset lists from the contract) | representations (P2, Q4, Q8), `\ref` text | yes; bounded by the 20,000-token bound |
| switches | name ↦ bool (only those in ⋃R ∩ ⋃W) | `\if@newlist` (P10), `\if@inlabel`, `\if@nobreak`, `\if@noskipsec` | yes |
| `\everypar` kind | finite enum of attested token lists | the next paragraph's start (`\@afterheading`, `\@doendpe`, list items) | yes |
| slots | name ↦ unset \| token list (grammar) | `\@title` (Q10), `\@currentlabel` | yes |
| meaning versions | name ↦ version | `\title` (R3), `\and` (R1/R2) | yes |
| resources | write streams, insert classes, float list | R11, `k_float` | yes, with the engine or format limit |
| environment stack | `\@currenvir` | E5 | yes |
| `aux_out` | ordered list of aux entries written in this pass (§3.2) | the next pass | yes (as data; no layout) |
| `aux_in` | the finite maps read at `\begin{document}`: labels ↦ (text, PageNum), bibcites, toc entries | `\ref`, `\cite`, `\tableofcontents` | yes |
| typeset material | bool (E0) | end of document | yes |

**Deliberately excluded, and why this is safe.** These are kept out of `Σ#`: fonts beyond the attested finite font states, glue and dimension values, box contents, page numbers' values, line and page breaks, and the output routine's internal state.
- None of them may be read by an admitted name's branch, lookup or error site; I6 enforces this.
- Where the engine reads them implicitly, P-2 applies.
- A name that reads one (for example `\addvspace` reading `\lastskip`) needs a finite abstraction of that component (last node kind × sign) to be added *first*, or it is not admitted.

### 3.2 Passes

**The pass function.**

`Pass C (aux_in : AuxIn) (d : doc) : outcome × AuxOut` is `Runs` extended with the state above. `aux_out` collects `aux_write` effects in execution order. Non-immediate writes are emitted at shipout, but their payloads are fixed at `\protected@write` time except `\thepage`. That is why their **order** is execution order and the page field is abstracted.

**Partial aux after a fatal pass.** It is modelled as *unknown*: after a failed pass the model does not claim to know which non-immediate writes were shipped. That is harmless because of the lemma below.

**Reading the aux file.** `read_aux : AuxOut -> AuxIn` is the pass-boundary semantics of LaTeX reading `main.aux` at `\begin{document}`:
- `\newlabel` defines `r@key`, and a duplicate is a warning;
- `\bibcite` defines `b@key`;
- `\@writefile{toc}` is ignored at this point;
- `\citation` is gobbled.

**Reading the toc file.** `read_toc : AuxOut -> list toc_entry` is `\@starttoc`'s re-read of `main.toc` (written from the `\@writefile` entries during the *end-of-document* aux read of the previous pass).

**Two re-read lemmas replace byte-level trust in the round trip**, each proved in Coq over the grammar under standard catcodes and then attested by probes:
- `write_roundtrip`: lexing `image t` gives `t`, for moving-safe `t`;
- `aux_parse_exact`.

**The protocol.** `Protocol C d : outcome` replays `_oracle.run_to_fixpoint` *exactly* (with the D-1 fix):

```
Protocol d := let o1 := Pass ∅ d in
              if o1 compiles then confirm (aux o1) d            (* 2 runs *)
              else let o2 := Pass (aux o1) d in if o2 compiles then confirm (aux o2) d
              else let o3 := Pass (aux o2) d in if o3 compiles then confirm (aux o3) d else o3
confirm a d := Pass a d                                          (* its outcome IS the verdict *)
```

"Compiles" per pass means rc 0 **and** "Output written" in *that* pass (D-1). No fixpoint is assumed: Q1 shows a document that oscillates [M], and the model must be able to say so.

### 3.3 Theorems

These replace `strict_decider_exact` as the capstones; it stays for the single-pass core.

- `pass_exact`: `decide_pass C a d = r <-> Pass C a d = r` (as today, per pass, both directions).
- `protocol_exact`: `decide C d = ProvenReady <-> Protocol C d = Compiles`, and the Fatal direction with reason and location. This is the new `strict_decider_exact`.
- **`aux_independent_fatal`** (the theorem that *replaces* the unproved §C.2 claim): for every `d` in the fragment and all `a a'`, `Pass C a d` is `Fatal r l` iff `Pass C a' d` is `Fatal r l`.
  - It holds for a fragment in which every aux-dependent text (`\ref`, `\pageref`, `\cite` output, toc entries) is admitted only in contexts where all its shapes are attested. The shapes are `??`, a numeral, `[n]`, and a toc line built from a moving-safe title.
  - It is **proved, not assumed**. If the toc contexts ever break it (a title fine in the heading but fatal in the toc), the proof fails and the admission of that title shape fails with it.
- `protocol_stabilises`: corollary. In the fragment, `Protocol C d = Pass C (aux (Pass C ∅ d)) d`, and its fatal/compile status equals `Pass C ∅ d`'s. So the cheap single-pass decider is exact, *as a theorem*.
- `material_aux_independent`: E0 does not depend on the aux file (a numeral, `??` and `\null` are all material) [R: `\@setref` ends with `\null`; M: P1].
- The bridge is unchanged in form. `Faithful` quantifies over the fragment with `Protocol` instead of the one-pass `Runs`. **This is a change to a pinned body**, so it needs the C-87/C-88 pins to be re-issued with owner sign-off.

**Moving-argument re-typesetting** (`\tableofcontents`): the toc entries of `aux_out` from pass k are typeset in pass k+1 in the toc context. That context is `\contentsline`/`\l@section`: a paragraph in `\bfseries` with `\numberline` in an hbox. It is a new context in the CONTEXT stage. `aux_independent_fatal` then *requires* every admitted title token to be attested in it, which is how S6-like failures in the toc are kept out.

---

## 4. Front matter and packages (step 3)

### 4.1 The practical path (fits ADR-012 decision 3)

**Per document: attest the exact preamble, on demand, cached by its hash.** The key is the configuration key of A.1.2: class + options + ordered loads + options + interleaved definers + format hash + content hashes of vendored files. The service runs pdflatex only on the preamble and on probe documents, never on the body.

1. **Configuration contract.** `gen_contract.py` as built (M1 slices 1–2): closed world, catcodes and active characters, `load_outcome`, files read, counters, key families, unicode table. It adds the new fields:
   - I1 dumps for the names in (2);
   - the configuration's `Σ#` schema: the switches, counters, slots and meaning-versioned names that appear in ⋃R ∩ ⋃W for the body's names;
   - the output routine's and hooks' closure.
2. **Use-based name set.** The body is parsed under a *permissive* reader that uses the closed world only to classify tokens. It returns the set U of `(name, context kind, argument classes)` the body actually uses, plus the environments. Only U is probed.
3. **Behaviour programs for U** through I1–I5, reusing the cache (§4.3). I6 runs over U ∪ the configuration's admitted core.
4. **Decide.** If a use falls outside an attested cell, the verdict is `PENDING (predicted …)` (heuristic) until the probe for that cell finishes. It is never PROVEN by extrapolation.

### 4.2 Cost model

The inputs are measured or published:
- The median body uses **75** distinct control words (p90 142, max 353), and **12** distinct environments (p90 21) [M: census over 1,119 unsealed roots, root file only].
- Configuration trace and dump: 0.2–2.3 s (B.3).
- Solo probes: ≈ 0.11 s wall each on 6 workers (B.3).
- The article full-signature run (M1 slice 2): 2,148 names, 57,027 solo probes, 3.9 h on 8 workers, i.e. ≈ 26.5 probes/name.
- Phase-1 signatures: 58 probes/name. Slice A: 36 base probes plus stage-2 probes per name.

| step | per name | per median paper |
|---|---|---|
| I1 + I2 + I3 (static; one pdflatex run dumps all of U at once) | ~0 probes | 1 run + analysis, ≈ 5–20 s [I] |
| I5 cells | cells ≈ contexts used (≈ 2–4) × guard blocks (1–6) × argument classes (1–3); **≈ 20–120 probes**, each run to the fixpoint (2 engine runs) | 75 × ~60 ≈ 4,500 probes |
| wall time with the paper's preamble (0.5–2.5 s per run) on 8 workers | — | **≈ 10–45 min cold** [I]; the 3.9–5.2 h full run is avoided because only 75/2,148 ≈ 3.5 % of names are probed |
| with a warm footprint cache (§4.3) | 0 for hits | seconds to a few minutes; **the hit rate must be measured** |

That is too slow for a first keystroke and acceptable for "open a project, get PROVEN within the hour". Meanwhile the verdict is `PENDING (predicted)` (§D.3). Two further reductions are *not* proposed, because they would change what is attested:
- **Dumping a format of the paper's preamble** makes probe runs cheap. It is a different engine input (`\everyjob`, the file list, `\AtBeginDocument` timing), so it may be used for **triage only**. The admitting probes run on the real preamble.
- **Batched probes** stay triage only (97.2 % batch/solo agreement, OPEN-120).

### 4.3 Reuse across configurations: the footprint key (sound)

TeX is deterministic (P-3), so two configurations give the same probe outcome for `N` in a cell if they agree on everything the execution can read. The key is the hash of:
- the token-exact closure `K_N` (I1), including hooks and the output routine;
- every register and parameter named in `K_N`, plus the full engine parameter table (conservatively; P-2);
- the catcode table;
- the TFM/`.fd` content hashes of every font `K_N` can select;
- the `Σ#` schema.

A cache hit transfers every attested cell. A miss reprobes.
- **Prediction** [I]: kernel math symbols hit across almost all configurations, since their closure is empty. Sectioning hits across configurations that do not patch it, and misses under hyperref (which patches `\refstepcounter`, `\label`, `\@sect`) and under geometry (which changes the parameter table).
- **Measure this** on the unsealed frame before relying on it.

### 4.4 Package families: what to admit first, argued

| family | papers loading it (of 1,119 unsealed) [M] | why it is or is not safe | order |
|---|---|---|---|
| **amssymb, amsfonts, latexsym** | 809, 508, 135 | They only add math symbols (`\DeclareMathSymbol` → MathChar kind) and lazy `.fd` loads (`\mathbb` → `umsa.fd`: `lazy_files`, E10 if absent). They have no body-time code of their own, so the footprint is empty. The Turing-complete part runs at load time and is covered by `load_outcome`. | **first** |
| **amsthm** | 533 | Definers are preamble-time (`\newtheorem`, `decl_templates`, C-81's matrix); theorem environments are list-based (`\trivlist`) with an optional note (Inspected). `\qed`/`proof` use a QED stack (`\QED@stack`, `\iffirstchoice@`), so a `Σ#` slot plus `\qedhere`'s look-ahead into the enclosing display is needed. Medium work, high payoff (theorem environments in 533 preambles). | second |
| **graphicx** | 806 | `\includegraphics`: keyval options (`TyKV` family `Gin`, one misspelled-key probe per key), an **input file** read by pdfTeX's image code (`\pdfximage`). The file is part of the closure by content hash, and its readability and format are attested per file hash by one probe (a corrupt PNG is fatal). The extension search list comes from `\Gin@extensions`. The float context is M4. | third (with floats, M4) |
| **amsmath** | 878 | Large, and mostly body-time code: `\text` runs its argument 4 times (Exec^4, guarded); `equation`'s label rule (`\df@label`, S1); `\tag` context rules; `\DeclareMathOperator` (preamble definer); the alignment environments measure their body twice (`\ifmeasuring@`) and belong to M4. Admit it in slices: symbols and `\text`, then `equation`/`\[`, then `\operatorname`, then alignments (M4). | fourth, sliced |
| **hyperref** | 782 | Last. It patches `\refstepcounter`, `\label` (five-field `\newlabel`), `\ref`, `\@sect`, `\footnote`, `\caption`, and the output routine (anchors, `\pdfdest`). It adds a **second expansion regime** for every moving argument (`\pdfstringdef` for bookmarks), so every moving-safe name needs a second, "PDF-string" program, whose failure class is a warning, not an error ("Token not allowed"). It writes and re-reads a second file (`.out`), which becomes a new `Σ#`/aux schema, and it emits driver specials. Its footprint changes the key of nearly every structural name (§4.3), so the cache gives little. **Its code is not a reason to exclude it (its code is fixed); its breadth is.** | last |

Also in the top 40 by load count, and each needs its own argument: `xcolor` (531), `booktabs`/`multirow` (alignment, M4), `inputenc`/`fontenc` (UTF-8 and encodings: this is **the E11 table**), `url`, `mathtools`, `geometry` (parameters only: cheap, but it shifts every footprint key), `enumitem` (keyval list options: `TyKV`), `tikz` (313: FOREIGN in practice), `cleveref` (193: its load-order fatal is a `load_outcome` fact; its `\cref` builds names from label types, as Key with a type table).

---

## 5. The candidate universe (question 4)

- **Universe:** every name a body can type in the configuration's closed world:
  - control words of letters;
  - control symbols;
  - the configuration's active characters;
  - environments (`X` with both `\X` and `\endX`);
  - UTF-8 code points with `u8:` definitions.

  For `article` that is 2,148 typeable control sequences and 41 environments (OPEN-120), not a sample of 400.
- **Order:** by frequency of use on the **unsealed** frame (ranks 0–399 and 2000–2718, as §I.6; never 720–919), grouped by mechanism, so that one `Eff` constructor unlocks a family:
  1. MathChar/Char (196);
  2. other argument-free names (the 1,312 slice-2 attested names minus those with arguments);
  3. one-argument Exec commands (text fonts, `\mathbf`/`\mathrm`/`\mathcal`);
  4. math-scanner arguments (accents, `\sqrt`);
  5. two-argument FSemi (`\frac`);
  6. Key names (`\label`, `\ref`, `\cite`);
  7. Moving (sectioning, `\footnote`, `\caption`);
  8. Stored (title block);
  9. environments;
  10. UTF-8.
- **Cost for `article`:**
  - static I1–I3 over all 2,148 names: one dump run and analysis, minutes [I];
  - I5 on the survivors: ≈ 2,148 × ~40 ≈ 86k probes, ≈ 6–9 h on 8 workers [I], once per engine pin, re-used by the footprint cache;
  - math symbols alone: ≈ 196 × 20 ≈ 4k probes, under 15 min.
- **What the census says** [M, root-only regex; used to *order*, never to prove]: in this frame, 34 bodies use only the top-100 names, 116 only the top-400, 245 only the top-800 and 415 only the top-1,600. Names are therefore necessary but far from sufficient (next section).

---

## 6. Adversarial self-critique: counterexample search

For each admission rule I tried to build a document in which the rule admits a name whose behaviour on an unprobed input differs. "Rule" means the rule under attack; the right column says whether the attempt breaks it, and what the design changed in response.

| # | attack | against | result [M unless marked] | outcome for the design |
|---|---|---|---|---|
| 1 | 27th item of an inner `enumerate` (P2) | trace attestation of `\item` on success paths with a few items | **succeeds**: 26 items compile, 27 give `Counter too large` | defeated by I2 (the `\ifcase` over `\c@enumii` via `\theenumii`), I3 (`\@ctrerr` site), exact counters in `Σ#`, and guard probes at 26/27 |
| 2 | 27 footnotes in a `minipage` (Q4); 10 `\thanks` (Q8) | admitting `\footnote` and `\thanks` from context probes | **succeeds** | same fix; the representation is chosen by context (`\thempfootnote`), so the frame kind is in the guard |
| 3 | 7 nested `itemize`, 5 nested `enumerate` (P5, P6) | the CONTEXT stage as built (one level of carrier) | **succeeds** against one-level context probing | depth counters in `Σ#`, guards probed at k and k+1 |
| 4 | text before the first `\item`; an empty list (P10, P11) | per-name probing of `\item` and `\end{itemize}` separately | **succeeds**: a switch written by one name and read by another | I6 (the R∩W closure) forces `\if@newlist` into `Σ#` |
| 5 | `\section` in `\mbox` (P3) vs in `center`/`\parbox`/`\footnote`/after `\item` (compile) | frame abstraction without restricted-horizontal mode | **succeeds** if the mode is not exact | mode is exact in `Σ#` (6 values); the context stage covers every frame kind |
| 6 | `\title{a^b}` before vs after `\maketitle` (R4/R3); `\and` (R1/R2) | a static per-name signature for `\title`/`\and` | **succeeds**: the same name, two behaviours | meaning versions in `Σ#`; I4 sees `\global\let\title\relax` as a write to a meaning, which must be modelled or rejected |
| 7 | `\item`, newline, `[$]` (R6); `\\ [$]` (R7b) | FOLLOWER probes with the follower adjacent only | **succeeds** against adjacent-only followers | look-ahead is Inspected with space-skipping; follower probes gain space and newline variants |
| 8 | `\frac{a\over b}{c}` (Q2) | "run the argument in a math group" (the slice-A model) | would **succeed** if `\over` were admitted; today `\over` is not in the fragment | FSemi frame kind; the grammar keeps generalised fractions and unbalanced `\left`/`\right` out of FSemi arguments; I2 flags list-sharing |
| 9 | `\section{A\footnote{b}}` (S6, S4) | admitting names inside moving arguments from use-site probes | **succeeds**: fatal at write time | Moving class: only moving-safe names are allowed in moving arguments, with the write image computed and the round trip proved |
| 10 | two `\label`s in one `equation`, kernel vs amsmath (S1c/S1) | reusing `article`'s `\label` program under another configuration | **succeeds** | the footprint key (§4.3) differs under amsmath (`\label` is rebound in displays), so there is no reuse, and `\df@label` enters `Σ#` |
| 11 | 16 × `\tableofcontents` (R11) | per-occurrence attestation | **succeeds** (C-85's shape, at 16) | resource counters in `Σ#` with limit probes |
| 12 | a pass-dependent verdict inside the fragment: `\label{a}\ref{a}` (P1), `\pageref` (P1c), `\ref` in a toc title (P8), `\label` in `\mbox` (P15), `\label{a~b}` (Q7) | `aux_independent_fatal` | **fails to break it** in 6 tries (every pass identical; `\@setref` ends with `\null`, so E0 cannot flip) | consistent with the lemma, which is still to be *proved* in Coq and not assumed |
| 13 | an oscillating document (Q1, outside the grammar) | the oracle predicate, not the rule | **succeeds against the ORACLE**: READY reported, the last pass has no pages | D-1: fix the oracle before any aux-reading admission; the model replays the protocol exactly, so oscillation is expressible |
| 14 | `\cite{a,,b}`, `\cite{}` (R8), `\bibliography` with no `.bbl` (R9) | the Key-list typing of `\cite` | **fails to break it**: compiles with warnings; R9 is E0 | typing is correct; `\@citex@checkblank` is an Inspected partition {empty, non-empty} |
| 15 | a hook or socket added by a package to `\label`/`\refstepcounter` | R-INERT's static closure | **succeeds in principle** (D-2: the closure stops at `\hook_use:nnw`) [M+R] | I1 follows hooks and sockets as token lists; they are part of the footprint key |
| 16 | `\afterassignment` escaping from `\@defaultunits` into user input (text fonts) | R-EFFECT's "consumed within N" class | **fails**: the assignment it guards is the macro's own (`\@defaultunits\@tempdimb\f@size pt\relax\@nnil`); the user cannot reach the gap [R] | admitted, with I4(iii) as the check; `\fontsize{<user>}` stays out (TyDimen literals only) |
| 17 | amsmath `\text{\footnote{b}}` (S2) | Exec^4 with an effectful argument | **fails**: compiles, because amsmath guards the effects [M] | Exec^n requires each effect in the argument to be guarded or idempotent, checked by trace (count the `\stepcounter` executions) |
| 18 | a name whose error path is reached only through a table lookup on a user key (`\ref{\zzundef}`, §B.2) | Key typing | **fails** when keys are characters only; would succeed with a control sequence in a key | the lattice type TyLabel is characters only (as OPEN-120) |

**What changed in the proposal because of the search.**
- Attacks 1–7, 9–11 and 15 are why the rule has *static* censuses (I1–I3) and a global closure (I6) rather than "trace the probed paths", why `Σ#` carries exact counters, meaning versions and resources, and why look-ahead and moving arguments are argument-flow classes.
- Attack 13 produced D-1.
- Attack 12 is the reason `aux_independent_fatal` is a theorem to prove, not a premise.

**Attacks I could not settle without more work** (open, and recorded as risks):
- an admitted name whose footprint reads `\lastskip`/`\lastbox` (`\addvspace`, `\@startsection`), where the abstraction "last node kind × sign" has to be designed and probed;
- layout-dependent output-routine failures with footnotes that split across pages;
- whether `\tracingassigns` shows `\global\setbox` and `\pdf*` object creation (P-3; calibrate).

---

## 7. Milestone plan, payoff, and the ways each step could produce a wrong PROVEN

**How the payoff was estimated.** It is a regex census over the root files of the 1,119 unsealed papers (§I.6's frame: ranks 0–399 and 2000–2718; sample 3 untouched) [M]. "Covered" means that every construct of the body falls in the stated classes. These are **upper bounds on bodies**: children of `\input` are not scanned, admission is assumed to succeed for every name in a class, and the front matter is counted separately. Real numbers must be measured with the extracted decider, as in §I.6.

- **Front-matter reality** [M]: 474 `article`, 248 `amsart`, 80 `IEEEtran`; median 16 packages; 971 of 1,119 have preamble definers; 432 use `\def`/`\let` in the preamble; only 3 are a bare `article` with no options and no packages. Even with the class ∈ {article, amsart} and packages ⊆ {amsmath, amssymb, amsthm, amsfonts, graphicx, hyperref}, only **13** qualify (9 without preamble definers). **A fixed "safe package set" is not a strategy; per-document attestation is.**
- **Body reality** [M]: the scenarios below admit, cumulatively, all of `article`'s attested names, structure (sectioning, labels, cites, lists, title block, footnotes), `amsmath`/`amssymb`/`amsthm`/`graphicx`/`hyperref` names, theorem environments, ASCII punctuation and control symbols, and user `\newcommand`-family macros.

| scenario (cumulative) | bodies covered / 1,119 | the largest remaining blockers |
|---|---|---|
| as today | 2 (root-only census; §I.6's decider measured 0) | names 1,117 |
| + all names of `article` + structure + chars | 2 | environments, other packages' names, non-ASCII |
| + the 6 packages' names, theorem environments, user macros (**no** alignment or floats) | 4 | environments 968, other packages' names 948, non-ASCII 709, `\input` 257 |
| + UTF-8 | 10 | |
| + alignment/tabular/floats (M4) | 22 | other packages' names 948, non-ASCII 709 |
| + UTF-8 (with M4) | 49 (29 without preamble `\def`) | |
| + `\input` closure (children unscanned: loose) | 135 (72) | |
| + every other package's names (per-document configurations) | 360 (204) | environments 754 |
| + every environment | 1,098 (680) | |

| milestone | deliverable | expected payoff on unsealed roots (in the fragment, with the decider) | ways it could produce a wrong PROVEN | mitigation |
|---|---|---|---|---|
| **S3.0** prerequisites (S) | D-1 oracle fix plus re-grade; D-2/D-3 token-exact dump replacing `\meaning` parsing in R-INERT; converge `gen_strict_signatures.py` with `contract_signatures.py` (OPEN-121) | 0 (hygiene) | a re-grade that moves cells unnoticed | publish the diff as an oracle-baseline change (as OPEN-118) |
| **S3.1** math names (S) | all MathChar/Char names of `article` through the existing phase-1 pipeline, whole universe instead of the 400 sample | **0** (they block no body on their own) [M: 2 → 2]; unblocks later rows | a symbol whose mathcode is `"8000` (math-active) behaves like a macro | I2 checks mathcode; the `"8000` class goes to the macro path |
| **S3.2** R-EFFECT instruments + `Eff` + `Σ#` core (L) | I1–I6; `Eff` interpreter in Coq; FSemi and ScanMath argument modes; text fonts, `\frac`, `\sqrt`, accents, `\label`/`\ref`/`\pageref` (single pass, with `aux_independent_fatal` proved) | 0 (the front matter still blocks) | analyser misses a read (P-1) | I4(i) cross-check; adversarial review of the analyser before any admission (C-30); differential generators for every guard boundary |
| **S3.3** passes (M) | `Pass`/`Protocol`, `aux`/`toc` schema, `write_roundtrip`, `protocol_exact`; sectioning, `\tableofcontents`, title block, `\cite` + `thebibliography` + `.bbl` in the closure, `\footnote` | 0 | the toc context breaks `aux_independent_fatal`; a moving-safe misclassification | the proof itself fails, blocking the admission; toc-context probes; S6-like probes in every moving slot |
| **S3.4** environments and lists (M) | generic `\begin`/`\end`, the list family, `center`/`quote`/`flushleft`, `equation`/`displaymath`, `abstract` | 0 | a missing guard on list state | the I6 closure; boundary probes (P10, P11, P5, P6, P2) as permanent rule probes |
| **S3.5** characters and UTF-8 (M) | `[ ] * ' \` " ~ \\ \, \; \! \% \& \_ \{ \}`; the `u8:` table as E11 (per configuration) | 0 | `inputenc`'s `u8:` dispatch has per-code-point code (some are macros with arguments) | each code point is a name with its own program; unattested code points are outside |
| **S3.6** per-document configuration attestation + user `\newcommand` (L) | the service of §4.1, the footprint cache, NDef (ADR-012 M3), `\newtheorem`/amsthm | **first non-zero number.** Bound from the census: ≤ 4 (without M4) … ≤ 10 (with UTF-8). **Expect low single digits** [I] | a configuration effect missed by the use-based probe set (for example a package that makes `"` active) | the closed world and catcode table come from the configuration contract (complete by construction); I6 over U ∪ the core; `PENDING` rather than PROVEN for any unattested cell |
| **S3.7 = ADR-012 M4** alignment, floats, graphicx (L) | tabular/array/amsmath alignments (measure-twice, Exec²), floats with `k_float`, `\includegraphics` with per-file probes | ≤ 22 → ≤ 49 with UTF-8 [bounds] | layout-dependent output-routine failures | §A.1.5 side conditions; output-routine error sites in I3; stress probes |
| **S3.8** widening by marginal coverage (per package) | amsmath slices, xcolor, url, booktabs, natbib, cleveref, … hyperref last | toward ≤ 360 (every other package's names) | the second expansion regime (hyperref); package hooks | a separate program per regime; hooks in the footprint key |

**The payoff, in one sentence.** Everything through S3.5 is necessary infrastructure with a measured payoff of zero real papers. The first real papers arrive with per-document configuration attestation (S3.6). Double digits need UTF-8 and alignment. Beyond that, coverage scales with the number of packages whose names the attestation pipeline admits, not with work on the kernel.

---

## 8. Open decisions for the owner

1. **Adopt R-EFFECT (static censuses + traced partition probing + global R∩W closure) as the admission rule, with R-INERT kept as a triage pre-filter?** The alternative is to keep R-INERT and admit structure by hand-written Coq rules per name. That is simpler to review, but it scales by hand and contradicts "no name is written in Coq".
2. **Accept four new residual premises (P-1 to P-4) in the trusted base**, next to `Faithful`? P-1 (completeness of a static analyser of TeX macros) is the one that carries the weight.
3. **Change the oracle predicate (D-1):** delete the PDF before each pass (recommended), or require `Output written` in the last log. Either one re-grades every multi-pass artefact.
4. **Re-pin `Faithful`'s body** from single-pass `Runs` to `Protocol` (C-87/C-88 pins re-issued). This is a change to a trust-boundary definition.
5. **Probe budget per new configuration**: accept ≈ 10–45 min cold (PENDING meanwhile) for PROVEN on a new preamble? Or cap it and publish coverage at the cap?
6. **Footprint-keyed reuse across configurations** (§4.3): adopt it as sound (it rests on determinism, P-3, and on the key's completeness, P-1), or require re-probing per configuration always (≈ 10–45 min per paper, every paper)?
7. **Order** (§7): S3.0 → S3.1 → S3.2 → S3.3 → S3.4 → S3.5 → S3.6 puts five milestones of zero measured payoff before the first real paper. The alternative is to build S3.6 (per-document configuration) earlier, on the current fragment. That also yields zero papers, because bodies need structure, but it de-risks the service sooner. Which risk first?
8. **hyperref**: accept that it comes last, even though 782/1,119 load it, so that a large share of papers stays outside for a long time?
9. **Record D-1 and D-2 as corrections now**, independently of this ADR, and open ledger rows for them? Use the next free C-ids: a parallel branch appears to be using C-93.
