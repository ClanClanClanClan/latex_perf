# Scoping the abstract interpreter of ADR-015's synthesis (OPEN-129)

**Status:** scoping report, 2026-10-06. Nothing here is built; one feasibility trace was run.
**Asked by:** owner decision E13 (2026-10-06): the fast-interpreter fallback is not funded until
this scoping reports. **Ledger:** OPEN-129. **Branch:** `spike/v27165-ai-scoping`, cut from
`spike/v27165-engine-translation` at `67ca47df`.
**Reads:** ADR-015 on `origin/main` (D1–D4, E1–E10, Consequences); the drafts ADR-013 (R-EFFECT)
and ADR-014 (interpreter) in `docs/v27/adr/drafts/`; the re-audit dated 2026-10-07 (premises 8–11; a
local file, not in the repository); `docs/v27/STRICT_TIER_DESIGN.md`; the spike's H1, H2, H3 and
H5 reports and `h2/coq` (`Values.v`, `Interp.v`, `Boundary.v`, `Extract.v`, `B2Equiv.v`);
`proofs/Strict`; PROJECT_STATE C-83 to C-100.

Evidence tags as elsewhere: **[M]** measured, **[R]** read from a source, **[I]** inferred,
**[U]** recalled or unverified. Every [M] names its artefact under [`ai/`](ai/).

## 0. The answer, in brief

- **Verdict: FEASIBLE WITH CONDITIONS** (§9). Nothing found makes a sound summary-based static
  decider impossible within the perfection standard: every case the design cannot settle is
  `Stuck`, which means outside the tier, never guessed. But the project's record has **none of
  the machinery**, and the scoping found that one unknown decides the architecture. That unknown
  is a proof that TeX's own allocator and hash table can be treated abstractly. Without it, no
  summary can be reused, not even between two uses of `\emph` in one paper, and the synthesis
  degenerates into running the model on the document (§4.3).
- **The judgement** (§2) is a Hoare-style summary over the engine's real state, at *segment
  boundaries* of the input. It has holes for arguments, guards on the following token, a
  per-capacity peak, and `Stuck` as the escape. **The composition theorem** (§2.3) is an
  induction over segments using determinism. It is plausible and cheap to prove. All the
  difficulty is in producing summaries that are both sound and reusable.
- **The feasibility trace** (§7) used `\emph` from `latex.ltx`. It exercises a conditional on
  the mode, a group, `\aftergroup`, `\futurelet` on the argument and on the token after the
  group, argument splitting by a delimited parameter, `\csname`, two global assignments, a
  configuration hook, and a font load on first use.
  - The B2 model build executed that code in format state and printed the same 18,849 terminal
    bytes as the pinned binary [M]. It then stopped `Stuck` at the TFM open of `cmti10`
    (`readfontinfo → bopenin`, an unmodelled external) [M].
  - So the TeX side of the model suffices. The C boundary is the first gap, and it is being
    built in parallel. Everything abstract (`exec#`, the domain, holes, the key's lemmas) does
    not exist [R].
- **The key** (§4): the summary's read set, recorded at the level of the engine's memory cells
  by the instrumented abstract run itself. Its reuse is sound by a frame lemma proved once for
  `PS`. That is unlike ADR-013's P-1, which trusted a TeX-level static analyser.
  - Cross-position and cross-configuration reuse needs read sets that are invariant under
    renaming of allocated addresses and hash slots. Hence the allocator/name-map lemma (AI-2,
    the critical milestone).
  - Hit-rate upper bound for `\emph` on sample 2: about 99 of 200 papers share a coarse
    `\emph`-relevant configuration signature with an earlier paper [M on a crude instrument; the
    hit rate itself is I].
- **Cost** (§6). On a cache miss, the abstract run is a second extracted interpreter over the same
  AST. It is not the "closure compiler", which was never built [R]. It runs ≈ 5–20× slower than
  the concrete model per explored path, times the number of forks [I]. The concrete model
  already runs ≈ 315× pdfTeX on the format load and ≈ 11,700× over the whole meaning dump (B2)
  [R]. A new command in a new configuration therefore costs minutes to hours of CPU [I]. The
  keystroke path folds cached summaries and is fast [I].
- **The plan** (§8): six milestones, each with its PASS and KILL criteria written now. The first
  two (`exec#` with its two generic lemmas; the allocator/name-map abstraction) decide the
  architecture within ≈ 8–18 agent-weeks [I]. The total is ≈ 20–42 agent-weeks [I], on top of
  ADR-014's C boundary and end-to-end stages, which are prerequisites.

## 1. What exists today, and what ADR-015 assumes [R]

| item | ADR-015 / ADR-014 draft says | on the spike branch at `67ca47df` |
|---|---|---|
| translated engine | the tangled `pdftex.p` as a Coq AST | **built**: 603 of 603 procedures, 185,086 IR nodes (H2 report) |
| `PS` | a reviewed relational semantics `PS.Step`, plus two interpreters (`exec`, `exec#`) proved against it (ADR-014 §2.2) | **`exec` only**: a fuelled big-step interpreter (`Interp.v`, 783 lines). No relational `PS.Step` exists, so `exec` *is* the reviewed semantics. No `exec#` exists |
| closure compiler | `compile` proved equal to `exec` and extracted for speed (ADR-014 §2.2, §7.1); in H.2's work column (ADR-015 D3) | **not built**: `Extract.v` extracts the fuelled interpreter itself (`Separate Extraction run initial_state`). H.2's pass criterion did not ask for it |
| `abstract_sound` | "the only substantial mathematics, proved once for `PS`" (ADR-014 §4.4) | **not started** |
| the abstract domain | `Exact`, `Range`, `Top` for integers and characters, *for the clock and positions only*; everything else concrete (ADR-014 §5.2) | not started. This domain was designed to quantify one document over dates, **not** to summarise a command over many states, which is ADR-015 D2's use |
| symbolic execution of `latex.ltx` | "out of scope" (ADR-014 §8.3, about relating `decide_S0` to the interpreter) | ADR-015 D2 makes it the admission mechanism. This is a reversal of ADR-014 §8.3, and nothing scoped it until now |
| C boundary | ADR-014 §2.5's enumeration | 23 of 189 externals modelled (H2 report); the rest are `Stuck`. File input, TFM loading and the PDF back end are unmodelled |
| preamble or state snapshot | ADR-014 §7.2: marshal the `Store` after the format load, and just before `\begin{document}` reads the `.aux` | **not built**. Every model run reloads the format |
| speed (B2 model build `cae7a953…`) | ADR-014 §7.1 estimate 10–60× | ≈ 315× on the format load, ≈ 11,700× over the whole 23,519-name meaning dump (one run, load up to 283) [R: H5-heap-design.md, H.5 stage 2; re-audit premise 6] |
| the static kernel | `proofs/Strict` (L_S0) decides with per-name signatures `mkSig text_beh math_beh` (`Contract.v`) | built. Its signature type has no field for a group, an argument, a follower, a capacity delta or a state change beyond mode, so it **cannot carry** the summaries of §2. A new contract type and a new `Semantics`/`Decide` pair are needed |

So the record supports ADR-015's *foundation* (a translated engine that executes real format code
exactly). It records nothing about the *admission* step. That step is the subject of this report.

## 2. Question 1: the judgement admission must produce

### 2.1 The objects

- **The engine.** `exec` of `prog` (the translated `pdftex.p`) over `PS` states `S` (heap of
  blocks plus the I/O record, `Values.v`). It is deterministic: it is a Coq function. Write
  `run : S -> Outcome` for a whole job, and `step*` for its partial runs.
- **The world premise**, unchanged from ADR-014 §4.2: `FaithfulEngine oracle` says that the
  oracle's verdict on a job is `Protocol` over `exec`, per (engine revision, image digest,
  architecture).
- **The document** is `P ++ B`: a preamble `P` up to and including `\begin{document}`, and a body
  `B`. The kernel works on `B` only. It needs an abstract **body-start state** `a₀` with the
  concrete state at body start in `γ(a₀)` (§5).
- **Segments.** The kernel cuts `B` into segments `u₁ … uₙ`:
  - one command occurrence, together with the arguments it reads;
  - a run of characters;
  - a group delimiter, a math shift, a blank line, `\end{document}`.

  The cut depends on catcodes, so the abstract state at every boundary must hold an **exact**
  catcode table for every byte of the next segment. Otherwise the run is `Stuck(catcode)`.
- **A boundary state.** `Bnd(s, p, τ)` holds when:
  - the input stack of `s` is the main file's level, at byte offset `p` of the body (the line
    buffer loaded up to the end of `p`'s line, as `input_line` reads whole lines), with **at most
    one** backed-up token list on top of it;
  - that list holds the tokens `τ`, which were already tokenized from the bytes just before `p`
    (`\futurelet` and `back_input` leave exactly this, tex.web §1221, §325);
  - no macro, parameter or inserted level is pending.

  `τ` matters because tokens tokenized under one catcode table keep it after a later
  `\catcode` change. The abstract state therefore carries `τ` *as tokens*; it never
  re-tokenizes them.

### 2.2 The judgement

A **summary** for a segment kind `u` (for example "`\emph` with one braced argument") is a value
`Σ` of the form

```
Σ = Guarded [ (g₁, R₁) ; … ; (g_k, R_k) ]          (k ≤ K, default 64; else no summary)
R = Post a'  Δ                                       -- reaches the next boundary
  | Fatal m ctx l                                    -- pdfTeX stops with this message, context, line
  | Hole (h, a_h) (fun a_after => R)                 -- runs an argument's own segments, then continues
```

Its parts:
- `g` is a guard the kernel can evaluate statically on the document text and the abstract state.
  Examples: "argument #1 is empty", "#1 contains `\nocorr` at brace depth 0", "the next token is
  a character in `{',', '.'}` or a control sequence whose current meaning is `\ifx`-equal to one".
- `a'` is the abstract state at the next boundary.
- `Δ` gives, per capacity counter `v` of the engine, `(peak_v, end_v)`: the largest and the final
  increment of `v` across the segment (§3.5). These are affine in the argument's size where the
  code copies the argument.
- A hole `h` names an argument whose tokens the engine executes as body text. The kernel decides
  that argument's own segments from `a_h`; the summary resumes from whatever abstract state they
  end in.

**Soundness of one summary** (`Sound Σ`), the property admission must establish:

```
forall a s p τ, s ∈ γ(a) -> Bnd(s, p, τ) -> text at p is an occurrence of u ->
  let (g, R) := the first case of Σ whose guard holds on (a, text, τ) in
  match R with
  | Post a' Δ   => exists s', step*(s) = s' /\ Bnd(s', p + |u|, τ') /\ s' ∈ γ(a')
                    /\ no error was issued between s and s'
                    /\ every capacity counter v stayed <= v(s) + peak_v and ended at v(s) + end_v
  | Fatal m c l => run s = Fatal m c l
  | Hole …      => the same, by induction on the hole's segments
  end
```

The guard is part of the precondition. A state or text in which no guard holds has no
summary, so it is outside the tier.

Two properties of this judgement matter. **The property admission must prove** is `Sound Σ`. It
is about `exec` of the engine's own code from *every* state in `γ(a)`: not about a model of
`\emph`, and not about a probe. **The assumption on the TeX state** is exactly `s ∈ γ(a)` together
with `Bnd`. Nothing else is assumed: no "typical" state, no "the format is unmodified", no
"packages do not patch this name". Whatever a package changed is a value in `s`, and the run
reads it, or the read set says it did not (§4).

**Admission** is a Coq function `summarize : Seg -> A -> option Summary`, implemented by `exec#`.
Its theorem is

```
Theorem summarize_sound : forall u a Σ, summarize u a = Some Σ -> Sound_u Σ a.
```

It is proved once, from `abstract_sound` for `PS`. So **no per-command proof is ever written**.
A command whose run the domain cannot follow returns `None`, and that command is outside the
tier.

### 2.3 The composition theorem

```
Definition fold (a : A) (us : list Seg) : Verdict :=        (* the static kernel, per pass *)
  match us with
  | []      => Outside                                       (* a body must end with \end{document} *)
  | u :: r  => match lookup_summary u a with
               | None              => Outside
               | Some (Post a' Δ)  => if capacity_ok a Δ then fold a' r else Outside
               | Some (Fatal m c l)=> NotReady m c l
               | Some (EndDoc R)   => R                     (* the \end{document} segment: §2.4 *)
               | Some (Hole …)     => fold the hole's segments, then continue
               end
  end.

Theorem static_decider_exact :
  forall cfg B a0 s0,
    s0 = body_start_state cfg B            (* the concrete state at body start, pass by pass §2.4 *)
    -> s0 ∈ γ(a0)                          (* §5: by a model run (proved) or a snapshot (premise) *)
    -> (forall Σ in the cache, Sound Σ)    (* by summarize_sound, plus cache integrity, §4.4 *)
    -> decide cfg B ≠ Outside
    -> (decide cfg B = ProvenReady            <-> Protocol cfg (P ++ B) = Compiles)
    /\ (decide cfg B = ProvenNotReady m c l   <-> Protocol cfg (P ++ B) = Fatal m c l).

Corollary static_ready_iff_pdflatex :
  forall oracle cfg B, FaithfulEngine oracle -> (* the same hypotheses *) ->
    decide cfg B = ProvenReady <-> oracle cfg (P ++ B) Compiles.
```

**The proof is an induction on the segments.** Each `Post` step uses `Sound Σ` to move the
concrete run to the next boundary, still inside `γ`. A `Fatal` step is exact by `Sound`.
Determinism (`exec` is a function) turns "some run reaches s′" into "the run reaches s′". Capacity
side conditions add up because each `Δ` is relative to the entry value (§3.5).

The theorem has the same shape as `strict_ready_iff_pdflatex` (`proofs/Strict/Bridge.v`), with
`FaithfulEngine` in place of `Faithful`. Its logical content is small, as ADR-014 §4.4 said of
`decide_exact`. **That is why the theorem is plausible: it puts no load on the induction. The load
is on `Sound Σ`, which `summarize_sound` gives by construction, and on whether `summarize`
returns `Some` for real commands at a level of abstraction that is reusable.**

### 2.4 Passes, the page, and `\end{document}`

- **Passes.** `Protocol` runs up to three passes to the first rc 0, then one confirming pass
  (ADR-014 §4.5). The body-start state of pass k+1 depends on the `.aux` that pass k wrote, so it
  depends on the body. The decider therefore needs:
  - (i) a snapshot just **before** `\begin{document}` reads the `.aux` (ADR-014 §7.2's
    checkpoint);
  - (ii) the `.aux` reading summarised like any other text. It is a sequence of `\newlabel`,
    `\bibcite`, `\@writefile`, … segments, run from an abstract aux content `aux#` that the
    previous pass's fold produced;
  - (iii) the rest of `\document` (the `\AtBeginDocument` hooks: hyperref does a great deal
    here) summarised as one segment.

  `aux#` is abstract wherever the page is abstract. A `\label`'s page number is `Range 1..N`
  (§3.3), so pass k+1 runs on an abstract aux. A `\pageref` typesets digits, which needs only a
  bounded width. An `\ifnum` on the page forks or is `Stuck`. The protocol's verdict is `Compiles`
  only if every pass compiles for every value in `aux#`.
- **The page is asynchronous.** The output routine fires inside segments: whenever material is
  moved to the page while the page is full. That happens even at the start of an `\emph` in
  vertical mode, because `new_graf` calls `build_page` at the outer level (tex.web §1091) [R].
  So a segment's summary must cover "the output routine may fire here", or the abstract state
  must decide that it does not. §3.3 gives the mechanism: a per-configuration **page-safety
  obligation**, proved by the same abstract interpreter on the configuration's real output
  routine, and assumed by every segment summary.
- **`\end{document}`** is a segment whose result is the end of the pass: `\clearpage`, the last
  shipouts, the `.aux` writes, `\enddocument`'s checks ("Label(s) may have changed" is a warning,
  rc 0), and `close_files_and_terminate`. Its summary ends the pass with `Compiles` or `Fatal`.

### 2.5 The hard cases, one by one

Each row says what the judgement does with the case, and what is left. "Inside" means a summary
can exist; "Stuck" means outside the tier.

| case | what happens in `exec#` | status |
|---|---|---|
| **global assignments** (`\global`, `\xdef`, `\gdef`, `\global\font`, e.g. `\emph` leaves `\font@name` globally changed, §7) | `eq_define`/`geq_define` run on the abstract store; the write is a plain write to `eqtb` and `Post` records it; `unsave` leaves global values in place because it runs the real code | inside, **exact** (it is the engine's own code). The risk C-90 named (what a use *leaves behind*) is closed by construction: whatever `Post` omits is unchanged by the frame lemma (§4.1), so nothing a run writes can be missing from it |
| **local assignments, groups** | the save stack is a stack of abstract frames; a summary that opens and closes its own group restores exactly what it saved, by the real `unsave`; a summary that leaves a group open (`\begin{itemize}`) leaves its frame on the abstract stack for the matching close | inside; the frame contents enter the **key** of the closing segment (§4) |
| **`\catcode` changes** (`\makeatletter`, `\verb`, `\url`, `\ExplSyntaxOn`) | the catcode table is in `eqtb` and is written like anything else | inside **only if** the table is exact at every boundary, and the segment says under which table its argument is tokenized (`\url` changes catcodes *before* it reads its argument, so its hole is "the bytes up to the delimiter, tokenized under table C′"). A catcode that is `Top` at a boundary is `Stuck(catcode)` |
| **`\afterassignment`** | `after_token` is a global of the engine; it is in the abstract state | inside; a segment that ends with `after_token` set passes it to the next segment's key. In code `\emph` can reach (`\selectfont` → `\set@fontsize`, when the line spread changed), `\@defaultunits` sets it and the very next assignment consumes it within the same segment |
| **`\aftergroup`** | `insert_token` entries on the save stack, run by `unsave` (tex.web §280–§282) | inside. `\emph`'s `\check@icr` puts `\maybe@ic` there and it runs inside the same segment (§7); for an open environment the entries ride on the frame, and the frame is part of the key |
| **look-ahead** (`\futurelet`, `\@ifnextchar`, `\@ifstar`, keyword and number scanning such as `plus`/`minus` after glue or a digit after `\count0=1`, display `$` with `get_x_token`) | the continuation is a **symbolic token** `t`; a read of it forks on the classes the code distinguishes (`\ifx` against a meaning, a catcode test, a digit test) and becomes a guard | inside when the read is **peek-only** or consumes only characters or meanings that the kernel can see statically. When the code **expands** `t`, it executes the next segment's code inside this one; that is allowed only as a fused two-segment summary (a window of 2), and is otherwise `Stuck(expanding look-ahead)`. This is the C-84 class, now derived from the code rather than guessed |
| **`\expandafter` chains** | ordinary code paths of `expand` | inside; nothing special |
| **`\csname`** | `id_lookup` on a name built from tokens | concrete names (`\csname OT1/cmr/m/it/10\endcsname`): inside. A name built from **argument** characters (`\label{key}` → `r@key`): the hash slot depends on every name in the table, so the abstract run needs the **name-map abstraction** (AI-2, §4.3); without it, `Stuck` |
| **conditionals on runtime values** | `\ifmmode`, `\ifvmode`, `\ifcase\currentgrouptype`: exact (finite mode and group state). `\ifdim\fontdimen1\font>0pt`: exact when the current font is concrete in the key; a fork over a finite font set otherwise. `\ifnum\lastpenalty=0`, `\ifdim\lastskip=0pt`: on the abstract last-node observer (§3.3). `\ifnum\day>28`: concrete under E10's fixed clock | inside up to K live cases; past K, `Stuck(fork)` |
| **`\write`/`\openout`** | `\immediate\write` to the job's `.aux`/`.toc`/`.out`: an abstract append log. A non-immediate `\write` is a whatsit holding a token list that is expanded **at shipout**, in the shipout-time state | inside for the job's own files. The deferred expansion is checked by the page-safety obligation (§3.3), over the abstract shipout state. `\openout` to any other name, and `\write18`: `Stuck` |
| **capacities** (C-86, C-94, C-98; the brief also names C-100, which on record is the format's byte-reproducibility, not a capacity) | the engine's own counters (`cur_level`, `save_ptr`, `input_ptr`, `max_param_stack`, `dyn_used`, `var_used`, `pool_ptr`, `str_ptr`, `hash_used`, `fmem_ptr`, `expand_depth_count`, …) are ordinary globals; `exec#` tracks each as an interval and records its peak | inside, by §3.5. One counter is not translation-invariant (main memory's variable-size region, through fragmentation) and needs its own lemma (AI-5) |
| **the output routine** | fires inside segments (§2.4) | inside only under the configuration's page-safety obligation; initially floats and marks beyond the kernel's own are `Stuck` (§3.3) |
| **`\scantokens`, `\read`, `\input` in the body, `\pdfstrcmp` of runtime text, `\pdfelapsedtime`** | re-tokenization or external input | `Stuck` in the first version. `\input` of a sibling file can later be a segment sequence of its own |

**Is the theorem plausible?** Yes, because it is weak where it has to be: it decides only bodies
in which every segment has a summary. The open question is not the theorem but the **coverage**.
That is, whether the domains of §3 let `summarize` return `Some` for the commands real papers
use, at a precondition general enough to be reused (§4). The trace of §7 is the first evidence on
that, and it is mixed. Nothing in `\emph` is beyond the domain. But almost every row above occurs
in the code `\emph` executes on its first use, or in code it can reach (an `.fd` load runs
`\nfss@catcodes` and `\InputIfFileExists`; a font warning runs `\GenericWarning`'s `\write`).

## 3. Question 2: the abstract domain(s)

### 3.1 The shape: concrete by default, abstract by region

The concrete state is `PS`'s store: about 690 globals and heap blocks (`mem`, `eqtb`, `hash`,
`str_pool`, `save_stack`, `input_stack`, `nest`, `font_info`, `trie`, pdfTeX's tables), plus the
I/O record [R: H2 report, `Values.v`].

Almost all of it is **identical at every use** of a command within one configuration: the format,
the packages' definitions, the font tables. What varies between uses is a small set of regions:
- the arguments and the continuation;
- the mode and the semantic nest;
- the group level and the save stack;
- the current font and the size variables;
- the counters' values;
- the contribution list and the page;
- `\lastskip`/`\lastpenalty`/`\lastnodetype`;
- the flags LaTeX keeps as macros (`\if@nobreak`, `\if@endpe`, …);
- definitions the body made (`\newcommand`, `\label` data read from the `.aux`);
- the allocator's free lists and the hash table's occupancy.

So the abstract store `A` is **the concrete store with abstract cells in designated places**,
not a separate model of TeX. Every operation of `exec#` is `exec`'s operation, applied to cells
that may be abstract:

| cell kind | abstract values | notes |
|---|---|---|
| integer (`KInt`) | `Exact z` · `Range lo hi` · `Sym x` (an unknown but fixed value, with an optional range) · `Top` | arithmetic on ranges is interval arithmetic; anything that may overflow its C type is `Stuck(overflow)` as in `exec` (E1) |
| pointer (`KPtr`) | `Exact (b,o)` · `Fresh n` (the n-th block this summary allocated) · `Sym p` (a pointer the precondition supplies, e.g. the argument's token list) | `Fresh`/`Sym` exist **only** under the allocator abstraction of §4.3 |
| union word (`KWord`) | bytes, each `Exact` or `Top`, with the existing defined-byte mask | a field read through an accessor that touches a `Top` byte yields `Top` |
| double (`KDbl`) | `Exact` · `Top` | `glue_ratio` only. It reaches TeX state only through `\pdfsavepos`, so `Top` is harmless unless branched on |
| a token list given by the document (an argument) | `Arg i` with its **length** as a `Sym` and a set of **shape predicates** the kernel will check (empty, a space, contains `\nocorr` at depth 0, its first token's class, …) | the run never expands `Arg i`: reaching it on the input stack ends the current transformer at a **hole** |
| a node list (the contribution list, a box being built, the page) | **opaque**, with observers: the kind of the last node, the sign class of a last glue or penalty, the number of words it holds as a `Range`, and its natural height/depth/width as `Range`s | see §3.3 |
| the continuation | `τ` (the peeked tokens, concrete) followed by `Next` (a symbolic token) | a read of `Next` forks on what the code compares it with (§2.5) |

### 3.2 Joins, widening and forks

- **Fork** at a branch whose condition is not decided by the abstract values. A path set is kept,
  bounded by `K` live paths (default 64, as in ADR-014 §5.2), and `Stuck(fork)` past it.
- **Join** where two paths reach the same program point (the same procedure, statement and
  call stack) with stores that differ only in abstract cells:
  - the join is pointwise: `Exact a ⊔ Exact b = Range`, and a pointer join that is not equal
    is `Top`;
  - control state never joins. Two paths with different call stacks or different input-stack
    shapes stay separate, because a join there would lose the boundary property.
- **Widening** is needed only for loops whose trip count depends on an abstract value. In TeX
  those are of two kinds:
  - loops over an argument's tokens (`\@tfor`, delimited-parameter matching, `\edef` of an
    argument): the argument is a hole or a shape predicate, so no loop runs over its abstract
    contents;
  - loops over runtime data (`\loop` on a counter, l3 `\int_step`): standard interval widening
    at the loop head, after 3 iterations, to `Range lo +∞`, then **`Stuck(widening)` if the
    widened state reaches an error site or a capacity check**. Termination is the fuel's job
    (`StFuel`). An abstract run that would need a widened value at an `\ifcase` or an array
    index is `Stuck` rather than imprecise.
- The domain is a **disjunctive** completion with a bound, not a lattice of convex sets. That is
  deliberate: TeX code branches on small finite things (mode, group type, a catcode, a flag),
  and a disjunction over K of them is exact where a convex join would be useless.

### 3.3 The page, and why layout must be abstracted here

ADR-014 §5.1 made layout exact *because the whole document was executed*. A summary cannot keep
layout exact, because the same `\emph` occurs at different points of different pages.

- Node lists are **opaque** with observers (the table above). A summary that reads a node list's
  content other than through those observers is `Stuck(layout)`. `\emph` itself reads only
  `\lastskip`, `\lastpenalty` and `\fontdimen1` (§7).
- Dimensions are `Range`s. Overfull and underfull boxes are warnings (rc 0) and do not matter. A
  fatal layout error ("Dimension too large", "Infinite glue shrinkage found in a paragraph",
  "Huge page cannot be shipped out") is reachable only through arithmetic or glue-order checks
  that the ranges must decide, else `Stuck(layout)`.
- **Page safety** is an obligation **per configuration**, proved by `exec#` once:
  - run `build_page`, `fire_up` and the configuration's real output routine (LaTeX's
    `\@outputpage`, the class's and packages' patches) from the abstract page state `π#`;
  - that run must end with no error, and with the abstract state outside the page regions
    unchanged up to a stated `Post_out`;
  - every non-immediate `\write` whatsit that the summaries can put on a page is part of `π#`,
    so its shipout-time expansion is run in that same abstract run.

  Then every segment summary may treat "the output routine fires here" as a transformer it
  already knows. **The first version admits no floats, no `\mark`s beyond the kernel's own, no
  `\vsplit` and no inserts other than footnotes**: those are `Stuck(page)`. This is a coverage
  limit, measured in AI-6, not a soundness hole.
- `\pdfsavepos` positions are `Top` (ADR-014 §5.1's ±k sp mitigation is subsumed).

### 3.4 What makes an abstract run `Stuck` (outside the tier)

Everything that makes `exec` `Stuck` (E1: undefined behaviour, an unmodelled external, fuel), and
in addition:
- a branch, array index, `\ifcase` or `id_lookup` on a value the domain cannot narrow to ≤ K
  cases;
- an expanding read of the continuation, beyond a two-segment window;
- a read of an `Arg` other than as a hole or a declared shape predicate (for example `\meaning`
  of an argument token, or `\uppercase` of it);
- a non-exact catcode at a boundary;
- the output routine outside the page-safety obligation;
- a capacity whose peak the domain cannot bound below its limit;
- a pointer join that is `Top` and then dereferenced;
- any read through the allocator or the hash table while their abstraction (§4.3) is not
  established for this run.

Every `Stuck` carries its reason and the procedure stack, like `exec`'s
(`stuck: 600 > 593 > 560 > 558 > 247 > unmodelled external: bopenin` in §7).

### 3.5 Capacities, soundly and at the worst case (the C-94/C-98 lesson)

The lesson on record is two-fold:
- C-94: bound the real limit, never a proxy;
- C-98: bound it at the worst case, because nested arguments **copy** their arguments, so memory
  grows like depth × tokens.

Both failures came from capacities modelled *beside* the semantics, with coefficients measured
by probes. Here a capacity is the engine's own counter, so:

1. **Every capacity is a global that the translated program checks** before `overflow`.
   ADR-014's table counts 37 `overflow` call sites [R]; they are enumerable from the IR, which is
   AI-5's first deliverable. Examples: `cur_level` against `max_quarterword` (grouping levels,
   C-94), `save_ptr` against `save_size`, `input_ptr` against `stack_size`, `param_ptr` against
   `param_size`, `dyn_used` and `var_used` against main memory (C-98), `pool_ptr`, `str_ptr`,
   `hash_used`, `fmem_ptr` (font memory, which `\emph` grows on its first use, §7).
2. In a summary's abstract run, each counter `v` **enters as `Sym v₀`**: an unknown entry value.
   The run is allowed to use `v₀` only:
   - by adding constants to it;
   - in the overflow comparison. That comparison is discharged by the side condition
     `v₀ + peak_v ≤ limit_v`, which the kernel checks at fold time on its (exact or upper-bound)
     value of `v`.

   Any other use of `v₀` (a branch on `cur_level`'s value, say) makes the summary non-invariant,
   and it is `Stuck(capacity)`. This is a **check**, not an assumption: it is what makes `Δ`
   independent of where the segment occurs.
3. **Argument copies** (C-98's channel):
   - `macro_call` stores an argument as a fresh token list, so `dyn_used` grows by the argument's
     length at every nesting level;
   - the hole's own segments run on top of that, and the kernel adds their `peak` at the hole's
     entry value;
   - so the fold computes `peak = entry + max over the run of the running sum`, along the actual
     nesting tree of the document.

   That is C-94's `Decide.peak` construction, with every coefficient now **derived from the
   engine's code** rather than measured by a maximiser.

   **What this needs, and does not yet have:** the scan of an argument whose length is symbolic
   is a loop with a symbolic trip count. Getting `Δdyn_used = n` from it, exactly, takes one of:
   - a relational numeric component, namely affine equalities between a loop counter and the
     capacity counters (Karr's domain [U: standard]);
   - or a lemma about `macro_call`'s scanner proved once on the translated code.

   Either is part of AI-1's scope.
4. **Main memory's variable-size region is the exception.** `get_node` (tex.web §125) is first
   fit over a rover list. Whether a request succeeds depends on fragmentation, not only on
   `var_used`, so `lo_mem_max`'s peak is not translation-invariant. A sound account needs a
   **fragmentation lemma**: `lo_mem_max` is bounded by a function of `var_used`'s peak and of the
   finitely many node sizes TeX allocates. That lemma is AI-5's.
   - Its margin is large for real bodies. The format state uses 435,796 of 5,000,000 words
     [M: the model's own `memory used` statistics in format state,
     `ai/evidence/model/model1/model-stdout.txt`], and a
     page's live material is small against that [I].
   - At the **worst case** the margin is whatever the lemma proves. A document past the proved
     bound is outside the tier, never READY.
5. The kernel's fold carries the exact value of each counter where it can (`cur_level`,
   `save_ptr` above the body-start value) and an upper bound otherwise. The gate recomputes every
   bound from the summaries' primary `Δ` (the C-98 rule: never from a number stored beside them).

## 4. Question 3: the summary key

### 4.1 The key: the read set, observed by the abstract run itself

`exec#` records, on every explored path, every cell it **reads**: a (block, offset) pair and the
abstract value it saw there. Everything in `PS` reads through `read_loc`/`cell_at` (`Interp.v`),
so this is one instrumentation point. The summary is then stored under the key

```
key(Σ) = (segment kind, guards, canonical form of { (location, abstract value read) })
```

**Reuse rule.** A cached `Σ` applies at a use with abstract state `a` iff `a` agrees with the key
at every recorded location (equal `Exact` values; containment for `Range`/`Sym`).

**Why reuse is sound: the frame lemma, proved once for `PS`.**

```
Lemma readset_frame : forall fuel st1 st2 r1 R,
  exec_traced fuel st1 = (r1, R) ->               (* R: the locations read, in order *)
  agree_on R st1 st2 ->
  exists r2, exec fuel st2 = r2 /\ same_result_up_to_unread r1 r2 R.
```

Its proof is the usual "first divergence" induction on the fuelled interpreter. The two runs read
the same values, so they take the same path. They write the same values. They differ only in
cells neither run read, and those cells keep their old, differing values. The read set is
**adaptive**: what is read depends on earlier reads. That is fine, because the lemma follows one
path.

The abstract version (`exec#`, path sets, abstract values) follows from `abstract_sound` and
this lemma. So:
- **reuse adds no premise**;
- `Post` needs to state only the cells the run **wrote**; every other cell is unchanged by the
  same lemma. That is why "what a use leaves behind" (C-90) cannot be omitted from a summary
  (§2.5).

### 4.2 Why ADR-013's footprint premise P-1 broke, and why this key does not have it

ADR-013 keyed reuse by a **footprint** computed by a *static analyser of TeX macro text*. Its I1
and I2 instruments walked a name's `\meaning` closure and classified every read (§2.7 and §4.3
of that draft). Its soundness premise P-1 was "the censuses are complete". That premise was
broken twice, after publication, in the instrument that the footprint rested on:
- **C-92:** the closure never followed LaTeX's robust wrappers. The inner command is the name
  `"X "` (with a trailing space), which the walker's regex could not spell. So for every robust
  command it screened only `\protect \X␣␣`.
- **C-96:** the closure never entered expl3 code (`\hook_use:nnw` read as `\hook`, "undefined",
  and the walk stopped *silently*), and it read `\protected\long macro:` as not a macro.

The cause is **structural, not two bugs**. The analyser reconstructed a program's dependencies
from a *printed rendering* of TeX code, with its own lexer. That rendering is not a faithful
syntax:
- `\meaning` text depends on catcodes and on `\escapechar`;
- names built by `\csname` do not appear in it at all;
- active characters and runtime-built expl3 variants do not appear either.

And P-1 had to be complete in the direction of *never missing a read*, which is a property of the
analyser, an extra trusted program.

This key differs at each of those points:

| ADR-013 footprint | this key |
|---|---|
| reads inferred from `\meaning` text, by regex | reads **observed** at `read_loc`, the only way `exec` can depend on a cell |
| over the TeX-level closure; `\csname`-built names invisible | at the memory-cell level; a `\csname` lookup reads the hash cells it probes and the `eqtb` entry it finds, whatever the name |
| a walk that can *end* on an unreadable name (C-96: silently) | an abstract run that cannot classify something is `Stuck`; there is no "end of walk" |
| completeness of the analyser is a premise (P-1) | the frame lemma is a **theorem about `PS`** (§4.1), and the run is the engine's own code under `abstract_sound` |
| one representative probe per cell (P-4) | no probes; arguments are holes or shape predicates checked by the kernel |

The remaining premise is the old one: `FaithfulEngine`. Its attestation is the H.4/H.6
co-simulation.

### 4.3 The deciding unknown: addresses and hash slots

A key at the level of **concrete locations** is sound, but it almost never matches. Two reasons:

1. **Allocation.** Typesetting `x` takes a char node from `avail` (`get_avail`, tex.web §120); a
   kern takes a node from the rover list (`get_node`, §125). The read set therefore contains the
   `avail` head and the rover's free-list cells. Their values differ at every position of every
   document. With a location-exact key, two uses of `\emph` in **the same paper** have different
   keys.
2. **The hash table.** `id_lookup` (§259) probes a chain whose cells depend on **every name** in
   the table. Two configurations with the same `\emph` code but different packages read
   different hash cells, so their keys differ.

So any reuse beyond an identical state needs `exec#` to treat both **abstractly**:
- the allocator returns `Fresh n` (a block disjoint from everything live);
- `id_lookup` returns "the location of name *s*", or "a new location", as a function of the
  *name*, not of the probe sequence.

Using those abstractions soundly requires refinement lemmas for the **translated** `get_avail`,
`get_node`, `free_node`, `flush_list`, `id_lookup` and `make_string`. Each holds only under a
**heap invariant** `I_heap`:
- the free lists are disjoint from every reachable structure;
- reference counts (TeX shares token lists and glue specifications by count, tex.web §200–§203)
  are right;
- the hash chains are well formed.

There are three ways to establish `I_heap`, in increasing order of reuse:

- **K1. Location-exact key, no abstraction.** Sound today, given the frame lemma. Reuse is ≈ 0,
  so every keystroke that changes a position re-runs `exec#`: the synthesis is then *slower* than
  running the concrete model on the document. **Not viable for D1.**
- **K2. A whole-program invariant.** Prove that every one of the 603 procedures preserves
  `I_heap`. ADR-014 §4.4 put such invariants ("no index leaves its bounds") down as research.
  This one is of that kind, over pointer-level code with reference counting.
  **Not proposed.**
- **K3. Checked, then preserved locally (proposed).**
  - `I_heap` is **decided** on the concrete body-start state by a Coq-verified checker. That is
    a computation over one store, and it can be checked on the 20 configurations of AI-2.
  - Each summary's abstract run must **preserve** `I_heap` *for the cells it touches*: it frees
    only nodes it owns or that the precondition gives it, and allocates only through the
    abstracted allocator. The checks are made during the run, with a separation-style footprint.
    A run that cannot show preservation is `Stuck(heap)`.
  - The composition theorem then carries `I_heap` along the fold as an invariant.

  This is shape analysis per summary, not a whole-program proof, and it is the **largest and
  riskiest item of the whole plan** (AI-2).

If AI-2 fails, the key falls back to K1, and §6's cost model shows that the static path then does
not beat running the model. That is why AI-2 carries the architecture's kill criterion (§8).

### 4.4 Cache integrity

`static_decider_exact` needs every cached summary to be sound. Summaries produced by the
extracted `summarize` are sound by `summarize_sound`. Whether the stored bytes **are** such
outputs is a property of storage, not of logic. Two choices, put to the owner with AI-6:
- **(a)** content-addressed storage written only by the pinned `summarize` binary. This is a new
  trusted-base row, of the same class as the extraction trust (H2 report, trusted base);
- **(b)** re-checking at load by a verified checker of a summary's certificate: the abstract
  post-fixpoint, re-validated by one pass of the transfer functions. It costs about one abstract
  run without the fixpoint iterations [I].

### 4.5 The hit rate on the real corpus (estimate)

Measured on sample 2 (ranks 201–400; 200 papers; every `.tex` of each paper, comments stripped
per line; regex instrument `ai/tools/census.py`; output `ai/evidence/census/sample2-census.txt`)
[M, crude]:
- **334 distinct packages**. The most loaded are amsmath (172), amssymb (156), graphicx (156),
  hyperref (145), amsthm and xcolor (104 each) and amsfonts (100). **139 packages are loaded by
  exactly one paper.**
- **200 distinct (class, package set)** of 200, as recorded (STRICT_TIER_DESIGN §B.1).
- **42 papers ship a `.cls`** (the record says 41; the instruments differ, and this one counts
  any `.cls` file in the tree). 50 ship a `.sty`. Of the 76 distinct vendored files, 15 are shared
  by more than one paper (conference styles).
- A **coarse `\emph`-relevant signature**: the class, or a vendored class's content hash; the
  subset of 39 font, encoding and emphasis packages loaded; the content hashes of the vendored
  files. It gives **101 distinct signatures**. **99 of 200 papers share a signature with an
  earlier paper.**

What this supports [I]:
- **For a kernel command whose read set touches only font and NFSS state (`\emph`)**, a warm cache
  serves *at most* about half of new papers. The bound is an upper one: the real read set is
  finer than the signature. It includes the `selectfont` hook's contents, which any package may
  extend; `\everypar`, through LaTeX's paragraph hooks; and `\nocorrlist`.
- **For commands that read class code** (`\section` through `\@startsection`'s parameters,
  `\maketitle`, list environments), every paper with a vendored class (≈ 1 in 5) is a miss. So
  are most papers whose class is rare.
- **For commands hyperref patches** (`\label`, `\ref`, `\section`, `\footnote`), the key includes
  hyperref's code and its option-dependent state. Reuse happens only among papers with the same
  hyperref configuration.
- **Math symbols** read `\mathcode`, the families and the math fonts' parameters, and should hit
  across most configurations that do not change math fonts [I].
- `Sym` values help. A summary that only moves a value into a node (for example `\parindent`'s
  width into the indent box) keeps it symbolic, and the value then stays out of the key. Only
  values that decide control flow enter it.

**The measurement that settles the hit rate is AI-6's.** Count the fraction of a new paper's
segment occurrences served by summaries computed for *other* papers, on sample 2 after sample 1.
It needs the real read sets, so it cannot be done before AI-3.

## 5. Question 4: the body-start state

The fold needs `a₀ ⊒` the concrete state at body start, and in fact needs it *before* the
`.aux` is read (§2.4). ADR-015 never says how this state is obtained (re-audit premise 10b). There
are two candidates.

### 5.1 M: a model run of the preamble (engine-free)

Run `exec` on the preamble, from the format load to the checkpoint before `\begin{document}`
reads the `.aux`. Marshal the store once per (preamble bytes, files read, environment class),
as ADR-014 §7.2 proposed.

- **Cost** [I, from measured rates]. The pinned pdfTeX takes 0.2–2.3 s for a real configuration's
  trace run (ADR-013 draft B.3 [R]); about 0.11 s of that is the format load [I: 35 s / 315×].
  At the B2 build's rates:
  - **≈ 315×**, the format-load rate: ≈ 1–12 minutes per configuration;
  - **≈ 11,700×**, the whole-dump rate, which is dominated by per-name work and so is closer to
    package loading: ≈ 40 minutes to 7.5 hours.

  Which rate applies to package code is unmeasured. The format load alone costs **35 s CPU** on
  record [R]. This branch measured **66–74 s user CPU** for the load plus a few lines, at load
  averages 16–25, so not a speed measurement (`model-time.txt` files under
  `ai/evidence/model/`) [M].
- **Prerequisites:** the C boundary for everything a preamble does. That means kpathsea file
  lookup and `\input` of `.cls`/`.sty`/`.cfg`/`.def`/`.fd` files, TFM loading, `\openin`, the
  `.aux` write, and PDF-side state that packages set up (hyperref's `\pdfcatalog` entries,
  `\pdfobj`). None is modelled today (§1).
- **What it gives for free:** preamble failures are decided exactly as **PROVEN-NOT-READY**
  (ADR-014 §8.1's "preamble failures are decided"). `γ(a₀)` contains the real state **by
  theorem**: the store *is* the run's state. No new premise.
- **Its price is the first verdict on a new configuration**: minutes to hours of CPU before any
  PROVEN verdict, during which the verdict is `PENDING`. Preamble edits are rare compared with
  body edits [I], so the cost is paid per configuration, not per keystroke.

### 5.2 O1.2: a snapshot made by running TeX on the preamble

Two forms:

| form | what runs | equivalence to the real run | trust it adds |
|---|---|---|---|
| **(a)** a format dumped after the preamble (`pdftex -ini`, `&pdflatex`, the preamble, `\dump`, in the style of `mylatexformat`), loaded by the model through the H.3-proven `load_fmt_file` path | the pinned binary, in INITEX mode | **not the same run**. `\dump` keeps `eqtb`, `mem`, the hash, strings, fonts and the trie. It does not keep the open `\write` streams, the `\read` streams, the input stack (the main file's level), `\inputlineno`, the job name, interaction, pdfTeX's object tables, or what is queued for `\AtBeginDocument` *as code that runs later*. ADR-013 (§4.2) recorded the same objection and allowed such a format "for triage only" | a per-configuration **equivalence premise**: the body cannot observe the difference. It is checkable only by comparing against a model run of the same preamble, which is M's cost |
| **(b)** a full-state snapshot from an instrumented **reference build**: the H.1 rebuild of r78081 with a change file that dumps every translated global at the checkpoint, as H.6's digest change file already proposes for co-simulation | a binary that is **not** the pinned one (same source plus a change file) | exact, *if* the instrumented build equals the pinned binary on the run up to the checkpoint. H.6's step-by-step co-simulation attests exactly that | `FaithfulEngine` extended to the instrumented build (attested, as for H.6); and a TeX engine runs on part of the document |

Trade-offs, for the owner:
- **Engine-free (D1's wording).** M satisfies it. O1.2 does not: a TeX engine runs on the
  document's preamble, on some machine. If that machine is a server, the user's machine still
  needs no TeX. But the preamble, including any private `.cls`, then leaves the user's machine.
- **Latency of the first verdict on a new configuration:** M takes minutes to hours of model CPU
  [I]; O1.2(b) takes about the pinned binary's preamble time (0.2–2.3 s) plus loading the snapshot.
- **Trusted base:** M adds nothing. O1.2(a) adds an equivalence premise per configuration that
  cannot be checked cheaply. O1.2(b) adds the instrumented build to `FaithfulEngine`'s scope.
- **Recommendation.** **M as the default**, because it is exact and adds no premise. **O1.2(b),
  not (a), if** the owner rules that "engine-free" means "no engine on the user's machine" and
  minutes-to-hours first-verdict latency is unacceptable. O1.2(a) is not recommended: its
  equivalence premise is exactly the kind of unattested composition claim that C-90 recorded.

## 6. Question 5: the cost

### 6.1 What `exec#` runs on

- `exec#` interprets **the same translated AST** (`prog`, 603 procedures) over the same store
  layout. Its abstract values are `exec`'s values with abstract alternatives (§3.1). That much
  ADR-014 §2.2 specified [R].
- It does **not** run on a "closure compiler": none was built. H.2 extracts the fuelled big-step
  interpreter itself (`Extract.v`) [R]. `exec#` would be a second extracted fuelled
  interpreter, with the same realizers (zarith, `Parray`, coq-core's primitive integers and
  floats) and no new trusted-base row.
- **The fast-interpreter fallback (E13) would not speed up `exec#` by itself** [I]. A verified fast
  interpreter or compiler for `exec` is a refinement proof about *concrete* values. Abstract
  interpretation needs either its own fast version, or a fast evaluator **generic over the value
  domain**: a closure compiler parameterised by a value module, proved equal to `exec` and to
  `exec#` by one argument. If the fallback is ever funded, its design should be the generic one;
  this is a requirement this scoping adds to it.

### 6.2 Per explored path: `exec#` against `exec` [I]

Each factor's basis is stated; none is measured, because nothing exists to measure (AI-1 measures
it).

| factor | basis | range |
|---|---|---|
| abstract values: a tag test per operand, interval arithmetic where not `Exact` | most cells stay `Exact`, so the fast path is a tag test | 1.5–3× |
| read-set recording: one insert into a persistent map per `read_loc` | reads dominate interpretation, and H.5 measured persistent-array work at 2 % of the CPU, so the map insert is a new cost of the same order as the read itself | 2–4× |
| path management: join checks at merge points, store comparison on touched cells | per merge, proportional to the cells written since the fork | 1.2–2× |
| **product** | | **≈ 5–20×** (range 3.6–24×) |

The concrete model is itself ≈ 315× (format load) to ≈ 11,700× (whole meaning dump) pdfTeX on the
B2 build [R]. Taking ≈ 1.2 µs per expansion for pdfTeX (0.4 s for ≈ 335k expansions, ADR-014 §7.1
[R]), `\emph`'s first use (≈ 66 macro expansions, 55 assignments, 28 conditionals and a font load,
§7) is of the order of 0.1–1 ms in pdfTeX [I]. One explored path of `exec#` therefore takes
≈ 0.2 s to 4 min [I: 0.1 ms × 315 × 5 = 0.16 s, up to 1 ms × 11,700 × 20 = 234 s]. The width of that range is
the honest state of knowledge.

Measured here: the model's whole run of `\emph{x}` in format state, up to the `Stuck` at the TFM
open, used **73.1 s user CPU**, against **73.6 s** for a control run that does only the format
load and one `\font` command up to the same `Stuck` (load average 16–25) [M:
`ai/evidence/model/{model3,model0}/model-time.txt`]. So a single command's code is **below the
run-to-run noise** of a run dominated by the format load. Two consequences:
- **every summary computation must start from a marshalled snapshot**, never from a format load;
  that snapshot is not built (§1);
- the per-command figure has to be measured from a snapshot (AI-1, AI-3).

### 6.3 Per summary, per paper, per keystroke [I]

- **Cases per summary.** `\emph`'s guards cross several things:
  - the mode (vertical, horizontal, math);
  - the follower class (`,`/`.` or other);
  - first use or not (the font is loaded or not);
  - the argument's shape (empty, a space, plain, `\nocorr` at either end).

  Not all combinations are distinct (in math mode the follower does not matter), so the estimate
  is **≈ 20–50 cases**, near the bound K = 64.
- **A summary costs** ≈ 20–50 × one path's cost: ≈ 3 s to ≈ 3 h. The central estimate is
  a few minutes (the geometric middle of the path range, ≈ 6 s, times ≈ 35 cases) [I].
- **A cold paper** has a median of 75 distinct control words and 12 environments in its body
  (ADR-013 draft §4.2 [R]). Each may need 2–4 distinct preconditions (contexts), so ≈ 200–350
  summaries, about **12–20 CPU-hours** at the central estimate (the full range runs from
  minutes to ≈ 1,000 hours), plus the preamble run of §5.1.
  Warm-cache hits divide this by up to 2 for font-level commands (§4.5) and less for class- and
  hyperref-dependent ones.
- **A keystroke with every summary cached** re-folds from the edit point:
  - per segment, one key lookup, and an agreement check over the read set, which is O(|R|) with
    |R| in the hundreds to thousands of cells;
  - in total, milliseconds to tens of milliseconds for a 40-page paper [I].

  So **real time is plausible on a hit, and impossible on a miss**: a miss means `PENDING` for
  minutes to hours.

For comparison: running the concrete model on the whole document (ADR-014's product, which D1
rejects for the keystroke path) costs ≈ 315–11,700 × pdfTeX's 0.4 s per pass of the 12-page
paper, i.e. ≈ 2 min to 1.3 h per pass [I], and needs no summaries. **The synthesis pays off only
if the warm-cache hit rate is high.** That is why AI-6's kill criterion is a hit rate and a cold
cost, fixed now (§8).

## 7. Question 6: one real command end to end — `\emph` from `latex.ltx`

### 7.1 Why `\emph`, and how it was traced

- **Why `\emph`.** It is in the kernel, so no package file is needed. It is ubiquitous. And it
  covers everything the brief asked for: expansion (a robust wrapper and a chain of
  `\expandafter`), assignments (local and **global**), a group, plus `\aftergroup`,
  `\futurelet`, `\csname`, conditionals on runtime state, a configuration hook, and a capacity
  that grows (font memory). `\section` would add the page and the `.aux`, which §2.4 covers but
  which the model cannot reach yet. `\url` needs a package file the model cannot read yet.
- **Meanings** come from the pinned image in format state (`pdftex -ini`, `&pdflatex`), by the
  H.3 README's binary-side meaning-dump recipe with `ai/tools/closure.py`'s input. H.3 showed the
  model's dump of all 23,519 kernel names IDENTICAL to the binary's on the B2 build (digest
  `4879fa65…`, H3 report) [R], so these meanings are the model's too. Recipe (documentation; it
  starts the engine outside `_oracle.py`, as the H.3 README's recipes do):

  ```zsh
  IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
  python3 ai/tools/closure.py start st.json 'emph,emph '          # writes ./in.tex
  docker run --rm -i --platform linux/arm64 --network none -e SOURCE_DATE_EPOCH=0 \
    -e FORCE_SOURCE_DATE=1 -e max_print_line=1000000 -e error_line=254 -e half_error_line=238 \
    $IMG pdftex -ini < in.tex > out.txt
  python3 ai/tools/closure.py absorb st.json out.txt              # repeat until nothing pending
  ```
- **The first use at body start** was traced in the pinned image with `\documentclass{article}`,
  `\begin{document}`, full tracing, then `A \emph{x} y.`, and tracing off for a second
  `\emph{z} w.` (`ai/evidence/bodystart/d.tex`, `d.log`; the slice for the first `\emph`:
  `emph-first-use-trace.txt`). Run: `pdflatex -interaction=nonstopmode -halt-on-error d.tex` in
  the same image, rc 0 [M].
- **The model run** used the B2 model build `ps.exe` `cae7a953…`, the build H.3's meanings
  clause was met on [R]. It ran under `h3/tools/capped.sh` with a 4,000 MB cap and a 1,800 s
  timeout (peak 1,523 MB) [M]. Its run identity is the H.5 meaning-dump spec
  (`ai/evidence/model/model3/spec`; the decompressed format's path is a placeholder). Its
  terminal input (`stdin`) is `&pdflatex`, then `\scrollmode`, tracing on,
  `\setbox0\hbox{\emph{x} y}`, `\showbox0`, and a second box with `\emph{z}.`. The pinned
  binary was run on the same input, with the same environment
  (`ai/evidence/model/model3/binary-terminal.txt`).
  The format state is not the body-start state: there `\OT1/cmr/m/n/10` is `\relax` and the
  current font is `\nullfont`. That is why the model run uses an `\hbox`, where a missing
  character costs nothing that could stop the model before `\emph`.

### 7.2 The definition, as pdfTeX holds it [M: `ai/evidence/closure/emph-closure-meanings.json`]

```
\emph   = macro:->\protect \emph␣␣
\emph␣  = \long macro:#1->\ifmmode \nfss@text {\em #1}\else \hmode@bgroup \text@command {#1}\em
          \check@icl #1\check@icr \expandafter \egroup \fi
\em␣    = macro:->\@nomath \em \ifx \emfontdeclare@clist \@empty \ifdim \fontdimen \@ne \font >\z@
          \eminnershape \else \itshape \fi \else \edef \em@currfont {…}\expandafter
          \do@emfont@update \emfontdeclare@clist \do@emfont@update \fi
\itshape␣ = macro:->\not@math@alphabet \itshape \mathit \fontshape \itdefault \selectfont
\text@command = macro:#1->\edef \reserved@a {\unexpanded {#1}}\ifx \reserved@a \@empty … \else
          \ifx \reserved@a \space … \else \check@nocorr@ #1\nocorr \@nil \fi \fi
\check@nocorr@ = macro:#1#2\nocorr #3\@nil ->\let \check@icl \maybe@ic \def \check@icr {\ifvmode
          \else \aftergroup \maybe@ic \fi }…
\maybe@ic = macro:->\futurelet \@let@token \maybe@ic@
\maybe@ic@ = macro:->\ifdim \fontdimen \@ne \font >\z@ \else \maybe@ictrue \expandafter \@tfor
          \expandafter \reserved@a \expandafter :\expandafter =\nocorrlist \do \t@st@ic
          \ifmaybe@ic \sw@slant \fi \fi
\sw@slant = macro:->\ifdim \lastskip =\z@ \fix@penalty \else \skip@ \lastskip \unskip \fix@penalty
          \hskip \skip@ \fi
\selectfont␣ = macro:->… \xdef \font@name {\csname \curr@fontshape /\f@size \endcsname }
          \pickup@font \font@name \UseHook {selectfont}\size@update \enc@update
\pickup@font = macro:->\expandafter \ifx \font@name \relax \define@newfont \fi
\nocorrlist = macro:->,.
```

A regex walk of the names these texts mention, to a depth of 12 rounds, reaches **726 names**
(277 `macro`, 109 `\long macro`, 80 `\protected\long macro`, 6 `\protected macro`, 214
primitives or other meanings, 40 undefined) [M]. The walk follows error paths (`\@latex@error`,
`\GenericError`), the hook machinery (`\hook_use:n`) and the paragraph hooks. It is a screen, not
a closure: it cannot see `\csname`-built names. That is the weakness C-92 and C-96 recorded, and
the reason §4.2 refuses to key anything on such a walk. **What the abstract run needs is not this
set but what the engine reads**, and the next subsection is that.

### 7.3 What the first use executes at body start [M: `emph-first-use-trace.txt`]

The first `\emph{x}` after `A ` in `article`'s body produces 850 trace lines:
- 66 macro expansions;
- 55 assignments, 3 of them **global**:
  - `\font@name`, by `\xdef`;
  - `\OT1/cmr/m/it/10` twice: first `\relax` by `\csname`, then `\font` by `\global\font`;
- 28 conditionals;
- 3 groups entered: the simple group of `\hmode@bgroup`, and two semi-simple groups inside
  `\maybe@load@fontshape` and `\define@newfont`;
- 3 `\futurelet`s and 1 `\aftergroup`. One `\futurelet` is inside `\define@newfont`, where
  `\escapechar` is −1, so the trace prints it without its backslash.

In order:
1. `\protect\emph␣␣` → `\emph␣`, which reads `#1 = x`. `\ifmmode` is false. **A runtime
   conditional, on the mode.**
2. `\hmode@bgroup` = `\leavevmode\bgroup`: horizontal mode already, so a **simple group** is
   opened (level 1).
3. `\text@command{x}`:
   - `\edef\reserved@a{\unexpanded{x}}`;
   - two `\ifx` tests on the **argument's shape** (empty? a space?);
   - `\check@nocorr@ x\nocorr \@nil`, a **delimited-parameter split** of the argument at
     `\nocorr`;
   - it sets `\check@icl := \maybe@ic` and `\check@icr := {\ifvmode\else\aftergroup\maybe@ic\fi}`.
4. `\em␣`:
   - `\ifx\emfontdeclare@clist\@empty` is true;
   - `\ifdim\fontdimen\@ne\font>\z@` is false (cmr10 is upright): **a branch on a parameter of the
     current font**;
   - so `\itshape` → `\fontshape{it}` → `\selectfont`.
5. `\selectfont`:
   - `\maybe@load@fontshape` (a semi-simple group; `OT1+cmr` is defined, so no `.fd` file is
     read);
   - `\ifcsname OT1/cmr/m/it\endcsname`;
   - `\xdef\font@name{\csname OT1/cmr/m/it/10\endcsname}`: **global**, and the `\csname` creates
     the name as `\relax`;
   - `\pickup@font` finds `\relax`, so `\define@newfont` (a semi-simple group) scans the size
     table `<5><6><7>cmti7…<10><10.95>cmti10…`. That is an `\@ifnextchar` loop (`\futurelet`
     inside the font machinery) and `\extract@font`;
   - `\global\font\OT1/cmr/m/it/10 = cmti10 at10.0pt`: **a font load**. pdfTeX's `new_font`
     reads `cmti10.tfm`. It is a **first-use** effect: the second `\emph{z}` finds the font
     defined and loads nothing [R: `\pickup@font`'s `\ifx`];
   - the font is selected; `\UseHook{selectfont}` runs (**the hook's contents are
     configuration data**); `\size@update` and `\enc@update` are `\relax`.
6. `\check@icl` = `\futurelet\@let@token\maybe@ic@`. It **peeks at the argument's first token**
   `x`, then `\ifdim\fontdimen1\font>\z@` is true for cmti10, so nothing is inserted. Then `x` is
   typeset in cmti10.
7. `\check@icr`: `\ifvmode` is false, so `\aftergroup\maybe@ic` puts a token on the save stack.
   `\expandafter\egroup\fi` closes the group: the current font is restored to cmr10, and the
   local definitions of steps 3–5 are restored. The global `\font@name` and the loaded font stay.
8. **After the group** (outer level, so these assignments persist):
   - `\maybe@ic` runs; `\futurelet` **peeks at the token after the group** (a space);
   - `\ifdim\fontdimen1\font>\z@` is false (cmr10), so `\maybe@ictrue` **sets `\ifmaybe@ic`
     locally at level 0**;
   - `\@tfor` over `\nocorrlist` (`,.`) runs `\t@st@ic`, which compares the peeked token with
     `,` and `.`;
   - not found, so `\sw@slant` reads **`\lastskip`** (0pt) and `\fix@penalty` reads
     **`\lastpenalty`** (0);
   - so `\/` appends the **italic correction** of `x`. It is `\kern 1.20416` in the pinned
     binary's run of §7.4's input.

   Persisting writes at level 0: `\ifmaybe@ic`, `\reserved@a` (three times), `\reserved@b`
   (twice), `\@fortmp`, `\@let@token` [M]. These are exactly **what a use leaves behind** (C-90),
   and a later `\ifx\reserved@a…` anywhere in the body reads them.

What this means for the abstract run, step by step:

| step | what `exec#` needs | in §3? |
|---|---|---|
| 1 | the mode, exact in the abstract nest | yes |
| 2 | the group: an abstract save-stack frame | yes |
| 3 | the argument's shape predicates (empty, space, `\nocorr` split) as guards; `\edef\reserved@a{\unexpanded{#1}}` stores a **copy** of the argument (`dyn_used` grows by its length: C-98's channel) | yes; the copy's Δ needs the relational component of §3.5 (3) |
| 4 | `\fontdimen1` of the current font: `Exact` if the key fixes the current font, otherwise a fork over the font set | yes |
| 5 | `\csname` of a concrete name: `id_lookup` over the hash. **The hash probe sequence depends on every name in the table**, so the read set differs between configurations unless the name-map abstraction holds | **only with AI-2** |
| 5 | the font load: `new_font` → `read_font_info` → the TFM open and read: **the C boundary**. `font_info` grows (`fmem_ptr`, a capacity); `font_ptr` grows (`font_max`) | needs the boundary (parallel branch); capacity by §3.5 |
| 5 | `\UseHook{selectfont}`: the hook's token list, read from the store; it enters the key | yes |
| 6 | `\futurelet` on the argument's first token: the kernel knows it (a guard on `#1`'s first token) | yes |
| 6–7 | typesetting `x`: a char node from `get_avail`, so **the allocator abstraction** | **only with AI-2** (otherwise the key includes the `avail` head) |
| 7 | `\aftergroup` and `unsave`: the real code on the abstract save stack | yes |
| 8 | `\futurelet` on the **continuation**: a guard on the follower's class (`,`/`.`, or a control sequence `\ifx`-equal to one of them, or other) | yes, a peek-only read of `Next` |
| 8 | `\lastskip`, `\lastpenalty` of the current list: the last-node observers | yes (§3.3) |
| 8 | `\/` appends a kern node: allocator again; its width from `font_info` of the argument's **last** character (`x`'s italic correction): a read that depends on the argument's last token | guard or `Sym` on the last character; allocator by AI-2 |

### 7.4 The model's run [M: `ai/evidence/model/model3/`]

- **The model's terminal output is 18,849 bytes, and they are a byte-for-byte prefix of the pinned
  binary's 42,220 bytes on the same input** (`model-terminal.txt`, sha256 `2ad21d15…`, against
  `binary-terminal.txt`, `cmp` of the first 18,849 bytes). Covered: the format load;
  `\scrollmode`; the tracing assignments; `\setbox0\hbox{`; `\emph`'s robust wrapper; `\ifmmode`;
  the group; `\text@command` with its argument split; `\em`; `\itshape`; `\selectfont` with
  `\maybe@load@fontshape`'s group and `\ifcsname`; the global `\xdef`; `\define@newfont`'s size
  table loop with its `\futurelet`; `\extract@font`; and every trace line of all of these.
- Then the model stops with
  `RESULT: stuck: 600 > 593 > 560 > 558 > 247 > unmodelled external: bopenin`. That is
  `mainbody > maincontrol > prefixedcommand > newfont > readfontinfo > bopenin`: the TFM open of
  `cmti10` (procedure names from the build's `procnames.txt`). The binary continues with
  `{globally changing OT1/cmr/m/it/10=select font nullfont}` /
  `{into OT1/cmr/m/it/10=select font cmti10}` and finishes both boxes.
- `new_font` (pdftex.p, module 1438) reuses an already loaded font only if its name, area and size
  match. The format holds 40 fonts (`627721 words of font info for 40 fonts`, the model's own
  statistics in `model1`'s run. That run put `\emph{x}` straight into vertical mode in format
  state, met LaTeX's "Missing \begin{document}" error, and stopped `Stuck` at `removepdffile`
  during `close_files_and_terminate`, after printing them). `cmti10` at 10pt is not among them, so the read is forced [R +
  M].
- A control run (`model0`: `\font\x=cmti10`) stops at the same `bopenin` [M].
- An earlier variant with a letter in `\nullfont` before `\emph` stopped earlier:
  `stuck: 600 > 593 > 337 > unmodelled external: pdfassert`. Procedure 337 is `getautokern`.
  That is a second boundary gap on the path of *every* typeset character in a font without the
  glyph (not kept as evidence; it is reproduced by putting `A ` before `\emph` in `model3/stdin`).
- Cost: 73.1 s user CPU, peak 1,523 MB, against 73.6 s for `model0` (§6.2) [M].

**So the TeX side of the model already executes `\emph`'s real code exactly, as far as it can
go. The first thing missing is the C boundary (TFM file input), which is being built on another
branch.** No hand modelling of `\emph` was involved, which is ADR-015's premise working as
intended.

### 7.5 The summary admission would produce (written by hand from the trace and the code)

Precondition `a` (the key's control-relevant part):
- horizontal mode;
- group level `L`;
- the current font `cmr10` (OT1/cmr/m/n/10, `\fontdimen1` = 0);
- `\emfontdeclare@clist` empty;
- `\font@name` either way;
- `\OT1/cmr/m/it/10` **undefined or `\relax`** (first use) **or** already the font `cmti10`
  (later use): two cases;
- the `selectfont` hook's token list (a value read, so a key component);
- `\nocorrlist` = `,.`;
- `\maybe@ic`, `\check@nocorr@`, … with their format meanings (read, so in the key, through the
  frame lemma's read set).

```
Σ(\emph{#1}, a) =
  guard "#1 is empty" or "#1 is a single space"    -> [no \check@icl/\check@icr; else as below]
  guard "#1 contains \nocorr at depth 0"           -> [3 sub-cases, by \check@nocorr@'s \ifx tree]
  guard "#1 plain, first token not \nocorr":
    T0:  open a simple group (cur_level := L+1; save_ptr += k₁);
         \edef\reserved@a (local; dyn_used += |#1| + c₁);  \check@icl, \check@icr (local);
         font := cmti10 (local);  \font@name := \OT1/cmr/m/it/10 (GLOBAL);
         [first use only:] \OT1/cmr/m/it/10 := font cmti10 (GLOBAL); font_ptr += 1;
                           fmem_ptr += size(cmti10.tfm)        -- the TFM read: C boundary
    HOLE #1 in state (horizontal, level L+1, font cmti10, \check@icl pending)
         \maybe@ic@'s peek at #1's first token is decided by the font: cmti10 is slanted, so
         nothing is inserted and no guard is needed here (an upright inner font needs one)
    T1:  \aftergroup\maybe@ic; unsave: font := cmr10, locals restored (save_ptr back to entry)
    PEEK Next:
      guard "Next is , or . (or \ifx-equal)" -> T2a: \ifmaybe@ic := false (local, level L) ...
      guard "otherwise"                       -> T2b: \ifmaybe@ic := true;
          observers: last glue = 0 and last penalty = 0  -> append kern(italcorr(last char of #1))
          last glue ≠ 0                                 -> \unskip, kern, re-add the glue
          last penalty ≠ 0                              -> \unpenalty, kern, \penalty
    Post: mode, level L, font cmr10 restored; GLOBAL \font@name changed;
          level-L writes: \ifmaybe@ic, \reserved@a, \reserved@b, \@fortmp, \@let@token;
          list: + the argument's material + possibly a kern;
          Δ: cur_level peak +1 (+ the hole's), save_ptr peak +k, dyn_used peak +|#1|+c, fmem_ptr +…
  mode = vertical: \leavevmode first (new_graf, \everypar's paragraph hooks, build_page at the
                   outer level, §2.4) -> a separate case set, subject to page safety
  mode = math:     \nfss@text{\em #1} = {\mbox{…}}: a separate case set
```

Counting the cases gives the estimate of §6.3: the mode (3) × first use (2) × the argument's shape
(about 4) × the follower class (2, not in math), less the combinations that cannot occur, so
≈ 20–50.

### 7.6 Where the current machinery suffices, and exactly where it does not

| needed for `\emph`'s admission | exists? | evidence |
|---|---|---|
| the real definition, as pdfTeX holds it | **yes**: the format load is exact, and the meanings are identical to the binary's for all 23,519 names | H3 report [R]; §7.2 [M] |
| executing that definition exactly (expansion, groups, global and local assignments, `\csname`, `\ifcsname`, `\futurelet`, the delimited argument split, the hook) | **yes**, up to the first external | §7.4: an 18,849-byte identical prefix [M] |
| the TFM read on first use (`bopenin`, then the TFM bytes) | **no**: C boundary, parallel branch | §7.4 `Stuck` [M] |
| `pdfassert` on the path of a missing glyph | **no**: C boundary | §7.4 [M] |
| a body-start state (the `article` preamble, `\begin{document}`) | **no**: needs file input (C boundary) and a snapshot (not built) | §1, §5 |
| `exec#`, the abstract store, forks and joins | **no**: no code | §1 [R] |
| holes for `#1`, and guards on the argument's shape and first token | **no** | — |
| the symbolic continuation and the peek guard | **no** | — |
| the read-set recording and the frame lemma | **no** | — |
| the allocator and name-map abstraction (needed at steps 5, 6, 8) | **no**: the deciding unknown | §4.3 |
| capacity Δs (font memory, `dyn_used` for the `\edef` copy) | **no**: the relational component of §3.5 (3) | — |
| page safety, needed if `\emph` starts a paragraph | **no** | §3.3 |
| a kernel that can consume such a summary | **no**: `Contract.signature` has two fields, `text_beh` and `math_beh` | `proofs/Strict/Contract.v` [R] |

The concrete foundation suffices. Everything specific to admission is missing, and the one
abstraction without which no summary can be reused (allocation and names) is also the hardest
to prove.

## 8. Question 7: a pre-registered plan

**Fixed now, before any building** (changing any of these later is a recorded owner decision,
never a silent edit):
- K = 64 live cases per summary;
- a look-ahead window of 2 segments;
- the thresholds in the table below;
- the measurement conditions:
  - E4's quiet machine for every speed figure (load average below 4, recorded per row);
  - every binary-side grade through `_oracle.py` (E7's measurement entry point once it lands;
    until then a stated recipe, as here);
  - the aarch64 architecture of record (E9);
  - the fixed clock (E10/OPEN-128).

**Standing stop rule.** At any milestone, **one** PROVEN verdict that the oracle contradicts
stops the track for an adversarial review of the method (C-30). It is never fixed and continued
within the milestone.

### 8.1 Dependencies (not this track's work)

| id | what | where | blocks |
|---|---|---|---|
| D-a | **C boundary**: kpathsea file lookup, `\input`/`\openin` of files, **TFM loading** (`bopenin` and its reads, §7.4), `pdfassert`; then the PDF back end | being built in parallel on another branch | AI-3 onward (the first `\emph` reads a TFM) |
| D-b | a **marshalled state snapshot** after the format load, and at the pre-`.aux` checkpoint (ADR-014 §7.2) | not built; ≈ 1–2 agent-weeks [I] | every AI run past AI-1 (§6.2: the load dominates) |
| D-c | OPEN-128 (the fixed clock, single backend, re-grade) and E7's entry point | main | AI-3's differential against the oracle |
| D-d | **H.4** (the concrete model agrees with the oracle on the L_S0 evidence) and **H.6** (co-simulation) | spike | the meaning of every result here: `exec#` is sound relative to `exec`, and `exec`'s faithfulness is `FaithfulEngine` |
| D-e | the owner's ruling on **O1.2** (§5.2) | owner | AI-6's cost model |

### 8.2 Milestones

Effort is in agent-weeks for one focused track [I]. The basis for the effort figures follows the
table (§8.3).

| id | work | PASS (all of) | KILL (any of) | effort [I] |
|---|---|---|---|---|
| **AI-1** | `exec#` over `PS`: the abstract store of §3.1; forks, joins and widening (§3.2); read-set recording; the relational component for argument scans (§3.5 (3)). Proofs: `abstract_sound` (against `exec`, the reviewed semantics; no `PS.Step` is assumed) and `readset_frame` (§4.1). Extraction | (a) both theorems closed, `Print Assumptions` = the kernel primitives only, as for `B2Equiv`; (b) the extracted build within H.2's limits (< 2 h compile, < 16 GB); (c) with an all-`Exact` initial state, `exec#` gives `exec`'s outcome and byte-identical output on all 178 H.2 differential inputs and on the 50-name meaning prefix; (d) on (c), `exec#`'s CPU ≤ 20× `exec`'s, quiet machine | either theorem not closed within 8 agent-weeks; (b) fails; (d) > 100× | 4–8 |
| **AI-2** | the allocator and name-map abstraction, route K3 (§4.3): refinement lemmas for the translated `get_avail`, `get_node`, `free_node`, `flush_list`, `id_lookup` and `make_string` under `I_heap`; a verified checker of `I_heap`; per-run preservation checks in `exec#` | (a) the lemmas closed; (b) the checker accepts the format state and the pre-`.aux` states of 20 sample-1 configurations (unsealed); (c) two uses of `\emph{x}` at different positions of one document **share one summary** (the key matches), checked on the model | `I_heap` is false on the real format state and cannot be repaired by restating it within 2 iterations (for instance, if reference-counted sharing makes the local disjointness unstatable); or the lemmas are not closed within 10 agent-weeks. **This kills the synthesis's real-time claim**: the key falls back to K1, and §6.3 then has the static path cost more than executing the document. The report to the owner then recommends ADR-014's product (asynchronous decide-by-execution) or stopping | 4–10 |
| **AI-3** | `\emph` end to end at `article`'s body start; the **new static kernel's** first version (a contract type for guarded summaries with holes, `fold`, capacity checks, the bridge `static_ready_iff_pdflatex`) | (a) `summarize` produces `\emph`'s summary with **no per-command input** (the interpreter is generic), with ≤ K cases, in ≤ 1 CPU-hour; (b) the kernel's fold agrees with the oracle **and** with the concrete model on 100 % of a generated set of ≥ 2,000 documents, fixed before the run. The set varies: the start mode (vertical, horizontal, math); the argument (empty, a space, letters, `\nocorr` first or last, nested `\emph`, `\textbf`, braces, 0 to 20,000 tokens); the follower (`,` `.` a letter, a space, `\par`, `\/`, `\relax`, a macro that expands to `,`); nesting from 1 to past the grouping limit; repetition ×300. (c) 0 false READY; every Outside counted and explained | a false READY or a false NOT-READY caused by the *method* (not a fixable implementation slip; the stop rule applies first); or `\emph` is `Stuck` for domain reasons after 3 domain refinements; or > 64 cases; or > 10 CPU-hours | 4–8 |
| **AI-4** | the page and the passes: page safety for `article` without floats (§3.3); deferred `\write` at shipout; the `.aux` cycle (§2.4) with abstract page numbers | `\label`/`\ref`/`\pageref` decided right on a generated set including the 27th-`enumii` case (ADR-015's composition cases) and the oscillating aux of ADR-013 D-1; 0 false READY | page safety for float-free `article` needs concrete node lists (no abstraction of the page found) after 2 attempts | 4–8 |
| **AI-5** | capacities (§3.5): the enumerated `overflow` sites, each a translation-invariant Δ or unreachable; the main-memory fragmentation lemma | (a) every `overflow` site is classified; (b) the C-86/C-94/C-98 witnesses and their maximisers (re-run on the new kernel) are each decided NOT-READY with the right message or Outside, **never READY**, with every bound recomputed by the gate from the summaries' Δ | no sound bound for main memory's variable-size region with margin ≥ 2 on the bodies of the 200 sample-2 papers | 2–4 |
| **AI-6** | coverage and reuse on the unsealed frame | thresholds, **fixed now**: (a) the warm-cache hit rate, i.e. the fraction of sample 2's segment occurrences served by summaries computed for sample-1 papers, is ≥ 80 %; (b) the median cold admission cost per new paper is ≤ 2 CPU-hours (excluding the preamble run, reported separately); (c) ≥ 1 real paper is PROVEN-READY end to end; 0 false verdicts on the frame | hit rate < 50 %, or median cold cost > 24 CPU-hours. Either means the synthesis is not real-time in practice; the report recommends ADR-014's asynchronous product instead | 2–4 |

**Totals [I]:** ≈ 20–42 agent-weeks for AI-1 to AI-6. The prerequisites D-a and D-b come on top;
ADR-014 §8.1 put its C boundary stage (G2) at 4–8 agent-weeks and its end-to-end stage (G4) at
6–10. **The decision point is the end of AI-2: ≈ 8–18 agent-weeks** [I]. If AI-1 and AI-2 have
not both passed within 20 agent-weeks of AI-1's start, the track stops and reports as if AI-2's
kill had fired.

### 8.3 The basis of the estimates

- **On record.** H.2 (the translator, `PS`, the INITEX boundary and extraction) took ≈ 2 days of
  agent work against the draft's 4 days (days 3–6) [R: H2 report checkpoints 2026-09-30 to
  2026-10-01]. But it was mechanical translation, with no proof beyond typing. The H.5 heap fix
  needed a 5-day box (E11 in H5-heap-design) for a performance change proved by reflexivity.
  Nothing on record is a proof of the size of `abstract_sound` or of AI-2's lemmas.
- **Outside the project** [U, recalled, not checked here]: Verasco, the verified static analyser
  for CompCert's C, was a multi-person-year effort. Its domains were numeric; this one adds
  symbolic token streams and a heap abstraction.
- **So** AI-1 and AI-2 are sized as research-grade proof work: several weeks each, with the
  widest ranges. AI-3 to AI-6 are mostly engineering once those two exist.

## 9. Question 8: the verdict

**FEASIBLE WITH CONDITIONS**, within the perfection standard.

**Why feasible.**
1. **The composition theorem is sound by construction, and cheap.** Every summary is an output
   of one proved function over the engine's own code, and the decider is an induction over
   segments (§2.3). No per-command proof, probe, or hand-written behaviour exists anywhere in it.
   Every case it cannot settle is `Stuck`, so there is no approximation, only exclusion (the
   owner's rule: exclude rather than approximate).
2. **The failure classes of the stopped track are closed by construction, not by vigilance:**
   - C-84/C-85 (look-ahead, transparent followers) become derived peek guards;
   - C-90 (what a use leaves behind) is the frame lemma's "everything written is in `Post`";
   - C-92/C-96 (the closure walk) become cell-level read sets;
   - C-94/C-98 (capacity proxies, multiplicative copies) become the engine's own counters with
     translation-invariant Δ, checked rather than assumed (§2.5, §3.5, §4.2).
3. **The foundation already executes a real, intricate command exactly** (§7.4) as far as the C
   boundary allows. No `\emph`-specific work was needed.

**The conditions** (each is a milestone of §8 or an owner ruling):
1. **AI-2 must pass.** Without the allocator and name-map abstraction, no summary is reusable,
   not even across two positions of one paper (§4.3), and the static path costs more than
   executing the document (§6.3). This is the architecture's single deciding unknown, and it is
   research-grade.
2. **The C boundary (D-a) and a state snapshot (D-b) must exist** before any summary can be
   computed for a body command (§7.4, §6.2).
3. **The owner must accept the tier boundary the page imposes.** The first version is `Stuck` on
   floats, marks beyond the kernel's own, `\vsplit` and inserts other than footnotes, until
   AI-4's page safety is extended. That costs coverage. tikz is in 60 of 200 sample-2 papers and
   `float` in 63 [M], and floats are more common than either [I].
4. **The owner must rule on O1.2** (§5.2), or accept a first verdict that takes minutes to hours of
   model CPU per new configuration (§5.1).
5. **"Real time" holds only on a cache hit.** A miss is `PENDING` for minutes to hours (§6.3).
   AI-6's pre-registered hit-rate and cold-cost thresholds decide whether that is acceptable in
   practice. The census bounds the hit rate for a font-level command at about one half (§4.5),
   **below AI-6's 80 % PASS line**. So AI-6 is at real risk: a pass needs commands whose read
   sets are coarser than a whole configuration, which only real read sets can show.

**What would make it NOT FEASIBLE:**
- AI-2's kill (no sound reuse);
- AI-6's kill (reuse too low, or cold cost too high to be real-time);
- or a false PROVEN that traces to the method rather than to an implementation slip.

The first two would leave ADR-014's product, deciding by executing the document asynchronously,
as the engine-free option. It needs none of this machinery, at the cost of D1's "real time".

**The ADR-014 draft's §8.3 put symbolic execution of `latex.ltx` "out of scope"; ADR-015 D2 made
it the admission mechanism without scoping it. This report is that scoping. Its main finding is
that the hard part is not TeX's macro language but TeX's *memory*: allocation and the hash table
decide whether any summary can be reused.**

## 10. What this report did not do, and the record

- **Nothing was built.** No `exec#`, no domain, no kernel change. The only runs are the trace of
  §7 (three model runs kept: `model0`, `model1`, `model3`; one more described in §7.4 and not
  kept), one body-start trace, one meaning walk and one corpus census. Every speed figure for the
  abstract interpreter is [I].
- **The census** read the arXiv corpus from a local copy of the corpus at the paper ids of
  `corpora/real_roots/results_sample2.json`. It did not recompute each paper's `sha256_tree`
  against the manifest, so the copy's identity with the graded trees is not verified here.
- **No binary run went through `_oracle.py`.** These were reads of meanings and traces, not grades,
  as in the H.3 README's recipes. Any grade in AI-3 onward goes through the oracle (§8).
- **Ids.** OPEN-129 is this scoping's ledger row (PROJECT_STATE on this branch). The reserved
  correction ids C-151 to C-159 were checked free on every remote and local branch and in every
  worktree on 2026-10-06. **None is used:** this report records no error of the project's that it
  found *and* that a C-row should own. The two facts it states against the record go to the
  owner through OPEN-129, not as corrections:
  - that ADR-014's `PS.Step`, closure compiler and `exec#` were never built (§1);
  - that ADR-015 D2 reverses ADR-014 §8.3 without scoping it.
