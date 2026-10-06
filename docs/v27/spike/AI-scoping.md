# Scoping the abstract interpreter of ADR-015's synthesis (OPEN-129)

**Status:** scoping report, 2026-10-06. Nothing here is built; one feasibility trace was run.
**Asked by:** owner decision E13 (2026-10-06): the fast-interpreter fallback is not funded until
this scoping reports. **Ledger:** OPEN-129. **Branch:** `spike/v27165-ai-scoping`, cut from
`spike/v27165-engine-translation` at `67ca47df`.
**Reads:** ADR-015 on `origin/main` (D1–D4, E1–E10, Consequences); the drafts ADR-013 (R-EFFECT)
and ADR-014 (interpreter) in `docs/v27/adr/drafts/`; the re-audit dated 2026-10-07 (premises 8–11; a
local file, not in the repository); `docs/v27/STRICT_TIER_DESIGN.md`; the spike's H1, H2, H3 and
H5 reports and `h2/coq` (`Values.v`, `Interp.v`, `Boundary.v`, `Extract.v`, `B2Equiv.v`);
`proofs/Strict`; PROJECT_STATE C-83 to C-100. Of those, **C-92, C-94, C-96 and C-98 exist only on
the branch `origin/feat/v27165-strict-args`** (the stopped signature track), not on `origin/main`
and not on this branch; every citation of them below means that branch's PROJECT_STATE.
**Revised 2026-10-06** after two adversarial reviews (soundness: MISLEADING; evidence and cost:
ACCURATE WITH CORRECTIONS, bordering on misleading). Every finding was checked against its source
or reproduced; the first version's verdict ("FEASIBLE WITH CONDITIONS") is withdrawn. What the
first version got wrong, and the classes behind it, are C-152 to C-158 (PROJECT_STATE on this
branch); §10 lists each change.

Evidence tags as elsewhere: **[M]** measured, **[R]** read from a source, **[I]** inferred,
**[U]** recalled or unverified. Every [M] names its artefact under [`ai/`](ai/).

## 0. The answer, in brief

- **Verdict: RESEARCH PROGRAMME WITH AT LEAST FOUR RESEARCH-GRADE UNKNOWNS** (AI-2 allocator/name
  map; M1 resumable semantics; M4 stack/pool relative addressing; M5 node-list and layout
  abstraction); **first-version coverage ceiling 2.5–15 % of real papers** (§9).
  - **What held** from the first version: the *safety principle*. Every case the design cannot
    settle is `Stuck`, which means outside the tier, never guessed. Reuse is keyed by the read
    set the run itself observes, never by a TeX-level analyser (§4.1–§4.2). Nothing found makes a
    sound summary-based decider impossible.
  - **What did not hold**: that one unknown decides the architecture. Two reviews found four,
    each research-grade, and none is built:
    - **AI-2**, the allocator and hash-table (name-map) abstraction (§4.3). Without it no summary
      is reusable, not even between two uses of `\emph` in one paper;
    - **M1**, a *resumable* semantics. `Interp.v` is a big-step, fuelled, mutually recursive
      interpreter: the control state at a segment boundary lives in Coq's recursion, not in the
      store, so "run from a boundary state" is not yet a definable thing (§2.1);
    - **M4**, relative addressing for the stacks and the string pool. `save_ptr`, `input_ptr` and
      `pool_ptr` are array indices, so a capacity counter that enters as an unknown makes every
      read through it land at an unknown address (§3.5);
    - **M5**, a sound shape-and-interval abstraction of node-list processing: `line_break` at
      every `\par`, `hpack`/`vpack`, `mlist_to_hlist`, `append_to_vlist`, `build_page` and
      `fire_up`. Without it every paragraph end is `Stuck` (§3.3).
  - **The coverage ceiling.** The first version is `Stuck` on floats, marks, `\vsplit` and
    multicolumn pages (§3.3). On sample 2, **168 of 200 papers use floats** (89 of the 95
    `article` papers), 22 use marks and 14 use `multicol` or `\vsplit`. **Only 29 of 200
    (14.5 %) use none of them, and 5 of 200 (2.5 %) on AI-4's `article`-only scope** [M, regex
    screen; an upper bound, §4.5].
  - **AI-6 fails both of its PASS lines on this report's own central estimates** (§6.3): the warm
    hit rate is at most ≈ 40–70 % for a font-level command (81–143 of 200 papers share a
    signature, an upper bound) against ≥ 80 %, and the admission cost per new paper is ≈ 50–90
    CPU-hours cold, ≈ 25–45 with ≈ 50 % warm reuse, against ≤ 2. Both cost figures are
    past AI-6's KILL line (24 CPU-hours). The first version's own basis gave ≈ 6–10 hours with
    warm hits, which was already over the PASS line and was not said.
- **The judgement** (§2) is a Hoare-style summary over the engine's real state, at *segment
  boundaries* of the input. It has holes for arguments (tokenized under the table in force when
  the engine read them), guards on the following tokens, a per-capacity peak, and `Stuck` as the
  escape. **The composition theorem** (§2.3) is an induction over segments using determinism,
  inside a decider that models the protocol's retry loop, one start state per pass. Its logic is
  small, but it rests on M1: there is no resumable semantics to state it over yet.
- **The feasibility trace** (§7) used `\emph` from `latex.ltx`. Its first use at `article`'s
  body start runs **146 macro expansions, 55 assignments and 50 conditionals** [M] (the first
  version said 66 and 28: it missed the trace lines printed while `\escapechar` is −1). It
  exercises a mode conditional, a group, `\aftergroup`, three `\futurelet`s, a delimited
  argument split, `\csname`, global assignments, a configuration hook, and a font load.
  - **The model reached only part of that** [M]. The B2 model build ran `\emph{x}` in *format*
    state inside an `\hbox` and printed 18,849 terminal bytes identical to the pinned binary's
    prefix. That prefix runs `\emph` up to `\selectfont`'s font load: **1 of the 3
    `\futurelet`s** (the one inside `\define@newfont`), **no `\aftergroup`, no hook**. Then the
    model stopped `Stuck` at the TFM open of `cmti10` (`readfontinfo → bopenin`).
  - So the TeX side of the model ran every line it reached exactly, and the C boundary is the
    first gap (being built in parallel). The rest of `\emph`'s first use is unexercised in the
    model. Everything abstract (`exec#`, the domain, holes, the key's lemmas) does not exist [R].
- **The key** (§4): the summary's read set, recorded at the level of the engine's state by the
  instrumented run itself, including the reads that bypass `cell_at` (the `hp`/`fp`/`fsp`
  fields, block sizes, the I/O record). Its reuse is sound by a frame lemma proved once for
  `PS`. That is unlike ADR-013's P-1, which trusted a TeX-level static analyser.
  - Cross-position and cross-configuration reuse needs read sets invariant under renaming of
    allocated addresses, hash slots and stack offsets (AI-2 and M4).
  - Reuse on sample 2 is a crude two-sided estimate: **81 to 143 of 200 papers share an
    `\emph`-relevant configuration signature with an earlier paper, depending on the key** [M on
    a regex instrument; the hit rate itself is I].
- **Cost** (§6). On a cache miss, the abstract run is a second extracted interpreter over the same
  AST. It is not the "closure compiler", which was never built [R]. It runs ≈ 5–20× slower than
  the concrete model per explored path, times the number of forks [I]. Per-command work in the
  concrete model costs **≈ 1,540×** pdfTeX on H.5's best variant (A, with T1 and T2) and
  **≈ 2 × 10⁴×** on the B2 model build, H.5's *marginal* per-name rates [R]. So one explored path
  costs ≈ 1.5 s to ≈ 7 minutes, a summary ≈ 15 minutes at the centre, and a cold paper ≈ 50–90
  CPU-hours [I]. The keystroke path folds cached summaries and is fast [I].
- **The plan** (§8): **cheap discriminators first**, each with a PASS and a KILL line: a
  cross-configuration read-set reuse probe on concrete runs; a feasibility probe for a sound
  `line_break`/`hpack` abstraction on typical paragraphs; and the multi-pass and output-routine
  treatment, checked against witnesses. Then the research milestones, each with its own KILL.
  The effort range is **uncalibrated** (§8.4): the project's last estimate of this kind missed
  by 5–200×.

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
| speed | ADR-014 §7.1 estimate 10–60× | **marginal (per unit of the binary's work), H.5's measure for anything past the format load:** ≈ 1,540× per name on variant A with T1 and T2 (≈ 1,260× min against min), interleaved medians [R: H5-heap-design.md §3.2]; ≈ 2.2 × 10⁴× on the B2 model build `cae7a953…` (no T1/T2), computed from its single full dump: (2,673 s − ≈ 72 s load) / 23,519 names ≈ 111 ms per name, against the binary's 4.97 µs, at a load of up to 283 [I from R: H5 §"H.5 stage 2"]. **Format load:** 59× on A [R]; on the B2 build, 70.4–73.6 s user CPU in this branch's three kept runs (load average 16–25) against the binary's 0.112 s, ≈ 630–660× [M, noisy]. The first version's "≈ 315× on the format load" rested on a 35 s load figure from the local re-audit that no committed artefact holds, and it priced per-command work at that format-load ratio (C-152) |
| the static kernel | `proofs/Strict` (L_S0) decides with per-name signatures `mkSig text_beh math_beh` (`Contract.v`) | built. Its signature type has no field for a group, an argument, a follower, a capacity delta or a state change beyond mode, so it **cannot carry** the summaries of §2. A new contract type and a new `Semantics`/`Decide` pair are needed |

So the record supports ADR-015's *foundation* (a translated engine that executes real format code
exactly). It records nothing about the *admission* step. That step is the subject of this report.

## 2. Question 1: the judgement admission must produce

### 2.1 The objects

- **The engine.** `exec` of `prog` (the translated `pdftex.p`) over `PS` states `S` (heap of
  blocks, the `hp`/`fp`/`fsp` fields and the I/O record, `Values.v`). It is deterministic: it is
  a Coq function. Write `run : S -> Outcome` for a whole job.
- **There is no `step*` (review M1).** The first version wrote `step*(s) = s'` for "the run from
  boundary state `s` reaches `s'`". `Interp.v` has no such thing [R]:
  - `exec` is a **big-step, fuelled, mutually recursive** interpreter (`evale`, `evall`,
    `callp`, `exec`, `for_loop`, `exec_list`, `goto_in`, `write_items`, all `{struct fuel}`). At
    a segment boundary, `main_control` is in the middle of its `while` loop, `main_body` is
    below it, and that *control* state lives in Coq's recursion, not in the store. A store
    alone does not say where to resume.
  - Fuel bounds **recursion depth**, and loops recurse: `SWhile` runs its body and then calls
    `exec f (SWhile c b)` with the same decremented fuel (`Interp.v`, the `SWhile` case). So
    the fuel `main_control` needs grows with the number of its iterations, i.e. with the
    document's length.
  - So the judgement needs, first, a **resumable semantics**: a small-step or
    continuation-passing form of `exec`, or a proved decomposition of `main_control`'s loop
    into "one iteration from a store at the loop head", together with a proof that it agrees
    with `exec`. Second, `Protocol` must be stated with **∃ fuel**, with a fuel-monotonicity
    lemma (more fuel never changes a non-`StFuel` result), so that composing segment runs
    cannot be defeated by a fuel bound. Neither exists, no milestone of the first version built
    them, and AI-1's scope excluded them. Below, `step*` means that missing semantics; §8 makes it
    milestone AI-7.
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
    buffer loaded up to the end of `p`'s line, as `input_line` reads whole lines), with a
    bounded stack of **backed-up token lists** on top of it. One `\futurelet` alone leaves
    **two** such levels: it reads two tokens, backs up the second and then the first (tex.web
    §1221 calls `back_input` twice, §325). The first version said "at most one";
  - those levels hold the tokens `τ` (a list of lists), already tokenized from the bytes just
    before `p`;
  - no macro or parameter level is pending.

  `τ` matters because tokens tokenized under one catcode table keep it after a later
  `\catcode` change. The abstract state therefore carries `τ` *as tokens*; it never
  re-tokenizes them.
- **Token-list boundaries, and the table a hole was tokenized under (review M2).** The first
  version let a hole's own segments be cut from the argument's *bytes* by the kernel, under the
  abstract state's current catcode table. That is ill-formed. The engine tokenizes an argument
  **when `macro_call` scans it**, under the table in force *then*, and the argument's body then
  runs from a token list. Witness [M: `ai/evidence/witnesses/m2-catcode.tex`]:
  `\emph{\catcode`\e=12 \relaxe}`. The engine reads `\relaxe` as one control word before the
  `\catcode` assignment runs, so the run stops at "Undefined control sequence" (rc 1 on every
  pass). A kernel that re-cuts the argument after the assignment, under the updated table, sees
  `\relax` followed by the character `e`, and that document (`m2-recut.tex`) compiles (rc 0): a
  **false READY**. So:
  - a hole is a **token list** `Arg i` together with the catcode table `C_i` under which the
    kernel tokenized it, which must be *the table at the moment the engine's scanner read it*
    (an exact table in the abstract state at that program point, else `Stuck(catcode)`);
  - `Bnd` has a second form, `BndTok(s, ℓ, k)`: the input stack's top is a token-list level
    holding the remaining tokens `ℓ` of an argument, at token offset `k`. A hole's segments are
    cut from `ℓ`, never from bytes;
  - `Sound` (§2.2) quantifies over both forms, and the cut of a byte segment is a function of the
    exact table at each byte the engine reads, which a segment that changes catcodes must
    expose as a guard.

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
  that argument's own segments, **cut from the token list `Arg i` tokenized under `C_i`**
  (§2.1), from `a_h`; the summary resumes from whatever abstract state they end in.
- **An argument has three uses, not two** (review H2). It can be (1) executed as body text (a
  hole), (2) tested by the code (a shape guard), or (3) **copied and executed later**, outside
  this segment: `\label{#1}` puts `#1` into a non-immediate `\write` whose tokens are expanded at
  shipout, and the `.aux` line they produce is read back and executed at `\end{document}` and in
  the next pass. Use (3) needs the copy to be carried in the abstract state as a symbolic token
  list `Copy(Arg i, C_i)`, and checked where it is executed (§2.4). The first version had only
  (1) and (2), so its §3.4 made `\label` `Stuck` while AI-4's PASS line required `\label` to be
  decided: the two contradicted each other.

**Soundness of one summary** (`Sound Σ`), the property admission must establish:

```
forall a s q τ, s ∈ γ(a) -> (Bnd(s, q, τ) \/ BndTok(s, q)) ->
  the input at q, tokenized under the exact table of a at each read, is an occurrence of u ->
  let (g, R) := the first case of Σ whose guard holds on (a, input, τ) in
  match R with
  | Post a' Δ   => exists s', step*(s) = s'               (* step*: the resumable semantics, AI-7 *)
                    /\ (Bnd(s', q + |u|, τ') \/ BndTok(s', q + |u|)) /\ s' ∈ γ(a')
                    /\ no error was issued between s and s'
                    /\ every capacity counter v stayed <= v(s) + peak_v and ended at v(s) + end_v
  | Fatal m c l => run s = Fatal m c l
  | Hole (Arg i, C_i) …
                => the same, by induction on the segments of Arg i's token list,
                   each started from BndTok, with Arg i tokenized under C_i
  end
```

The guard is part of the precondition. A state or text in which no guard holds has no
summary, so it is outside the tier. Until AI-7 defines `step*` and proves it agrees with `exec`
under ∃-fuel (§2.1), `Sound` is a statement about an object that does not exist.

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
Definition fold (a : A) (us : list Seg) : AbsPassResult :=  (* the static kernel, ONE pass *)
  match us with
  | []      => Outside                                       (* a body must end with \end{document} *)
  | u :: r  => match lookup_summary u a with                 (* u is cut under a's exact table *)
               | None              => Outside
               | Some (Post a' Δ)  => if capacity_ok a Δ then fold a' r else Outside
               | Some (Fatal m c l)=> Ended (Fatal m c l) (aux_out a)   (* partial aux: §2.4 *)
               | Some (EndDoc R)   => R                     (* \end{document}: Ended _ aux'# *)
               | Some (Hole (Arg i, C_i) …)
                                   => fold Arg i's token segments from BndTok, then continue
               end
  end.
(* The first version's fold returned a Verdict per pass and had no retry loop (C-155). *)

(* The protocol, as _oracle.run_to_fixpoint implements it (scripts/tools/_oracle.py on main,
   MAX_PASSES = 3): up to 3 passes, stopping at the first rc 0; if none had rc 0 the verdict is
   the 3rd pass's; otherwise ONE confirming pass, whose rc is the verdict. Each pass starts from
   the .aux (and other auxiliary files) the previous pass left, INCLUDING a failed pass's
   partial output. decide models exactly that loop, one abstract start state per pass. *)
Definition decide (cfg : Config) (B : Body) : Verdict :=
  let pass (aux# : AbsAux) : AbsPassResult :=           (* fold of §2.3 from a0(cfg, aux#) *)
      fold (a0 cfg aux#) (segments B) in
  let fix retry (k : nat) (aux# : AbsAux) :=
      match pass aux# with
      | Outside              => Outside
      | Ended (Fatal m c l) aux'# => if k = 3 then NotReady m c l else retry (k + 1) aux'#
      | Ended Compiles aux'# =>                              (* the confirming pass *)
          match pass aux'# with
          | Ended Compiles _      => Ready
          | Ended (Fatal m c l) _ => NotReady m c l
          | Outside               => Outside
          end
      | Forked _             => Outside        (* passes disagreeing across γ(aux#): no verdict *)
      end
  in retry 1 aux#_empty.

Theorem static_decider_exact :
  forall cfg B a0 s0,
    s0 = body_start_state cfg B            (* the concrete state at body start, pass by pass §2.4 *)
    -> s0 ∈ γ(a0)                          (* §5: by a model run (proved) or a snapshot (premise) *)
    -> (forall Σ in the cache, Sound Σ)    (* by summarize_sound, plus cache integrity, §4.4 *)
    -> decide cfg B ≠ Outside
    -> (decide cfg B = ProvenReady            <-> Protocol cfg (P ++ B) = Compiles)
    /\ (decide cfg B = ProvenNotReady m c l   <-> Protocol cfg (P ++ B) = Fatal m c l).
    (* Protocol is stated with ∃ fuel (AI-7), over exactly the loop decide models. *)

Corollary static_ready_iff_pdflatex :
  forall oracle cfg B, FaithfulEngine oracle -> (* the same hypotheses *) ->
    decide cfg B = ProvenReady <-> oracle cfg (P ++ B) Compiles.
```

**The proof is an induction on the segments, inside an induction on the passes.** Each `Post`
step uses `Sound Σ` to move the concrete run to the next boundary, still inside `γ`. A `Fatal`
step is exact by `Sound`, and it also yields the pass's abstract aux output, which is the next
pass's start (§2.4). Determinism (`exec` is a function) turns "some run reaches s′" into "the run
reaches s′", **but only once AI-7 gives a resumable `step*` and fuel monotonicity** (§2.1):
without them, "the run from a boundary state" is not defined, and a fuel bound could separate
the composed runs from the whole one. Capacity side conditions add up where each `Δ` is relative
to the entry value (§3.5, with its corrections).

The theorem has the same shape as `strict_ready_iff_pdflatex` (`proofs/Strict/Bridge.v`), with
`FaithfulEngine` in place of `Faithful`. Its logical content is small, as ADR-014 §4.4 said of
`decide_exact`. **Its logic puts no load on the induction. The load is on the objects it is
stated over (AI-7's semantics), on `Sound Σ`, which `summarize_sound` gives by construction, and
on whether `summarize` returns `Some` for real commands at a level of abstraction that is
reusable** (AI-2, AI-8, AI-9).

### 2.4 Passes, the page, and `\end{document}`

- **Passes (review H1).** `Protocol` runs up to three passes to the first rc 0, then one
  confirming pass (ADR-014 §4.5; `_oracle.run_to_fixpoint`, lines 1396–1421 of `_oracle.py` at
  `5aa96502` and at this branch's base, lines 1673–1699 on today's `origin/main` `17996978`, the
  same loop) [R]. **The first version's decider did not model that loop.** It said "the verdict
  is `Compiles` only if every pass compiles for every value in `aux#`", which is false: a pass
  that fails is *retried*, from the `.aux` the failed pass left. Witness [M:
  `ai/evidence/witnesses/h1-multipass.tex`, `protocol-out.txt`]: the body does
  `\immediate\write\@auxout{\gdef\string\zzflag{1}}` and then
  `\ifx\zzflag\undefined \GenericError{…}\fi`. Pass 1 has no `.aux`, so it writes the line and
  stops with rc 1. Pass 2 reads `\gdef\zzflag{1}` at `\begin{document}` and compiles (rc 0); the
  confirming pass 3 compiles too: **`Compiles`**. The first version's rule calls it NOT-READY,
  a false NOT-READY. So `decide` (§2.3) iterates the passes, each from its own abstract start
  state, and a failed pass's **partial** auxiliary output (everything written by
  `\immediate\write`, plus what `close_files_and_terminate` flushes after the error) is the next
  pass's input. The fold therefore returns the pass's result *and* its abstract aux output.
  The body-start state of pass k+1 depends on the `.aux` that pass k wrote, so it depends on the
  body. The decider therefore needs:
  - (i) a snapshot just **before** `\begin{document}` reads the `.aux` (ADR-014 §7.2's
    checkpoint);
  - (ii) the `.aux` reading summarised like any other text. It is a sequence of `\newlabel`,
    `\bibcite`, `\@writefile`, … segments, run from an abstract aux content `aux#` that the
    previous pass's fold produced;
  - (iii) the rest of `\document` (the `\AtBeginDocument` hooks: hyperref does a great deal
    here) summarised as one segment.

  `aux#` is abstract wherever the page is abstract. A `\label`'s page number is `Range 1..N`
  (§3.3), so pass k+1 runs on an abstract aux. A `\pageref` typesets digits, which needs only a
  bounded width. An `\ifnum` on the page forks or is `Stuck`. Each pass's result must be the same
  for every value in its `aux#` (else `Forked`, hence `Outside`); `decide` then follows the
  protocol's loop on those results.
- **The page is asynchronous.** The output routine fires inside segments: whenever material is
  moved to the page while the page is full. That happens even at the start of an `\emph` in
  vertical mode, because `new_graf` calls `build_page` at the outer level (tex.web §1091) [R].
  So a segment's summary must cover "the output routine may fire here", or the abstract state
  must decide that it does not.
- **A per-configuration page-safety obligation is unsound (review H2).** The first version proved
  the output routine safe *once per configuration* and let every segment assume it. But the
  output routine reads state the **body** can change, and expands tokens the body supplied.
  Two witnesses [M: `ai/evidence/witnesses/`, `protocol-out.txt`, `context-out.txt`]:
  - `\renewcommand\thepage{\zzz}`: the error fires **in the output routine**, when the footer
    expands `\thepage` at shipout (`\thepage ->\zzz`, reported at `l.5 \end{document}`), rc 1 on
    all three passes. With the command in the *body* (`h2-thepage-body.tex`) the configuration
    is stock `article`, whose output routine is safe, and the run still fails the same way:
    a per-configuration proof would have called it READY;
  - `\label{a\protect\zzz}`: the label's tokens go into a deferred `\write`, the `.aux` gets
    `\newlabel{a\zzz }{{}{1}{}{}{}}`, and the run fails **when the `.aux` is read back** at
    `\end{document}` (`<argument> a\zzz`, `l.2 \newlabel…`), rc 1 on all three passes.

  So the output routine and the deferred-write/`.aux` channel are segments like any other: they
  need **per-state summaries keyed by their read sets** (§4.1), looked up at each point where
  the output routine may fire, against the abstract state there, including the `Copy` token
  lists of §2.2 that sit in whatsits on the page. Reading the `.aux` back (at `\end{document}`
  and at the next pass's `\begin{document}`) is a segment sequence run over the abstract aux
  content. §3.3 restates the page treatment on that basis.
- **`\end{document}`** is a segment whose result is the end of the pass: `\clearpage`, the last
  shipouts, the `.aux` writes, `\enddocument`'s checks ("Label(s) may have changed" is a warning,
  rc 0), and `close_files_and_terminate`. Its summary ends the pass with `Compiles` or `Fatal`.

### 2.5 The hard cases, one by one

Each row says what the judgement does with the case, and what is left. "Inside" means a summary
can exist; "Stuck" means outside the tier.

| case | what happens in `exec#` | status |
|---|---|---|
| **global assignments** (`\global`, `\xdef`, `\gdef`, `\global\font`, e.g. `\emph` leaves `\font@name` globally changed, §7) | `eq_define`/`geq_define` run on the abstract store; the write is a plain write to `eqtb` and `Post` records it; `unsave` leaves global values in place because it runs the real code | inside, **exact** (it is the engine's own code). The risk C-90 named (what a use *leaves behind*) is closed by construction: whatever `Post` omits is unchanged by the **write-frame** property (§4.1: every write, including whole-block writes through `hput` and output through the I/O record, is recorded), so nothing a run writes can be missing from it |
| **local assignments, groups** | the save stack is a stack of abstract frames; a summary that opens and closes its own group restores exactly what it saved, by the real `unsave`; a summary that leaves a group open (`\begin{itemize}`) leaves its frame on the abstract stack for the matching close | inside; the frame contents enter the **key** of the closing segment (§4) |
| **`\catcode` changes** (`\makeatletter`, `\verb`, `\url`, `\ExplSyntaxOn`) | the catcode table is in `eqtb` and is written like anything else | inside **only if** the table is exact at every boundary, and the segment says under which table its argument is tokenized (`\url` changes catcodes *before* it reads its argument, so its hole is "the bytes up to the delimiter, tokenized under table C′"). A catcode that is `Top` at a boundary is `Stuck(catcode)` |
| **`\afterassignment`** | `after_token` is a global of the engine; it is in the abstract state | inside; a segment that ends with `after_token` set passes it to the next segment's key. In code `\emph` can reach (`\selectfont` → `\set@fontsize`, when the line spread changed), `\@defaultunits` sets it and the very next assignment consumes it within the same segment |
| **`\aftergroup`** | `insert_token` entries on the save stack, run by `unsave` (tex.web §280–§282) | inside. `\emph`'s `\check@icr` puts `\maybe@ic` there and it runs inside the same segment (§7); for an open environment the entries ride on the frame, and the frame is part of the key |
| **look-ahead** (`\futurelet`, `\@ifnextchar`, `\@ifstar`, keyword and number scanning such as `plus`/`minus` after glue or a digit after `\count0=1`, display `$` with `get_x_token`) | the continuation is a **symbolic token** `t`; a read of it forks on the classes the code distinguishes (`\ifx` against a meaning, a catcode test, a digit test) and becomes a guard | inside when the read is **peek-only** or consumes only characters or meanings that the kernel can see statically. When the code **expands** `t`, it executes the next segment's code inside this one; that is allowed only as a fused two-segment summary (a window of 2), and is otherwise `Stuck(expanding look-ahead)`. This is the C-84 class, now derived from the code rather than guessed |
| **`\expandafter` chains** | ordinary code paths of `expand` | inside; nothing special |
| **`\csname`** | `id_lookup` on a name built from tokens | concrete names (`\csname OT1/cmr/m/it/10\endcsname`): inside. A name built from **argument** characters (`\label{key}` → `r@key`): the hash slot depends on every name in the table, so the abstract run needs the **name-map abstraction** (AI-2, §4.3); without it, `Stuck` |
| **conditionals on runtime values** | `\ifmmode`, `\ifvmode`, `\ifcase\currentgrouptype`: exact (finite mode and group state). `\ifdim\fontdimen1\font>0pt`: exact when the current font is concrete in the key; a fork over a finite font set otherwise. `\ifnum\lastpenalty=0`, `\ifdim\lastskip=0pt`: on the abstract last-node observer (§3.3). `\ifnum\day>28`: concrete under E10's fixed clock | inside up to K live cases; past K, `Stuck(fork)` |
| **`\write`/`\openout`** | `\immediate\write` to the job's `.aux`/`.toc`/`.out`: an abstract append log. A non-immediate `\write` is a whatsit holding a token list that is expanded **at shipout**, in the shipout-time state | inside for the job's own files. The whatsit's token list, including any `Copy` of an argument (§2.2), is carried on the abstract page; its expansion at shipout is a segment summarised **at that state**, keyed by its read set (§2.4, §3.3), and the `.aux` lines it writes are read back as segments. `\openout` to any other name, and `\write18`: `Stuck` |
| **capacities** (C-86, C-94, C-98; the brief also names C-100, which on record is the format's byte-reproducibility, not a capacity) | the engine's own counters (`cur_level`, `save_ptr`, `input_ptr`, `max_param_stack`, `dyn_used`, `var_used`, `pool_ptr`, `str_ptr`, `hash_used`, `fmem_ptr`, `expand_depth_count`, …) are ordinary globals; `exec#` tracks each as an interval and records its peak | inside only with §3.5's corrected scheme, which is **not** the first version's: several counters are not translation-invariant. `get_avail` fails on the free list and the gap shared with the variable-size region; `save_ptr`, `input_ptr` and `pool_ptr` are array **indices** (so they need relative addressing, AI-8); `hash_used`'s change depends on occupancy; main memory's variable-size region depends on fragmentation (AI-5) |
| **the output routine** | fires inside segments (§2.4) | inside only through per-state output-routine summaries keyed by their read sets (§2.4, §3.3), which need the node-list abstraction (AI-9); floats, marks, `\vsplit` and multicolumn output are `Stuck` in the first version (§3.3) |
| **`\scantokens`, `\read`, `\input` in the body, `\pdfstrcmp` of runtime text, `\pdfelapsedtime`** | re-tokenization or external input | `Stuck` in the first version. `\input` of a sibling file can later be a segment sequence of its own |

**Is the theorem plausible?** Its *logic* is, because it is weak where it has to be: it decides
only bodies in which every segment has a summary. But it cannot be stated until AI-7 gives a
resumable semantics (§2.1), and its passes and page must be modelled as §2.4 now says. The
first version called it "plausible and cheap"; that held only for the induction, not for the
objects it is about. Past that, the open question is the **coverage**.
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
| a token list given by the document (an argument) | `Arg i`, tokenized under the table `C_i` in force when the engine scanned it (§2.1), with its **length** as a `Sym` and a set of **shape predicates** the kernel will check (empty, a space, contains `\nocorr` at depth 0, its first token's class, …); a **copy** of it stored for later execution is `Copy(Arg i, C_i)` (§2.2) | the run never expands `Arg i`: reaching it on the input stack ends the current transformer at a **hole**; a `Copy` is executed where it is expanded (a shipout, an `.aux` read), by that segment's summary |
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
- **The output routine: per-state summaries, not a per-configuration obligation.** The first
  version proved "page safety" once per configuration and let every segment assume it. That is
  unsound (§2.4: `\thepage` redefined in the body; a `\label` argument re-read from the `.aux`).
  Instead:
  - `build_page`, `fire_up` and the real output routine (LaTeX's `\@outputpage`, the class's
    and packages' patches) are summarised like any segment, **from the abstract state at the
    point where they may fire**, and keyed by their read set. That read set includes the
    macros the head and foot expand (`\thepage`, `\@oddfoot`, `\leftmark`), the counters, and
    the token lists of every whatsit on the page, among them the `Copy` lists of §2.2;
  - a segment summary that may fire the output routine carries a guard "the page fills here"
    (decided by the page observers, else a fork) and composes with the output routine's summary
    looked up at that state; there is no assumption proved once;
  - the `.aux` lines written at shipout are an abstract aux content, read back at
    `\end{document}` and at the next pass's `\begin{document}` as segments (§2.4).
- **Node-list traversal is a research-grade unknown of its own (review M5).** The first version
  treated node lists as opaque with observers and said nothing of the code that **walks** them.
  Every paragraph end runs `line_break` (Knuth–Plass over the whole paragraph's node list), and
  then `post_line_break`, `hpack` of each line and `append_to_vlist`, which reads `prev_depth`;
  math runs `mlist_to_hlist`; boxes run `hpack`/`vpack`; the page runs `build_page` and
  `fire_up`. These loop over the list's nodes, branch on their kinds and dimensions, and
  allocate. On an opaque list each of them is `Stuck(layout)`, so **without a proven
  shape-and-interval abstraction of Knuth–Plass and of packaging, every paragraph end is
  `Stuck`**, and so is every document. That abstraction needs:
  - a shape domain for node lists (sequences of node kinds with interval-valued widths, glue
    and penalties, of symbolic length);
  - a sound abstract `line_break`: the set of feasible breaks and the resulting line count,
    badness classes and `prev_depth` as intervals or a bounded disjunction, proved against the
    translated procedure (it reaches no error site; overfull and underfull lines are warnings);
  - the same for `hpack`/`vpack` (which can raise only warnings, except through dimension
    overflow) and for `mlist_to_hlist`;
  - and enough precision that the code after them is not `Stuck`.
  It has its own milestone and KILL (AI-9, §8) and a cheap discriminator before it (AI-0b).
- **The first version admits no floats, no marks, no `\vsplit` (hence no `multicol`) and no
  inserts other than footnotes**: those are `Stuck(page)`. This is a coverage limit, not a
  soundness hole, and it is large. **Measured on sample 2** [M: `ai/tools/coverage_ceiling.py`,
  `ai/evidence/census/sample2-coverage-ceiling.txt`]:

  | the paper's own `.tex` files use | papers (of 200) | `article` papers (of 95) |
  |---|---|---|
  | a float (`figure`, `table`, `algorithm`, rotating's and sidecap's floats, `listing`, starred forms, `\marginpar`, `\newfloat`, `\DeclareFloatingEnvironment`) | **168** | **89** |
  | marks (`\markboth`, `\markright`, `\mark`, `\marks`, `\leftmark`, `\rightmark`, `\topmark`/`\firstmark`/`\botmark` and their e-TeX forms, `\…mark` hooks, `\pagestyle{headings/myheadings/fancy}`, `fancyhdr`) | 22 | 8 |
  | `multicol` or `\vsplit` | 14 | 8 |
  | **none of these** | **29 (14.5 %)** | **5 (2.5 % of 200)** |

  Method: the census's reading (every `.tex` of each paper at `regrade_sample.py`'s corpus path,
  comments stripped per line, the class from the first `\documentclass`), then one regex per
  row. The corpus copy was checked against sample 2's recorded `sha256_tree`: 200 of 200 match
  [M]. The screen sees only what a paper's `.tex` spells, so **"none" is an upper bound**:
  - 17 of the 29 are `amsart` and 2 `amsproc`, whose default page style puts
    `\leftmark`/`\rightmark` (that is, `\topmark`/`\botmark`) in the running heads (`amsart.cls`
    and `amsproc.cls` in the pinned image: `\ps@headings`, and `\pagestyle{headings}` at
    `amsart.cls` line 1914 and `amsproc.cls` line 1850) [R]. Counting the AMS classes' own marks leaves **10 of 200
    (5.0 %)**;
  - packages that patch the output routine (`longtable`, for one) or use inserts are not counted.

  So the first version's ceiling is **2.5 % (AI-4's `article`-only scope) to 14.5 %** of real
  papers, before any other cause of `Stuck`.
- `\pdfsavepos` positions are `Top` (ADR-014 §5.1's ±k sp mitigation is subsumed).

### 3.4 What makes an abstract run `Stuck` (outside the tier)

Everything that makes `exec` `Stuck` (E1: undefined behaviour, an unmodelled external, fuel), and
in addition:
- a branch, array index, `\ifcase` or `id_lookup` on a value the domain cannot narrow to ≤ K
  cases;
- an expanding read of the continuation, beyond a two-segment window;
- a read of an `Arg` other than as a hole, a declared shape predicate, or a copy stored as
  `Copy(Arg i, C_i)` for later execution (§2.2). Examples that stay `Stuck`: `\meaning` of an
  argument token, `\uppercase` of it. The copy is the third use: it is **not** `Stuck` (the
  first version made it so, and so made `\label` `Stuck` while AI-4 required it decided), but
  it is executed only where a summary of the executing segment (a shipout, an `.aux` read)
  covers it;
- a non-exact catcode at a boundary, or at the point where an argument is scanned;
- a point where the output routine may fire with no output-routine summary for the abstract
  state there (§3.3);
- any traversal of a node list (`line_break`, `hpack`, `vpack`, `mlist_to_hlist`,
  `build_page`) until AI-9's abstraction exists, so in the first version **every paragraph end
  and every box** (§3.3, review M5);
- a capacity whose peak the domain cannot bound below its limit;
- a pointer join that is `Top` and then dereferenced;
- any read through the allocator, the hash table or a stack/pool index while their
  abstractions (§4.3, §3.5) are not established for this run.

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

   **As stated, this scheme does not fit the code (review M4)** [R: tex.web]. It assumes every
   capacity is a counter that is only incremented and compared. Four of them are not:
   - **`get_avail`** (§120) takes the free list's head if it is non-null; otherwise it extends
     `mem_end`, or lowers `hi_mem_min`, and overflows when `hi_mem_min ≤ lo_mem_max`. Its
     overflow depends on the **free list** and on the **gap shared** with the variable-size
     region, not on a single counter `dyn_used`;
   - **`save_ptr`, `input_ptr` and `pool_ptr` are array indices**: `save_stack[save_ptr]`,
     `input_stack[input_ptr]`, `str_pool[pool_ptr]`. With `save_ptr = Sym v₀ + k`, every push
     writes, and every `unsave` reads, an address `v₀ + k`, so the read set's *locations* are
     symbolic. And `new_save_level` **copies** the value, `cur_boundary := save_ptr` (§274),
     which then rides in the store as a `v₀`-dependent value. Making those reads and writes
     position-independent needs a **relative-address abstraction** (stack frames addressed
     relative to the entry value), with its own refinement lemmas against the translated code:
     another research-grade obligation (AI-8);
   - **`hash_used`**'s change in `id_lookup` (§260) is a downward scan to the next empty slot:
     how far it moves depends on the table's **occupancy**, not on a constant;
   - **`max_param_stack`** is a **high-water mark** (§390: raised to `param_ptr + n`, then
     compared with `param_size`), so its entry value is a running maximum, and its "Δ" is not
     additive.

   So the per-counter `(peak_v, end_v)` form holds only for counters like `cur_level`; the others
   need, respectively, an allocator-state abstraction (AI-2's free lists plus the shared gap as
   one quantity), relative addressing (AI-8), an occupancy bound on the hash (AI-2), and a
   max-plus treatment of high-water marks (AI-5).
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

`exec#` records, on every explored path, everything it **reads**, with the abstract value it saw.

**The first version said "everything in `PS` reads through `read_loc`/`cell_at`, so this is one
instrumentation point". That is false (review M3)** [R: `Interp.v`, `Values.v`]. Reads that
bypass `cell_at`:
- the state's fields **`hp`** (the next heap block, read by `EAlloc` and `ERealloc`), **`fp`**
  (the frame pointer, read by `LLoc`/`LRef`) and **`fsp`** (the frame-stack pointer, read by
  `callp`);
- **`bsize`** of a block (`ERealloc` reads the old block's size, `bsize (hget st2 ob)`);
- **`st_io`**: the input (`io_in`), the clock (`io_clock`), the environment and the
  kpathsea/file-system model, and `io_char_signed`, which `read_loc` itself consults.

And writes that bypass `put_cell`: **whole-block writes** through `hput` (allocation installs a
new block; `ERealloc` installs one and empties the old; `callp` installs and clears frames) and
**output** (`emit`/`out_append` through `set_io`). Counterexample to the lemma as stated: two
states that agree on every cell but differ in `hp` diverge at the first `xrealloc_array`,
which allocates block `hp`; both runs read the same cells, and the lemma would have called
them equivalent.

So the observation set is **every cell read through `cell_at`, plus `hp`, `fp`, `fsp`, every
`bsize` consulted, and every field of `st_io` consulted**, and there are two lemmas:
- a **read-frame** lemma (below): agreement on the observation set gives the same path;
- a separate **write-frame** property: the final state differs from the initial one only at
  the recorded write set, which includes the cells written by `put_cell`, every block replaced
  by `hput`, the changes to `hp`/`fp`/`fsp`, and the output appended to `st_io`.

The summary is then stored under the key

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

Here `R` is the observation set just defined, not only `cell_at` locations. Its proof is the
usual "first divergence" induction on the fuelled interpreter. The two runs observe the same
values, so they take the same path. They write the same values, by the write-frame property.
They differ only in what neither run observed, and that keeps its old, differing values. The
read set is **adaptive**: what is read depends on earlier reads. That is fine, because the lemma
follows one path.

The abstract version (`exec#`, path sets, abstract values) follows from `abstract_sound` and
this lemma. So:
- **reuse adds no premise**;
- `Post` needs to state only what the run **wrote** (the write set above, whole blocks and
  output included); everything else is unchanged by the write-frame property. That is why "what a use leaves behind" (C-90) cannot be omitted from a summary
  (§2.5).

### 4.2 Why ADR-013's footprint premise P-1 broke, and why this key does not have it

ADR-013 keyed reuse by a **footprint** computed by a *static analyser of TeX macro text*. Its I1
and I2 instruments walked a name's `\meaning` closure and classified every read (§2.7 and §4.3
of that draft). Its soundness premise P-1 was "the censuses are complete". That premise was
broken twice, after publication, in the instrument that the footprint rested on (both rows are in
PROJECT_STATE on `origin/feat/v27165-strict-args` only):
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
| reads inferred from `\meaning` text, by regex | reads **observed** by the interpreter: every `cell_at`, plus the `hp`/`fp`/`fsp` fields, block sizes and the I/O record (§4.1), which together are every way `exec` can depend on its state; the first version named `read_loc` alone, which is not (C-152) |
| over the TeX-level closure; `\csname`-built names invisible | at the memory-cell level; a `\csname` lookup reads the hash cells it probes and the `eqtb` entry it finds, whatever the name |
| a walk that can *end* on an unreadable name (C-96: silently) | an abstract run that cannot classify something is `Stuck`; there is no "end of walk" |
| completeness of the analyser is a premise (P-1) | the frame lemma is a **theorem about `PS`** (§4.1), and the run is the engine's own code under `abstract_sound` |
| one representative probe per cell (P-4) | no probes; arguments are holes or shape predicates checked by the kernel |

The remaining premise is the old one: `FaithfulEngine`. Its attestation is the H.4/H.6
co-simulation.

### 4.3 The first unknown: addresses and hash slots (AI-2)

*The first version called this "the deciding unknown". It is one of at least four (§0, §9); the
others are the resumable semantics (§2.1, AI-7), relative addressing of the stacks and the pool
(§3.5, AI-8), and the node-list abstraction (§3.3, AI-9).*

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
    a computation over one store, and it can be checked on the 20 configurations of AI-0a.
  - Each summary's abstract run must **preserve** `I_heap` *for the cells it touches*: it frees
    only nodes it owns or that the precondition gives it, and allocates only through the
    abstracted allocator. The checks are made during the run, with a separation-style footprint.
    A run that cannot show preservation is `Stuck(heap)`.
  - The composition theorem then carries `I_heap` along the fold as an invariant.

  This is shape analysis per summary, not a whole-program proof. The first version called it
  the **largest and riskiest item of the whole plan**; AI-9 (the node-list abstraction) is at
  least its equal, and nothing measured yet ranks them.

If AI-2 fails, the key falls back to K1, and §6's cost model shows that the static path then does
not beat running the model. That is why AI-2 carries one of the architecture's KILL criteria (§8.3); AI-7 and AI-9 carry the
others.

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
- **Vendored classes.** A review asked this revision to adopt the record's **41** papers that ship
  their own class (STRICT_TIER_DESIGN §B.1). Re-measured on the verified corpus, no count gives 41
  [M: `ai/evidence/census/cls.txt`]: **42** papers ship a `.cls`, and in all 42 the toplevel's
  `\documentclass` names a `.cls` next to it, which kpathsea finds before TeX Live's; 4 of the 42
  are byte-identical to TeX Live's `IEEEtran.cls`, so **38** load class code that is not TeX
  Live's; 19 name a class TeX Live does not have. The difference from 41 is unexplained and is
  left open in OPEN-129; every figure below uses the measured counts. 50 papers ship a `.sty`. Of
  the 76 distinct vendored files, 15 are shared by more than one paper (conference styles).
- **Reuse, as a crude two-sided estimate** [M on the regex instrument; what it means for the hit
  rate is I]. "Papers that share an `\emph`-relevant signature with an earlier paper" depends on
  the key (`census.py`'s last lines):

  | key | distinct | papers sharing with an earlier one |
  |---|---|---|
  | A: class (any vendored class as one value), the 39 font/encoding/emphasis packages, whether a `.sty` is vendored | 57 | **143** |
  | B: class, the 39 packages, the vendored files' content hashes (the first version's key) | 101 | 99 |
  | F: B + the class's size option (`\emph` reads `\f@size`) | 117 | 83 |
  | H: F + those packages' options (`fontenc`'s encoding) | 119 | **81** |
  | G: B + every class option (splits on options `\emph` never reads) | 145 | 55 |

  The first version quoted B's 99 alone. **81–143 of 200** is the honest range for keys that
  track what `\emph` reads (G over-splits, so 55 is not a bound). The real read set is finer than
  every one of these keys (below), so even 81 is not a lower bound on misses.

What this supports [I]:
- **For a kernel command whose read set touches only font and NFSS state (`\emph`)**, a warm cache
  serves *at most* about 40–70 % of new papers (81–143 of 200), about half on the first
  version's key. The bound is an upper one: the real read set is
  finer than the signature. It includes the `selectfont` hook's contents, which any package may
  extend; `\everypar`, through LaTeX's paragraph hooks; and `\nocorrlist`.
- **For commands that read class code** (`\section` through `\@startsection`'s parameters,
  `\maketitle`, list environments), every paper with a vendored class (42 of 200, ≈ 1 in 5) is a miss unless another paper vendors
  the same bytes. So
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
It needs abstract read sets, so it cannot be done before AI-3. **But its upper bound can be
measured cheaply and first** (AI-0a, §8): a *concrete* run instrumented to record its
observation set (§4.1) gives, for a command in each of ≈ 20 configurations, the cells and values
it actually reads. If concrete read sets, with the allocator, hash and stack-offset cells masked
(that is, assuming AI-2 and AI-8 succeed), already differ across most configurations, no
abstraction can make them agree, and AI-6 cannot pass. That costs days, not the 5,000–18,000
CPU-hours of populating AI-6's cache (§6.3).

## 5. Question 4: the body-start state

The fold needs `a₀ ⊒` the concrete state at body start, and in fact needs it *before* the
`.aux` is read (§2.4). ADR-015 never says how this state is obtained (re-audit premise 10b). There
are two candidates.

### 5.1 M: a model run of the preamble (engine-free)

Run `exec` on the preamble, from the format load to the checkpoint before `\begin{document}`
reads the `.aux`. Marshal the store once per (preamble bytes, files read, environment class),
as ADR-014 §7.2 proposed.

- **Cost** [I, from measured rates]. The pinned pdfTeX takes 0.2–2.3 s for a real configuration's
  trace run (ADR-013 draft B.3 [R]); 0.112 s of that is the binary's start-up and format load
  (its median at 0 names, H5-heap-design.md §3.2 [R]), so 0.09–2.2 s is package and preamble
  work. The model's cost is its format load plus that work at the **marginal** rate (the first
  version priced it at a format-load ratio, 315×, whose 35 s basis no committed artefact holds):
  - **variant A** (T1, T2; ≈ 1,540× marginal, 59× load ≈ 6.6 s): ≈ 2.4 minutes to ≈ 57 minutes
    per configuration;
  - **the B2 model build** (≈ 2.2 × 10⁴× marginal; load 70.4–73.6 s user CPU in this branch's
    three kept runs, at load averages 16–25 [M: `ai/evidence/model/*/model-time.txt`]): ≈ 34
    minutes to ≈ 13.5 hours.

  So **≈ 2.5 minutes to ≈ 13.5 hours** per configuration. Which rate applies to package code is
  unmeasured: H.5's marginal rates are measured on the meaning dump, a proxy.
- **Prerequisites:** the C boundary for everything a preamble does. That means kpathsea file
  lookup and `\input` of `.cls`/`.sty`/`.cfg`/`.def`/`.fd` files, TFM loading, `\openin`, the
  `.aux` write, and PDF-side state that packages set up (hyperref's `\pdfcatalog` entries,
  `\pdfobj`). None is modelled today (§1).
- **What it gives for free:** preamble failures are decided exactly as **PROVEN-NOT-READY**
  (ADR-014 §8.1's "preamble failures are decided"). `γ(a₀)` contains the real state **by
  theorem**: the store *is* the run's state. No new premise.
- **Its price is the first verdict on a new configuration**: minutes to ≈ 13 hours of CPU before any
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
- **Latency of the first verdict on a new configuration:** M takes ≈ 2.5 minutes to ≈ 13.5 hours of model CPU
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
| read-set recording: one insert into a persistent map per observation (§4.1) | reads dominate interpretation, and H.5 measured persistent-array work at 2 % of the CPU, so the map insert is a new cost of the same order as the read itself | 2–4× |
| path management: join checks at merge points, store comparison on touched cells | per merge, proportional to the cells written since the fork | 1.2–2× |
| **product** | | **≈ 5–20×** (range 3.6–24×) |

**The concrete model's rate for per-command work is its marginal rate**, not its format-load
ratio: ≈ 1,540× pdfTeX on H.5's variant A (with T1 and T2), ≈ 2.2 × 10⁴× on the B2 model build
(§1) [R; the B2 figure computed from H.5's single full dump]. The first version used ≈ 315×, a
*format-load* ratio, at the low end; that understated per-command cost by ≈ 5–70×.

Taking ≈ 1.2 µs per expansion for pdfTeX (0.4 s for ≈ 335k expansions of the 12-page paper,
which also covers its typesetting and PDF writing, ADR-014 §7.1 [R]), `\emph`'s first use
(**146 macro expansions, 55 assignments, 50 conditionals** and a font load, §7.3; the first
version used 66 and 28) is of the order of **0.2–1 ms** in pdfTeX [I: 146 × 1.2 µs ≈ 0.18 ms,
plus the assignments, conditionals and the TFM read]. One explored path of `exec#` therefore
takes **≈ 1.5 s to ≈ 7 minutes** [I: 0.2 ms × 1,540 × 5 ≈ 1.5 s, up to 1 ms × 2.2 × 10⁴ × 20 ≈
440 s]; the geometric middle is ≈ 26 s. The width of that range is the honest state of
knowledge.

**Measured here, by instructions retired, not CPU time** [M:
`ai/evidence/model/{model3,model0}/model-time.txt`]. The model's run of `\emph{x}` in format
state, up to the `Stuck` at the TFM open, retired **460.3 × 10⁹** instructions; a control run
that does only the format load and one `\font` command up to the same `Stuck` retired
**443.2 × 10⁹**. The difference, **≈ 17 × 10⁹ instructions**, is the model's cost of the part of
`\emph` it ran (§7.4: 110 expansions, 37 conditionals, and their trace output), less the control's
`\font` command. At the control's rate (443.2 × 10⁹ in 73.6 s, ≈ 6 × 10⁹ per second under load)
that is **≈ 2.8 s of CPU** [I], against ≈ 0.1–0.2 ms in pdfTeX for the same work [I]: of the order
of 10⁴×, consistent with the B2 build's marginal rate. The first version compared the two runs'
*user CPU* (73.1 s against 73.6 s, at load averages 16–25) and called the command's cost "below
the run-to-run noise"; the instruction counts in the same files resolve it. Two consequences
stand:
- **every summary computation must start from a marshalled snapshot**, never from a format load
  (≈ 70 s of the B2 build's CPU); that snapshot is not built (§1);
- the per-command figure has to be measured from a snapshot, by instructions retired (AI-1,
  AI-3).

### 6.3 Per summary, per paper, per keystroke [I]

- **Cases per summary.** `\emph`'s guards cross several things:
  - the mode (vertical, horizontal, math);
  - the follower class (`,`/`.` or other);
  - first use or not (the font is loaded or not);
  - the argument's shape (empty, a space, plain, `\nocorr` at either end).

  Not all combinations are distinct (in math mode the follower does not matter), so the estimate
  is **≈ 20–50 cases**, near the bound K = 64.
- **A summary costs** ≈ 20–50 × one path's cost: **≈ 30 s to ≈ 6 h**. The central estimate is
  **≈ 15 minutes** (the geometric middle of the path range, ≈ 26 s, times ≈ 35 cases) [I]. (The
  first version: ≈ 3 s to ≈ 3 h, central "a few minutes", on the 315× basis and the undercounted
  trace.)
- **A cold paper** has a median of 75 distinct control words and 12 environments in its body
  (ADR-013 draft §4.2 [R]). Each may need 2–4 distinct preconditions (contexts), so ≈ 200–350
  summaries, about **50–90 CPU-hours** at the central estimate (the full range runs from ≈ 2
  hours to ≈ 2,000 hours), plus the preamble run of §5.1. The first version said 12–20.
  Warm-cache hits divide this by at most ≈ 2 for font-level commands (§4.5: 81–143 of 200
  papers share a signature, an upper bound) and less for class- and hyperref-dependent ones:
  **≈ 25–45 CPU-hours per new paper at best** [I].
- **Against AI-6's pre-registered lines** (§8): PASS needs a warm hit rate ≥ 80 % and a median
  admission cost ≤ 2 CPU-hours; KILL fires below 50 % or above 24 CPU-hours. **On these central
  estimates both PASS lines fail: the hit rate is GRAY at best (an upper bound of ≈ 40–70 %),
  and the cost is past the KILL line.** On the first version's own
  basis (12–20 hours, halved by warm hits: ≈ 6–10 hours, and a hit rate of about one half), both
  PASS lines already failed; the first version said only that AI-6 was "at real risk".
- **Populating AI-6's cache** means admitting sample 1's 200 papers first: ≈ 200 × 50–90 ≈
  **10,000–18,000 CPU-hours** cold at the central estimate, or ≈ 5,000–9,000 if half of the
  segments hit summaries made for earlier papers of the same sample [I]. On the first version's
  basis a reviewer put it at 2,400–4,000 CPU-hours; either way it is a compute budget that must
  be granted before AI-6 can run, and it is why AI-0a (§8) comes first.
- **A keystroke with every summary cached** re-folds from the edit point:
  - per segment, one key lookup, and an agreement check over the read set, which is O(|R|) with
    |R| in the hundreds to thousands of cells;
  - in total, milliseconds to tens of milliseconds for a 40-page paper [I].

  So **real time is plausible on a hit, and impossible on a miss**: a miss means `PENDING` for
  ≈ 30 s to ≈ 6 hours per missing summary (≈ 15 minutes central).

For comparison: running the concrete model on the whole document (ADR-014's product, which D1
rejects for the keystroke path) costs the format load plus pdfTeX's ≈ 0.4 s of per-pass work
on the 12-page paper (already net of start-up, ADR-014 §7.1) at the marginal rate: ≈ 6.6 s +
0.4 s × 1,540 ≈ 10 minutes (variant A) to ≈ 72 s + 0.4 s × 2.2 × 10⁴ ≈ 2.5 hours (the B2 build)
per pass [I], and it needs no summaries.
(The first version: ≈ 2 minutes to 1.3 hours.) **The synthesis pays off only
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
- **146 macro expansions**: 66 printed with a backslash and **80 printed without one**, because
  `\define@newfont` sets `\escapechar` to −1 and the trace then prints every name bare
  (`font@name ->…`, `extract@font ->…`, `f@size ->10`). Counted as the lines that contain `->`
  and do not start with `{` or `#`: 146 [M];
- 55 assignments (49 `changing`, 3 `reassigning`, 3 `globally changing`), 3 of them **global**:
  - `\font@name`, by `\xdef`;
  - `\OT1/cmr/m/it/10` twice: first `\relax` by `\csname`, then `\font` by `\global\font`;
- **50 conditionals**: 28 printed with a backslash, 22 bare (`{if: …}`, `{ifdim: …}`, `{ifx: …}`
  under `\escapechar` −1), counted as the `{…: (level n) entered …}` lines [M];

  *The first version counted 66 expansions and 28 conditionals: its pattern required the
  backslash, so it missed every line printed while `\escapechar` was −1 (C-153).*
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

   Persisting writes at level 0: **8 writes to 5 cells**: `\@let@token`, `\ifmaybe@ic`,
   `\@fortmp` (once each), `\reserved@a` (three times), `\reserved@b` (twice) [M: the
   `changing` lines after `{leaving simple group (level 1)}`]. **Plus 3 global writes** made
   inside the group (`\font@name`; `\OT1/cmr/m/it/10` twice) and **the loaded font** (`font_ptr`,
   `font_info`). The first version's ledger row said "7 assignments persisting". These are exactly
   **what a use leaves behind** (C-90), and a later `\ifx\reserved@a…` anywhere in the body reads
   them.

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
- **What the prefix does *not* contain** (review F2) [M: `grep` of `model-terminal.txt` against
  `binary-terminal.txt`]: it executes **1 of the 3 `\futurelet`s** (`\@ifnextchar`'s, inside
  `\define@newfont`; the other two are `\maybe@ic`'s peeks at the argument and at the token after
  the group, which come after the font load); **no `\aftergroup`** (the text `\aftergroup` occurs
  only inside `\check@icr`'s definition, which is assigned, not run); **no hook** (`\UseHook`
  occurs only inside `\selectfont`'s printed body; `\hook_use:n` never runs: 0 lines in the
  model's output, 6 in the binary's). And it runs in **format state inside an `\hbox`**, not at
  `article`'s body start (§7.1). The first version's §0 and §7.6 said the model executed the
  `\futurelet`s, the `\aftergroup` and the hook; it executed none of the last two.
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
- Cost: 460.3 × 10⁹ instructions retired (73.1 s user CPU), peak 1,523 MB, against 443.2 × 10⁹
  (73.6 s) for `model0`: ≈ 17 × 10⁹ instructions for the part of `\emph` the model ran (§6.2) [M].

**So the TeX side of the model executes exactly every line of `\emph`'s real code that it
reaches, which is the part up to the font load, in format state. The first thing missing is the
C boundary (TFM file input), which is being built on another branch; the rest of the first use
(two `\futurelet`s, the `\aftergroup`, the hook, the italic correction) is unexercised in the
model.** No hand modelling of `\emph` was involved, which is ADR-015's premise working as
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
          level-L writes (8 writes, 5 cells): \ifmaybe@ic, \reserved@a, \reserved@b, \@fortmp,
          \@let@token;  [first use:] the loaded font cmti10 (font_ptr, font_info);
          list: + the argument's material + possibly a kern;
          Δ: cur_level peak +1 (+ the hole's); save_ptr peak +k, relative to the entry (AI-8);
             dyn_used: through get_avail, so the free list and the shared gap (§3.5, AI-2);
             fmem_ptr +…
  mode = vertical: \leavevmode first (new_graf, \everypar's paragraph hooks, build_page at the
                   outer level, §2.4) -> a separate case set, composed with the output
                   routine's summary at that state (§3.3)
  mode = math:     \nfss@text{\em #1} = {\mbox{…}}: a separate case set
```

Counting the cases gives the estimate of §6.3: the mode (3) × first use (2) × the argument's shape
(about 4) × the follower class (2, not in math), less the combinations that cannot occur, so
≈ 20–50.

### 7.6 Where the current machinery suffices, and exactly where it does not

| needed for `\emph`'s admission | exists? | evidence |
|---|---|---|
| the real definition, as pdfTeX holds it | **yes**: the format load is exact, and the meanings are identical to the binary's for all 23,519 names | H3 report [R]; §7.2 [M] |
| executing that definition exactly, up to the font load (expansion, groups, global and local assignments, `\csname`, `\ifcsname`, the delimited argument split, 1 of the 3 `\futurelet`s), in format state inside an `\hbox` | **yes**, up to the first external | §7.4: an 18,849-byte identical prefix [M] |
| the rest of the first use: `\maybe@ic`'s two `\futurelet`s, the `\aftergroup` and `unsave`, the `selectfont` hook, `\sw@slant` and the italic correction; and any of it at body start | **not exercised** in the model (it stops at the TFM open first) | §7.4 [M] |
| the TFM read on first use (`bopenin`, then the TFM bytes) | **no**: C boundary, parallel branch | §7.4 `Stuck` [M] |
| `pdfassert` on the path of a missing glyph | **no**: C boundary | §7.4 [M] |
| a body-start state (the `article` preamble, `\begin{document}`) | **no**: needs file input (C boundary) and a snapshot (not built) | §1, §5 |
| `exec#`, the abstract store, forks and joins | **no**: no code | §1 [R] |
| holes for `#1`, and guards on the argument's shape and first token | **no** | — |
| the symbolic continuation and the peek guard | **no** | — |
| the read-set recording and the frame lemma | **no** | — |
| the allocator and name-map abstraction (needed at steps 5, 6, 8) | **no**: one of the four research-grade unknowns | §4.3 (AI-2) |
| capacity Δs (font memory, `dyn_used` for the `\edef` copy) | **no**: the relational component of §3.5 (3) | — |
| output-routine summaries per state, needed if `\emph` starts a paragraph (`new_graf` calls `build_page`) | **no** | §2.4, §3.3 |
| a kernel that can consume such a summary | **no**: `Contract.signature` has two fields, `text_beh` and `math_beh` | `proofs/Strict/Contract.v` [R] |
| a resumable semantics to state `Sound` over (a boundary state is mid-`main_control`) | **no**: `Interp.v` is big-step and fuelled | §2.1 (AI-7) [R] |
| relative addressing for the save stack (the group's frame at `save_ptr`) | **no** | §3.5 (AI-8) |
| `hpack` of the box, `line_break` if `\emph` ends a paragraph, the output routine if it fills a page | **no**: node lists are opaque, and their traversal is `Stuck` | §3.3 (AI-9) |

The concrete foundation suffices for the part of `\emph` it reached. Everything specific to
admission is missing, including four research-grade abstractions: allocation and names (AI-2),
a resumable semantics (AI-7), relative addressing (AI-8), and node-list traversal (AI-9).

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
  - the fixed clock (E10/OPEN-128);
  - every model-side cost as **instructions retired** as well as CPU time, since CPU time on
    this machine moves with load (§6.2).

**Definitions, fixed now, that every PASS and KILL below uses** (the first version left them
open, review F6):
- **GRAY.** For a metric with a PASS line and a KILL line, a value strictly between them is
  GRAY. A GRAY milestone neither passes nor dies: the track **stops and reports**, and it
  continues only by a recorded owner decision that names the value accepted. GRAY never
  satisfies a later milestone's prerequisite.
- **Outside counts.** A paper or segment that is `Outside` stays in every denominator. In a body
  whose fold stops at its first `Outside` segment, every later segment occurrence counts as not
  served. A figure "over the papers in scope" may be reported beside, never instead.
- **A hit** is a segment occurrence of a sample-2 body for which the cache holds a summary
  computed while admitting **sample-1** papers, whose key agrees with the abstract state at the
  occurrence by §4.1's reuse rule. Summaries made for earlier sample-2 papers are reported
  separately and are not hits.
- **Admission cost per paper** is the CPU time and the instructions retired of every `summarize`
  call made while deciding that paper with the warm sample-1 cache, excluding the preamble run
  (reported separately); a paper that ends `Outside` counts with what it spent. Its **median** is
  over all 200 sample-2 papers.
- **An attempt** (AI-4's and AI-9's "2 attempts") is one written design, reviewed
  adversarially, implemented, and run to completion on the milestone's fixed set. A design
  abandoned before that run counts as an attempt.

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
| D-f | a **compute grant** for AI-6: admitting sample 1 cold is ≈ 10,000–18,000 CPU-hours at the central estimate (≈ 5,000–9,000 with intra-sample reuse), §6.3 | owner | AI-6 |
| D-g | the **H.1 reference build** with a change file that logs reads of the translated globals (as H.6's digest change file proposes), for AI-0a and AI-0b before D-a/D-b exist; a measurement instrument, not a proof | spike | AI-0a, AI-0b (or wait for D-a, D-b and use `exec`) |

### 8.2 First: three cheap discriminators (owner's choice, 2026-10-06: "cheap tests first")

**The owner has chosen "cheap tests first"**: before any milestone of §8.3 is funded, the three
discriminators below run, each with its KILL line fixed here in advance. Their dependencies:
- **AI-0a needs the C boundary (D-a)**: the 20 configurations' packages, `.cls`, `.fd` and TFM
  files must load in the instrumented run, and `exec` cannot read files today (§7.4). It also
  needs D-b (a snapshot at body start). D-g (the H.1 reference build with a read-logging change
  file) can stand in as the instrument, as a measurement, not a proof;
- **AI-0b probably needs the C boundary too**: its paragraphs' node lists come from real
  configurations' fonts (TFM widths), so a dump from `exec` needs D-a; D-g can supply them
  earlier;
- **AI-0c needs only the oracle** (`_oracle.py`) and Coq; it can start now.

The first version started with AI-1 and AI-2, ≈ 8–18 agent-weeks of proof before any evidence
on reuse or layout. Each discriminator below can kill the architecture for a fraction of that,
and none needs `exec#`. They run first, in parallel; **any KILL stops the track** and the report
recommends ADR-014's product (deciding by executing the document asynchronously). Effort is
[I, uncalibrated] (§8.4).

| id | what | PASS (all of) | KILL (any of) | effort [I] |
|---|---|---|---|---|
| **AI-0a** | **Cross-configuration read-set reuse probe** (review F7). A *concrete* run instrumented to record the observation set of §4.1 (every `cell_at`, plus `hp`/`fp`/`fsp`, block sizes, the I/O fields read) for one occurrence of each of 10 commands fixed now: `\emph{x}`, `\textbf{x}`, `$x+1$`, `\cite{k}`, `\ref{k}`, `\label{k}`, `\section{T}`, `\item` (in `itemize`), `\footnote{x}`, and a paragraph end; at the body start of **20 configurations** (the 20 most frequent (class, `\emph`-relevant packages) signatures of sample 1, unsealed, chosen by `census.py` before the run). Then the same with the allocator cells, the hash-probe slots (replaced by the names they hold) and the stack offsets (made relative to the entry value) **masked**, i.e. assuming AI-2 and AI-8 succeed. Instrument: `exec` once D-a and D-b exist, else D-g. Metric per command `c`: `s_c`, the fraction of the 20 configurations whose masked (location, value) set equals that of at least one other; and whether a second occurrence of `c` at another position of the same document has the same masked set | median over the 10 commands of `s_c` ≥ 0.8; and same-document sharing for ≥ 9 of the 10 | median `s_c` < 0.5 (AI-6's hit rate cannot reach its PASS line even with perfect abstractions); or same-document sharing for < 5 of the 10 *with* masking (the masking assumed by AI-2/AI-8 is not enough) | 1–3 |
| **AI-0b** | **Feasibility of a sound `line_break`/`hpack` abstraction** (review M5). An *unverified* prototype of the shape-and-interval abstraction of §3.3 (`line_break`, `post_line_break`, `hpack`, `append_to_vlist`), run on 100 paragraphs drawn now (fixed seed) from sample-1 bodies, whose concrete node lists are dumped at each `line_break` call (D-g or `exec`). Each paragraph is abstracted as a summary would see it: every box width that came from an argument becomes an interval ±10 %, and each argument's word count a symbolic range [1, 3×]. The prototype's per-paragraph outcome is checked against the concrete trace: (a) no error site is reachable; (b) every value the following code reads (`prev_depth`, the line count, the last node's kind, `\lastskip`/`\lastpenalty`) is produced with ≤ K = 64 disjuncts and is not `Top` | ≥ 90 of 100 paragraphs satisfy (a) and (b) | < 50 of 100 (no reusable summary crosses a paragraph end, so every summary is position-specific and the static path cannot beat executing the document) | 2–4 |
| **AI-0c** | **The multi-pass and output-routine treatment** (reviews H1, H2, M2). (1) The Coq **statements** (no proofs) of `decide` with the protocol's retry loop and per-pass start states (§2.3), `BndTok` and the tokenization-time table (§2.1), `Copy` arguments (§2.2), and output-routine summaries keyed by read set (§2.4, §3.3), over `Interp.v`'s types with `step*` as a parameter; (2) a witness battery fixed now: the 6 documents of `ai/evidence/witnesses/` plus ≥ 40 generated variants (convergence after 1, 2 and 3 passes via `\immediate\write` to the `.aux`; the oscillating aux of ADR-013 D-1; `\thepage`, `\@oddfoot`, `\markboth` redefined in the body; `\label`/`\ref`/`\pageref` with `\protect`ed undefined commands; `\catcode` changes inside the arguments of `\emph`, `\textbf`, `\label`), each graded through `_oracle.py`; (3) the designed judgement applied by hand to each, giving READY, NOT-READY or Outside | the statements typecheck; **0** contradictions with the oracle on the battery; every witness class has a non-`Outside` treatment for its simplest member | a witness class whose only sound treatment is `Outside` for every document that ships a page (the output routine cannot be summarised per state without concrete layout) | 1–2 |

**Decision point 1: the end of AI-0a, AI-0b and AI-0c (≈ 4–9 agent-weeks [I]).** PASS on all
three opens §8.3. Any KILL stops the track. Any GRAY stops it for an owner decision.

### 8.3 Then: the research milestones, each with its own KILL

Four of these (AI-2, AI-7, AI-8, AI-9) are the research-grade unknowns of §0. Their order is by
dependency: AI-7 first (nothing can be stated without it), then AI-1, AI-2 and AI-8 (the
abstract interpreter and its address abstractions), AI-9 in parallel (it needs AI-7 and AI-1's
domain), then AI-3 to AI-6.

| id | work | PASS (all of) | KILL (any of) | effort [I] |
|---|---|---|---|---|
| **AI-7** | **A resumable semantics** (review M1, §2.1): a small-step or continuation form of `exec`, or a proved decomposition of `main_control`'s loop into "one iteration from a store at the loop head"; its agreement with `exec`; `Protocol` restated with ∃ fuel and a fuel-monotonicity lemma | (a) the agreement theorem and fuel monotonicity closed, `Print Assumptions` = the kernel primitives only; (b) the extracted resumable interpreter gives `exec`'s outcome and byte-identical output on all 178 H.2 differential inputs; (c) it can be stopped at a segment boundary of a real body and resumed from the marshalled state with an identical result | (a) not closed within 12 agent-weeks; or (c) impossible without state outside the store (then a boundary state is not a store, and summaries cannot be keyed by one) | 4–12 |
| **AI-1** | `exec#` over `PS` (as AI-7 makes it resumable): the abstract store of §3.1; forks, joins and widening (§3.2); recording of the **observation and write sets of §4.1** (not only `cell_at`); the relational component for argument scans (§3.5 (3)). Proofs: `abstract_sound` against AI-7's semantics, the read-frame lemma and the write-frame property. Extraction | (a) the theorems closed, `Print Assumptions` = the kernel primitives only; (b) the extracted build within H.2's limits (< 2 h compile, < 16 GB); (c) with an all-`Exact` initial state, `exec#` gives `exec`'s outcome and byte-identical output on the 178 H.2 differential inputs and on the 50-name meaning prefix; (d) on (c), `exec#`'s instructions retired ≤ 20× `exec`'s | a theorem not closed within 8 agent-weeks; (b) fails; (d) > 100× | 4–8 |
| **AI-2** | the allocator and name-map abstraction, route K3 (§4.3): refinement lemmas for the translated `get_avail`, `get_node`, `free_node`, `flush_list`, `id_lookup` and `make_string` under `I_heap`; the free lists **and the gap shared by the two regions** as one abstract quantity (§3.5); an occupancy bound for `hash_used`; a verified checker of `I_heap`; per-run preservation checks in `exec#` | (a) the lemmas closed; (b) the checker accepts the format state and the pre-`.aux` states of AI-0a's 20 configurations; (c) two uses of `\emph{x}` at different positions of one document **share one summary**, checked on the model | `I_heap` is false on the real format state and cannot be repaired by restating it within 2 attempts; or the lemmas are not closed within 10 agent-weeks. The key then falls back to K1 and the static path costs more than executing the document | 4–10 |
| **AI-8** | **Relative addressing** of the save stack, the input stack, the parameter stack and the string pool (review M4, §3.5): addresses relative to the entry value, with refinement lemmas for the translated `new_save_level`/`unsave`, `begin_token_list`/`end_token_list`, `str_room`/`make_string`, and the copy `cur_boundary := save_ptr`; the high-water-mark form for `max_param_stack` | (a) the lemmas closed; (b) two uses of `\emph{x}` at **different group depths** share one summary; (c) AI-0a's 10 commands, with these offsets abstracted, need no position-specific case | not closed within 8 agent-weeks; or a construct in ≥ 10 % of AI-0a's command occurrences reads a stack value absolutely (a `\ifnum\currentgrouplevel`-style read that cannot be made relative) | 3–8 |
| **AI-9** | **The node-list and layout abstraction** (review M5, §3.3): the shape domain; abstract `line_break` (with `post_line_break`), `hpack`, `vpack`, `mlist_to_hlist`, `append_to_vlist`, `build_page` and `fire_up`, each proved sound against the translated procedure | (a) the soundness lemmas closed; (b) on AI-0b's 100 paragraphs, the **proved** abstraction meets AI-0b's PASS figures (≥ 90 of 100) | the proved version stays below 50 of 100 after 2 attempts; or the lemmas are not closed within 20 agent-weeks | 8–30 |
| **AI-3** | `\emph` end to end at `article`'s body start; the **new static kernel's** first version (a contract type for guarded summaries with holes and `Copy` arguments, `fold` over both boundary forms, capacity checks, `decide` with the retry loop, the bridge `static_ready_iff_pdflatex`) | (a) `summarize` produces `\emph`'s summary with **no per-command input**, with ≤ K cases, in ≤ 1 CPU-hour from a snapshot; (b) the kernel's verdict agrees with the oracle **and** with the concrete model on 100 % of a generated set of ≥ 2,000 documents, fixed before the run, that varies the start mode; the argument (empty, a space, letters, `\nocorr` first or last, nested `\emph`, `\textbf`, braces, a `\catcode` change, 0 to 20,000 tokens); the follower (`,` `.` a letter, a space, `\par`, `\/`, `\relax`, a macro that expands to `,`); nesting from 1 to past the grouping limit; repetition ×300; (c) 0 false READY and 0 false NOT-READY; every Outside counted (in the denominator) and explained | a false READY or false NOT-READY caused by the *method* (the stop rule applies first); or `\emph` `Stuck` for domain reasons after 3 domain refinements; or > 64 cases; or > 10 CPU-hours | 4–8 |
| **AI-4** | the page and the passes: per-state output-routine summaries (§3.3) for float-free `article`; deferred `\write` and `Copy` arguments at shipout; the `.aux` cycle with abstract page numbers and the retry loop (§2.4) | `\label`/`\ref`/`\pageref` decided right (READY or NOT-READY as the oracle says, or Outside, counted) on a generated set fixed now that includes AI-0c's battery, the 27th-`enumii` case (ADR-015's composition cases) and the oscillating aux of ADR-013 D-1; 0 false verdicts | per-state output-routine summaries for float-free `article` need concrete node lists after 2 attempts | 4–8 |
| **AI-5** | capacities (§3.5): the enumerated `overflow` sites, each classified as an additive Δ, a high-water mark, an allocator-state bound (AI-2), a relative offset (AI-8), or unreachable; the main-memory fragmentation lemma | (a) every `overflow` site is classified; (b) the C-86 witness and the C-94/C-98 witnesses and maximisers (the latter on `origin/feat/v27165-strict-args`), re-run on the new kernel, are each decided NOT-READY with the right message or Outside, **never READY**, with every bound recomputed by the gate from the summaries' Δ | no sound bound for main memory's variable-size region with margin ≥ 2 on the bodies of the 200 sample-2 papers | 2–4 |
| **AI-6** | coverage and reuse on the unsealed frame, with §8's definitions (Outside in the denominator; a hit is a sample-1 summary; the cost is per paper, median over 200) | thresholds, **fixed now**: (a) the warm-cache hit rate over all of sample 2's segment occurrences ≥ 80 %; (b) the median admission cost per new paper ≤ 2 CPU-hours (the preamble run reported separately); (c) ≥ 1 real paper PROVEN-READY end to end; 0 false verdicts on the frame | hit rate < 50 %, or median admission cost > 24 CPU-hours. Between the lines: GRAY (§8). **On this report's own central estimates (§6.3) the hit rate is at most ≈ 40–70 % and the cost ≈ 25–45 CPU-hours: GRAY on (a) at best, KILL on (b).** It needs D-f's compute grant | 2–4 (plus D-f) |

**Decision point 2: the end of AI-7, AI-1 and AI-2.** If they have not all passed within 30
agent-weeks of AI-7's start, the track stops and reports as if AI-2's KILL had fired.
**Decision point 3: AI-9.** If AI-9 has not passed within 30 agent-weeks of its start, the
track stops: without it every paragraph end is `Stuck`.

### 8.4 The basis of the estimates, and why they are uncalibrated

- **Totals [I, uncalibrated]:** the discriminators ≈ 4–9 agent-weeks; the research milestones
  AI-7, AI-1, AI-2, AI-8, AI-9 ≈ 23–68; AI-3 to AI-6 ≈ 12–24. **About 40–100 agent-weeks in
  all**, against the first version's 20–42, plus ≈ 5,000–18,000 CPU-hours for AI-6 (D-f), plus
  the prerequisites D-a and D-b (ADR-014 §8.1 put its C boundary stage G2 at 4–8 agent-weeks
  and its end-to-end stage G4 at 6–10).
- **These figures are not calibrated, and the record says how badly such figures miss.** The
  project's last [I] estimate of this kind, ADR-014 §7.1's model speed of 10–60× pdfTeX, was
  measured at ≈ 315–11,700× on the figures the first version used, a miss of **≈ 5–200×**; on
  H.5's marginal rates (≈ 1,540× and ≈ 2.2 × 10⁴×) the miss is ≈ 26–370×. In the other
  direction, H.2 (the translator, `PS`, the INITEX boundary and extraction) took ≈ 2 days of
  agent work against the draft's 4 [R: H2 report checkpoints 2026-09-30 to 2026-10-01], but it
  was mechanical translation with no proof beyond typing. The H.5 heap fix needed a 5-day box
  (E11 in H5-heap-design) for a performance change proved by reflexivity. **Nothing on record
  is a proof of the size of `abstract_sound`, AI-2's lemmas, AI-7's agreement theorem or AI-9's
  abstract `line_break`.**
- **Outside the project** [U, recalled, not checked here]: Verasco, the verified static analyser
  for CompCert's C, was a multi-person-year effort. Its domains were numeric; this one adds
  symbolic token streams, a heap abstraction, relative stack addressing and a layout domain.
- **So** the discriminators are the only figures here that the plan relies on, and they are
  first for that reason: they buy evidence on the two questions (reuse, layout) that decide
  whether the 40–100 weeks are worth spending, before any of it is spent.

## 9. Question 8: the verdict

**RESEARCH PROGRAMME WITH AT LEAST FOUR RESEARCH-GRADE UNKNOWNS (AI-2 allocator/name map; M1
resumable semantics; M4 stack/pool relative addressing; M5 node-list and layout abstraction);
first-version coverage ceiling 2.5–15 % of real papers.**

The first version's verdict, "FEASIBLE WITH CONDITIONS", is withdrawn (C-152). It rested on one
deciding unknown, a composition theorem it called cheap, a page treatment it called sound, and
cost figures that understated the model's per-command rate; two adversarial reviews refuted each.

**What held: the safety principle.**
1. **`Stuck` is outside the tier, never a guess.** Every case the design cannot settle is
   excluded, never approximated (the owner's rule). The reviews found no case where the design,
   *as corrected*, would have to guess; every error they found was an unsound or ill-formed
   statement of the judgement, which the corrections replace with an exact one or with `Stuck`.
2. **Reuse is keyed by the read set the run itself observes**, with a frame lemma proved once
   for `PS` (§4.1, now over the full observation set and with a separate write-frame property),
   never by a TeX-level analyser. The failure classes of the stopped signature track are still
   closed by construction, not by vigilance:
   - C-84/C-85 (look-ahead, transparent followers) become derived peek guards;
   - C-90 (what a use leaves behind) is the write-frame property;
   - C-92/C-96 (the closure walk; on `origin/feat/v27165-strict-args`) become observed read sets;
   - C-94/C-98 (capacity proxies, multiplicative copies; same branch) become the engine's own
     counters, with §3.5's corrected forms.
3. **The foundation executes real format code exactly as far as it reaches** (§7.4): `\emph` up
   to its font load, in format state, with no `\emph`-specific work.

**What did not hold.**
1. **Four research-grade unknowns, not one** (§0): AI-2 (allocator and hash), AI-7 (a resumable
   semantics: there is no `step*`, and fuel grows with the document), AI-8 (relative addressing
   of the stacks and the pool), AI-9 (node-list traversal: without it every paragraph end is
   `Stuck`). None is built; nothing on record is a proof of their size.
2. **The judgement as first stated was unsound or ill-formed in five places**, each now corrected
   in §2–§4: the decider did not model the protocol's retry loop (a false NOT-READY, witnessed);
   page safety per configuration (false READYs, witnessed twice); a hole re-cut under the
   updated catcode table (a false READY, witnessed); a frame lemma that missed the reads and
   writes outside `cell_at`/`put_cell` (a counterexample through `hp`); a capacity scheme that
   does not fit `get_avail`, the stack indices, `hash_used` or a high-water mark.
3. **The coverage ceiling.** The first version is `Stuck` on floats, marks, `\vsplit` and
   multicolumn output. On sample 2 only **29 of 200 papers (14.5 %)** use none of them, **10
   (5.0 %)** once the AMS classes' own running-head marks are counted, and **5 (2.5 %)** on
   AI-4's `article`-only scope; 168 of 200 use floats (§3.3) [M, regex; upper bounds].
4. **AI-6 fails both PASS lines on this report's own central estimates** (§6.3): a hit rate of at
   most ≈ 40–70 % (GRAY at best) and an admission cost of ≈ 25–45 CPU-hours per new paper with
   warm reuse (past the 24-hour KILL line). The first version's own basis already failed both
   PASS lines, and it said only that AI-6 was "at real risk".

**What the owner decided, and is asked** (OPEN-129):
1. **Decided 2026-10-06: "cheap tests first".** The three discriminators (AI-0a, AI-0b, AI-0c;
   ≈ 4–9 agent-weeks [I, uncalibrated]) run before any milestone is funded, each with the KILL
   line of §8.2. AI-0a, and probably AI-0b, wait for the C boundary (D-a) unless D-g is built.
2. Rule on O1.2 (§5.2), or accept a first verdict per new configuration of ≈ 2.5 minutes to
   ≈ 13.5 hours of model CPU (§5.1).
3. Accept, or not, a first tier whose ceiling is 2.5–15 % of real papers.
4. Note D-f: AI-6 alone needs ≈ 5,000–18,000 CPU-hours.

**What would make it NOT FEASIBLE:** any discriminator's KILL; AI-7's, AI-2's or AI-9's KILL;
AI-6's KILL; or a false PROVEN that traces to the method. Each leaves ADR-014's product,
deciding by executing the document asynchronously, as the engine-free option. It needs none of
this machinery, at the cost of D1's "real time".

**ADR-014 §8.3 put symbolic execution of `latex.ltx` "out of scope"; ADR-015 D2 made it the
admission mechanism without scoping it. This report is that scoping. Its main finding, as
revised: the hard part is not TeX's macro language but TeX's *machine*. Its memory (allocation,
the hash table, the stacks), its control (a big-step interpreter with no resumable state), and
its layout (node lists walked by `line_break` and the page builder) each need a proved
abstraction before any summary can be reused, and the design's own exclusions leave at most
2.5–15 % of real papers in its first tier.**

## 10. What this report did not do, and the record

- **Nothing was built.** No `exec#`, no domain, no kernel change. The runs are: the trace of §7
  (three model runs kept: `model0`, `model1`, `model3`; one more described in §7.4 and not
  kept), one body-start trace, one meaning walk, one corpus census and, in the revision, the
  coverage screen (§3.3) and the six witness documents of §2.1/§2.4 (`ai/evidence/witnesses/`).
  Every speed figure for the abstract interpreter is [I].
- **The corpus.** The census and the coverage screen read the arXiv corpus at
  `scripts/tools/regrade_sample.py`'s `CORP` path, at the paper ids of
  `corpora/real_roots/results_sample2.json`. The revision recomputed every paper's
  `sha256_tree` with `diff_real_roots.sha256_tree`: **200 of 200 match** the recorded values
  [M], so the copy is the graded trees. (The first version had not checked this.)
- **The witnesses** ran in the pinned image (`texlive/texlive@sha256:4984977c…`, arm64, no
  network, `SOURCE_DATE_EPOCH=0`, `FORCE_SOURCE_DATE=1`), one short container per script, under
  `protocol.sh`, which restates `_oracle.run_to_fixpoint`'s loop with `pdflatex
  -interaction=nonstopmode -halt-on-error`; `context.sh` prints each first error's context.
  Recipe: `docker run --rm --platform linux/arm64 --network none -e SOURCE_DATE_EPOCH=0
  -e FORCE_SOURCE_DATE=1 -v "$PWD":/w:ro $IMG sh /w/protocol.sh > protocol-out.txt`, from
  `ai/evidence/witnesses/`. These are recipes, not grades.
- **No binary run went through `_oracle.py`.** These were reads of meanings, traces and witness
  outcomes, not grades, as in the H.3 README's recipes. Every grade from AI-0c onward goes
  through the oracle (§8).
- **Ids.** OPEN-129 is this scoping's ledger row (PROJECT_STATE on this branch). The reserved
  correction ids C-151 to C-159 were checked free on every remote and local branch and in every
  worktree on 2026-10-06, before the first version and again before this revision. The first
  version used none and said it "records no error of the project's that it found *and* that a
  C-row should own". The revision uses **C-152 to C-158** for the first version's own errors and
  the classes behind them:
  - **C-152**: the errors, item by item (soundness: H1, H2, M1–M5; evidence and cost: F1–F7, the
    census, the coverage ceiling, the C-row citations, the `\futurelet` levels);
  - **C-153**: counting trace events by their printed spelling (the `\escapechar` −1 lines);
  - **C-154**: lemma statements about `PS` written against an imagined interpreter (`step*`, a
    single read path, counters that are not indices);
  - **C-155**: the protocol restated in the decider without quoting its implementation;
  - **C-156**: an obligation proved once per configuration over state the body can change (page
    safety);
  - **C-157**: cost evidence mispriced and overstated (a format-load ratio for marginal work,
    CPU time under load instead of the instructions in the same file, a model "executing" what
    its output does not contain);
  - **C-158**: a verdict not checked against the report's own pre-registered lines and its own
    exclusions (AI-6's PASS lines, the coverage ceiling).
  C-151 and C-159 remain unused. The two facts stated against the record still go to the owner
  through OPEN-129: that ADR-014's `PS.Step`, closure compiler and `exec#` were never built
  (§1), and that ADR-015 D2 reverses ADR-014 §8.3 without scoping it.
- **One review instruction was not followed, and why.** Review 2 asked that the record's 41
  vendored classes be adopted. Re-measured on the verified corpus, 42 papers ship and load their
  own `.cls` (38 not byte-identical to TeX Live's) and no count gives 41 (§4.5). The measured
  figures are used, and the discrepancy is left open in OPEN-129.
