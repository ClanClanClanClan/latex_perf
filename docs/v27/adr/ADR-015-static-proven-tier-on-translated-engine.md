# ADR-015 — The proven tier is static, real-time and engine-free, built on a Coq translation of the pinned pdfTeX

**Status:** Accepted (2026-09-29). **Deciders:** maintainer (owner).
**Extends:** ADR-012 (its goals, verdict type, oracle and exit codes are unchanged). It
replaces the *mechanism* by which names enter the proven tier: the per-name signature/contract
admission of OPEN-116/OPEN-122 is stopped.
**Design basis (historical drafts, committed verbatim):**
[`drafts/ADR-013-draft-R-EFFECT.md`](drafts/ADR-013-draft-R-EFFECT.md) and
[`drafts/ADR-014-draft-interpreter.md`](drafts/ADR-014-draft-interpreter.md).
**Tracking:** OPEN-123 (the foundation spike). **First result:** [`docs/v27/spike/H1-report.md`](../spike/H1-report.md).

Evidence tags as elsewhere: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## Context

- The per-name **command-signature track** (M1 slice 2, OPEN-120: each command attested by solo
  probes under the oracle, then admitted by its signature) failed adversarial review four rounds
  running, each time on a composition hole the previous round had missed. This is the track the
  owner was asked about ("The command-signature track (the running dynamic workflow) has failed
  review 4 rounds running on composition holes. Stop it?", 2026-09-29 06:12:50Z). The holes, as
  the assistant summarised them to the owner at 06:12:44Z (the summary names findings from rounds
  1–3 only):
  - round 1: commands that swallow the next token;
  - round 2: the mode a command leaves behind, and fragile commands inside moving arguments;
  - round 3: `x \section{a}\par\unskip x`, where whether `\unskip` is allowed depends on what is
    already on the page;
  - also round 3: `\label` stores a counter's printed form, and `\ref` makes it fatal on a later
    pass (the 27th `enumii` item gives "Counter too large").

  The corrections are recorded on the unmerged branch `feat/v27165-contract-signatures` (last
  commit `1224b4b7`): C-82 (a probe that saw one way of taking a token; a typing witness that
  toggled the mode it tested) and C-90 (each use attested in isolation, so what a use leaves
  behind was never attested). Every one of these holes was in *our model* of how commands
  compose, not in pdfTeX.
- Corroborating, from a different track: step 2 slice A of the hand-modelled L_S0 kernel
  (OPEN-122, branch `feat/v27165-strict-args`, unmerged) had its own review rounds find capacity
  and closure holes: C-92, C-94, C-96, C-98. Slice A is not stopped by this ADR (D4).
- On 2026-09-29 the owner restated the goal: "the goal is yet again PERFECTNESS: we need to
  provably declare compilation if and only if it will compile (within a subset of latex where
  thsi [sic] can be done). So no shortcuts, no bandaids, only perfect and durable solutions."
- Two architectures were then designed to the same depth, as the owner asked ("Design both,
  then decide"):
  - **ADR-013 draft, R-EFFECT.** Per-command behaviour programs, derived from a static read/write
    and error-site census of each name's code plus traced probes; a multi-pass semantics; per
    document configuration attestation. Its trusted base grows with every package (a complete
    static analyser of TeX macro code, representative probes).
  - **ADR-014 draft, a verified interpreter.** Translate pdfTeX's own tangled program into Coq
    mechanically, load the real `pdflatex.fmt` as data, and decide by execution. It has one
    fixed premise (`FaithfulEngine`, per engine revision, image and architecture). Its own §10.3
    pointed out the cost: it is, in effect, pdflatex re-run inside Coq, estimated 10–60x slower
    than pdfTeX [I], so it complies with ADR-012 decision 3 ("never compile the body") only in
    wording unless the purpose of that decision is stated.

## Decision

The owner answered four questions in the working session (recorded answers, UTC timestamps of
the session transcript `6724887f`):

1. **2026-09-29 07:14:57Z — architecture:** "Design both, then decide". **Signature track:**
   "Stop it now". The per-name signature workflow is stopped; its branch is kept for its measured
   composition holes and is never shipped as a basis for PROVEN verdicts (its last commit is
   `1224b4b7`, "WIP (STOPPED, do not merge)", on `feat/v27165-contract-signatures`).
2. **2026-09-29 07:52:26Z — what the proof is for:** "Static, real-time, engine-free". The
   option, verbatim: *"The proven verdict must come WITHOUT running pdflatex on the document
   (fast, per keystroke, works where TeX isn't installed). Build the synthesis: translate pdfTeX
   into Coq as the fixed foundation, derive proven command summaries offline by sound abstract
   interpretation, keep the fast static kernel for real-time decisions."*
3. **2026-09-29 07:52:26Z — the spike:** "Yes, start the spike". The option, verbatim: *"Run
   steps H.1–H.6 with their kill criteria; report before any further architecture commitment."*

What this decides, and what it does not:

- **D1. Purpose.** A PROVEN verdict is static: it is computed without running a TeX engine on the
  document, fast enough for keystroke use. This is the reason behind ADR-012 decision 3 and it is
  now stated. ADR-014's "decide by executing the whole document in Coq" is therefore **not** the
  product; it is the foundation.
- **D2. Architecture: the synthesis.**
  - *Foundation.* pdfTeX's program, from the exact source revision of the pinned binary,
    mechanically translated into Coq (ADR-014 draft §2: `tie` + `tangle` of `pdftex.web` and its
    change files, the tangled Pascal translated statement by statement under a small reviewed
    semantics `PS`). The one premise about the world is `FaithfulEngine`, fixed per (engine
    source revision, image digest, architecture). It replaces `Faithful` over the hand-written
    relation `Runs`.
  - *Admission, offline.* A Coq-proven **sound abstract interpreter** over the translated engine
    symbolically executes a command's *real* definition (from the pinned format and the
    package's own code) and produces a summary whose soundness is a theorem, not a trusted
    analysis. This happens when a configuration is set up, not per keystroke.
  - *Decision, real time.* The fast static kernel (`proofs/Strict`, extracted) decides the
    document using only proven summaries.
  - *Boundary.* Anything the abstract interpreter cannot summarise soundly, and any combination
    it cannot cover, is **outside the tier**, never guessed.
- **D3. The foundation spike is funded**: ADR-014 draft §9, the plan the owner approved with "Run
  steps H.1–H.6 with their kill criteria". The pass criteria, kill criteria and fallbacks below
  are the draft's, verbatim (work summarised):

  | step | work | pass criterion | kills the approach if (fallback) |
  |---|---|---|---|
  | H.1 | identify the exact source revision of the pinned binary; build it; confirm `INTEGER_TYPE`, `GLUERATIO_TYPE`, `-ffp-contract` | the reference build's logs and `.aux` equal the pinned binary's on 200 corpus documents (PDF modulo `/ID`) | the revision cannot be identified, **and** no revision reproduces the logs. Fallback: pin the reference build as the new oracle (an ADR-012 decision-7 change) |
  | H.2 | translator for the Pascal subset → Coq AST; `PS` as a fuelled interpreter; closure compiler; extraction | 100 % of procedures translated; Coq accepts the term; the extracted binary runs INITEX to the `*` prompt | the Coq term or its extraction is intractable (> 2 h compile or > 16 GB). Fallback: split the program into per-part modules, or emit a shallow embedding with a generated reflection lemma |
  | H.3 | load the real `pdflatex.fmt` in the model; round-trip `store_fmt_file`; meanings of the kernel names; locate F7's byte difference | round trip byte-exact; meanings byte-identical to the contract generator's; F7 explained | the load cannot be made exact within the spike |
  | H.4 | reproduce all L_S0 evidence, ADR-013's ≈ 50 measured documents and the owner's composition cases in the model | verdict, message and `l.N` agree with the recorded oracle grades on 100 %, or every disagreement is traced to a stubbed external | disagreements traced to the *translated* code keep appearing after 3 fixes |
  | H.5 | speed: the one-line document, the 12-page synthetic paper, a 40-page corpus paper; cold and from a preamble snapshot | ≤ 60× pdfTeX per pass | > 200× with no profile-guided fix in sight. Fallback: a verified-refinement fast interpreter becomes its own project |
  | H.6 | co-simulation: a digest change file in the reference build; step-by-step comparison on 20 documents | the first divergence (if any) is localised to a unit automatically | the digest cannot be made to match on a *correct* model (hidden C state not in the translated globals) |

  The spike reports before any further architecture commitment.
- **D4. The per-name signature track is stopped** (answer 1). As a consequence (derived, not a
  separate question put to the owner): OPEN-122's slices B–D of ADR-012 step 2 are **frozen**
  pending the synthesis. The L_S0 kernel on `main` stays as it is: the synchronous fast path and
  regression evidence. Slice A (branch `feat/v27165-strict-args`, not merged) is unaffected by this
  ADR; whether it merges is decided on its own review.
- **Not decided here** (ADR-014 draft §12, still open): O-5 (quantify verdicts over the date and
  the random seed, or change the oracle to a forced date — the clock measurement of #625 moved no
  grade on the fragment, but the run-dependent primitives exist); O-9 (restricted `\write18`);
  O-7's exact wording of the trusted base. O-8 (accept a reference build as the oracle if the
  revision cannot be identified) is moot after H.1: see below.

## Consequences

- Nothing about TeX's behaviour is written by hand any more; what remains hand-modelled is the
  C boundary (kpathsea, the first line, the clock, the terminal, the PDF-side C libraries), which
  ADR-014 draft §2.5 enumerates. That is where the next scrutiny belongs.
- Payoff is a step function: no new PROVEN verdict on a real paper until the foundation, the
  format load and the abstract interpreter exist. The published strict-tier number stays what the
  L_S0 kernel measures until then.
- The engine pin becomes a *source* pin as well as a digest pin. H.1 establishes it.

## H.1 result (2026-09-30, full numbers in `docs/v27/spike/H1-report.md`)

- **The revision is identified, and the binary is reproduced byte for byte on both architectures [M].**
  The image's `pdftex` for both architectures is byte-identical to the assets of TeX Live's
  GitHub release `svn78081` (TeX-Live/texlive-source commit `dc8efcd4…`, svn r78081, 2026-02-23).
  Rebuilds of that commit with TeX Live's own CI recipe give the pinned sha256 on aarch64
  (`cee621bf…`, native) and on x86_64 (`1c5ff711…`, under emulation). The kill criterion of H.1
  did not fire.
- **The shipped `pdflatex.fmt` is reproducible byte for byte [M]**, contrary to the ADR-014
  draft's F7. The only run-dependent content is the INITEX run's clock (`\time`, `\day`,
  `\month`, `\year` are dumped with the format, and the format identifier carries the date). A
  rebuild with `SOURCE_DATE_EPOCH` set to the shipped build's start minute and
  `FORCE_SOURCE_DATE=1` is identical to the shipped file.
- The draft's source citations were read from TeX Live **trunk**. Ten of the eleven files it
  cites are identical to r78081; `tex.ch` is not (trunk has since changed `scan_file_name`'s
  handling of `\relax`). The spike uses r78081.
- **The pass criterion was met only with the clock fixed [M].** Under the protocol's real clock, 7 of
  the 200 real papers differ between the two builds (2 logs, 5 PDFs beyond `/ID`). All 7 differ
  through the clock; the two binaries are the same bytes. With `FORCE_SOURCE_DATE` and one
  `SOURCE_DATE_EPOCH`, 200 of 200 agree. Treating the clock as an input is O-5, still open above.
- **The architectures do differ, in the PDF [M].** The aarch64 binary fuses floating-point
  multiply-adds (FMA) that the x86_64 one does not.
  - At `\pdfsetmatrix`'s matrix arithmetic (every graphicx `\rotatebox`/`\scalebox`) the products
    are inexact. A review-round-1 document with 400,000 rotated links gives PDFs that differ in
    one `/Rect` byte, with rc, log and `.aux` identical.
  - Every fused site outside xpdf that reaches TeX state is exact on its whole input range or
    under a stated bound, or is unreachable in `pdflatex.fmt`. The exception is xpdf's
    real-number parser for included PDFs, which is open.
  - On the corpus (200 real papers, 489 evidence documents, 40 traced documents) no
    difference was observed.
  - So H.2's semantics must model fused multiply-add per architecture at the matrix sites (no
    exactness lemma exists there), or not claim the PDF output there. Report §5.
- **All amd64 evidence is emulated** (qemu-user on an arm64 host): the rebuild, the behaviour runs
  and the format run. A confirmation on a native amd64 host, the CI runner of `tex-oracle.yml`, is
  open (OPEN-123).
