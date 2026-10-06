# ADR-015 — The proven tier is static, real-time and engine-free, built on a Coq translation of the pinned pdfTeX

**Status:** Accepted (2026-09-29). **Deciders:** maintainer (owner).
**Extends:** ADR-012 (its goals, verdict type, oracle and exit codes are unchanged). It
replaces the *mechanism* by which names enter the proven tier: the per-name signature/contract
admission of OPEN-116/OPEN-122 is stopped.
**Design basis (historical drafts, committed verbatim):**
[`drafts/ADR-013-draft-R-EFFECT.md`](drafts/ADR-013-draft-R-EFFECT.md) and
[`drafts/ADR-014-draft-interpreter.md`](drafts/ADR-014-draft-interpreter.md).
**Tracking:** OPEN-123 (the foundation spike). **First result:** [`docs/v27/spike/H1-report.md`](../spike/H1-report.md).
**Results of record:** § "H.1 result" and § "H.2 and H.3 results" below; H.5 per E12.

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
- **D3. The foundation spike is funded**: ADR-014 draft §9, "(H) Feasibility spike (≈ 2 weeks of
  agent work)", the plan the owner approved with "Run steps H.1–H.6 with their kill criteria" (the
  question put was "Fund the 2-week foundation spike", 07:40:16Z). The days, pass criteria, kill
  criteria and fallbacks below are the draft's, verbatim; the work column is summarised:

  | step | days | work | pass criterion | kills the approach if (fallback) |
  |---|---|---|---|---|
  | H.1 | 1–2 | identify the exact source revision of the pinned binary; build it; confirm `INTEGER_TYPE`, `GLUERATIO_TYPE`, `-ffp-contract` | the reference build's logs and `.aux` equal the pinned binary's on 200 corpus documents (PDF modulo `/ID`) | the revision cannot be identified, **and** no revision reproduces the logs. Fallback: pin the reference build as the new oracle (an ADR-012 decision-7 change) |
  | H.2 | 3–6 | translator for the Pascal subset → Coq AST; `PS` as a fuelled interpreter; closure compiler; extraction | 100 % of procedures translated; Coq accepts the term; the extracted binary runs INITEX to the `*` prompt | the Coq term or its extraction is intractable (> 2 h compile or > 16 GB). Fallback: split the program into per-part modules, or emit a shallow embedding with a generated reflection lemma |
  | H.3 | 7–8 | load the real `pdflatex.fmt` in the model; round-trip `store_fmt_file`; meanings of the kernel names; locate F7's byte difference | round trip byte-exact; meanings byte-identical to the contract generator's; F7 explained | the load cannot be made exact within the spike |
  | H.4 | 9–11 | reproduce all L_S0 evidence, ADR-013's ≈ 50 measured documents and the owner's composition cases in the model | verdict, message and `l.N` agree with the recorded oracle grades on 100 %, or every disagreement is traced to a stubbed external | disagreements traced to the *translated* code keep appearing after 3 fixes: the translator or `PS` is wrong in a way that is not converging |
  | H.5 | 12 | speed: the one-line document, the 12-page synthetic paper, a 40-page corpus paper; cold and from a preamble snapshot | ≤ 60× pdfTeX per pass | > 200× with no profile-guided fix in sight. Fallback: a verified-refinement fast interpreter becomes its own project |
  | H.6 | 13–14 | co-simulation: a digest change file in the reference build; step-by-step comparison on 20 documents | the first divergence (if any) is localised to a unit automatically | the digest cannot be made to match on a *correct* model (hidden C state not in the translated globals) |

  The spike reports before any further architecture commitment.
- **D4. The per-name signature track is stopped** (answer 1). As a consequence (derived, not a
  separate question put to the owner): OPEN-122's slices B–D of ADR-012 step 2 are **frozen**
  pending the synthesis. The L_S0 kernel on `main` stays as it is: the synchronous fast path and
  regression evidence. Slice A (branch `feat/v27165-strict-args`, not merged) is unaffected by this
  ADR; whether it merges is decided on its own review.
- **Not decided here** (ADR-014 draft §12, still open): O-9 (restricted `\write18`); O-7's exact
  wording of the trusted base. (O-5, the clock — quantify verdicts over the date and the random
  seed, or change the oracle to a forced date — was listed here; it was decided on 2026-10-05 by
  E10 below.) O-8 (accept a reference build as the oracle if the
  revision cannot be identified) is moot after H.1: see below.

## Owner decisions of 2026-09-30 (after the H.1 report)

This section is the one place of record for these decisions. Other documents (OPEN-123,
OPEN-124, the CHANGELOG) point here. Where a decision answers an open question of the ADR-014
draft §12, the O-n id is given; otherwise none exists and none is invented.

- **E1. The Pascal "Stuck" rule is ACCEPTED.** Arithmetic that pdfTeX's Pascal semantics leave
  undefined (signed overflow, division by zero or INT_MIN/−1, out-of-range real→integer
  conversion) stops the run in `PS`: the document is **outside the tier**, never assigned a
  verdict. This is the reading H.1 proposed for H.2 (§H.1 result above, report §5.4). It needs no
  per-architecture model for those operations. It settles, for this class, part of what O-7's
  trusted base must name (the implementation-defined classes, `char` signedness and FMA
  contraction, remain parameters of `FaithfulEngine` per architecture, as above).
- **E2. The CPU architecture IS part of the oracle's identity.** A PROVEN verdict names its
  architecture, and graders must not compare grades across architectures (C-103: the same image
  digest gives different exit codes on aarch64 and x86_64). This makes the per-architecture
  `FaithfulEngine` of D2 and O-7 binding on the oracle as well as on the proofs. It amends
  ADR-012 decision 7 (the digest-pinned oracle) by adding the architecture to the pin.
  **Implementation is a later oracle PR**; until it lands, nothing in `_oracle.py` or the
  artefacts enforces it. *Implementation note (2026-10-02, OPEN-126, branch
  `fix/v27165-oracle-arch`; not a new decision):* the architecture of record is aarch64
  (`_oracle.ARCH_OF_RECORD`); the oracle refuses to grade on any other; every oracle block
  recorded in a tracked JSON file must name it (`check_oracle_pin.py` DISCOVERS every such block
  and fails one that is unregistered or of another architecture; until review round 2 it checked
  a hand list of 15 and missed the L_S0 bytes evidence, the contracts and the re-grade diffs,
  C-127), so a recorded grade and a live one are of one architecture by construction; the
  comparers check it again on the recorded side (`require_same_oracle`; `gen_contract.py probes`
  and `check_contracts_reproducible.py` compare a contract pin's image, architecture and format);
  and CI's `tex-oracle` job runs on a native arm64 runner, which `check_oracle_pin.py` also
  enforces. Choosing aarch64 for CI (rather than keeping amd64
  with per-architecture baselines) is put to the owner in OPEN-126. *Decided 2026-10-05: E9
  (aarch64; no per-architecture baselines).*
- **E3. Native amd64 confirmation: approved, not yet run.** The owner approved confirming the
  emulated amd64 evidence of H.1 by a one-off GitHub Actions job on the spike branch. That job has
  not been created or run: adding the workflow awaits the owner's permission. Until it runs, all
  amd64 evidence stays emulated and OPEN-123 lists the confirmation as open.
- **E4. Speed: no optimisation funding yet.** The spike's speed measurements so far (≈150–300×
  pdfTeX, taken at a machine load average of 57–114, so not a speed measurement a decision can
  rest on) fund no optimisation work. Speed is re-measured on a quiet machine with a real
  document during H.3. H.5's pass and kill criteria (D3's table: pass at ≤ 60× per pass, kill
  above 200× with no profile-guided fix in sight) are **unchanged**.
- **E5. Step 2 (ADR-012 step 2, slice A, branch `feat/v27165-strict-args`) is PARKED**, as
  OPEN-124 already records. This is the answer to the slice-A part of O-10: the branch is kept as
  a backup and does not merge; capacity limits are to be derived from the translated engine
  (Consequences, first bullet), not modelled by hand.

## Owner decisions of 2026-10-05 (after the H.3 checkpoint 1 report)

Same rule as above: this is the one place of record. The H.3 report and its evidence are on
branch `spike/v27165-engine-translation`, at `7d927b5f:docs/v27/spike/H3-report.md`.

- **E3 status (no new decision).** The native amd64 confirmation approved in E3 was RUN on
  2026-10-02 on GitHub-hosted x86_64 runners (`spike-native-amd64.yml`, branch
  `ci/v27165-native-amd64`, PR #630 into the spike branch). It CONFIRMS every committed H.1
  architecture probe. For H.2's differential it confirms 176 of 178 rows and REFUTES 2: at
  `t205` and `t208` the committed emulated amd64 exit code was qemu's, not the binary's (C-113 on
  that branch). E3's "not yet run" is superseded by this line.
- **E6. H.3's "round trip byte-exact" means MODEL = BINARY.** The pass clause is met when the
  model's run, given `pdflatex.fmt` and dumping again, is byte-identical to the pinned binary's
  run of the same input: terminal output, log and the dumped format stream. It does **not** mean
  that dumping a loaded format reproduces the loaded file (`store(load(x)) = x`). The pinned
  pdfTeX does not satisfy that reading either: its re-dump appends the strings created by the run.
  The difference between the re-dumped and the shipped format must still be **fully explained**,
  byte by byte, by decoding the format beyond the string pool. "Not yet decoded" is not an
  explanation.
- **E7. `_oracle.py` gets a measurement entry point.** It must provide terminal input, an explicit
  architecture and the clock shim, so that every run of the pinned binary goes through the pinned,
  checked oracle and `check_oracle_pin`. That includes the binary side of the spike's H.2 and H.3
  evidence (today a quoted recipe) and of H.4 and H.6. It builds on E2's implementation (OPEN-126,
  branch `fix/v27165-oracle-arch`) and lands after it.
- **E8. Memory: measure before funding.** No new heap representation is funded yet. The model's
  full meaning dump (H.3's remaining clause) is first run once on a GitHub-hosted runner. The
  repository is public, so `ubuntu-latest` is documented as 4 vCPU / 16 GB; the job records what
  it actually got. The run records the peak memory, time and result. Whether the remaining heap
  growth (C-112 on the spike branch) is an H.5 matter is decided on that measurement.
  Profile-guided fixes of the kind already made stay within the spike's scope (D3, H.5's kill
  criterion).

## Owner decisions of 2026-10-05 (continued)

Same rule as above: this is the one place of record. Both decisions answer owner questions that
OPEN-126 (branch `fix/v27165-oracle-arch`) put; the evidence they rest on is that row's.

- **E9. The architecture of record for grading is aarch64.** CI's required `tex-oracle` job runs
  on GitHub's `ubuntu-24.04-arm` runner. No per-architecture baselines are kept.
  *Chosen over:* keeping amd64 CI with per-architecture baselines.
  *Rationale (the evidence and argument of OPEN-126, which the owner was shown; no other reason
  is of record):* E2 forbids comparing grades across
  architectures, and every graded artefact was recorded on aarch64 (all 15, MEASURED in OPEN-126),
  while CI had graded on amd64 since #617 (C-119). Keeping amd64 CI with per-architecture
  baselines would first need a native amd64 grade of every fixture set.
  *Author's note, NOT a reason the owner was shown (added by the recording agent, 2026-10-05):*
  per-architecture baselines are two baselines to keep in step at every oracle-baseline change;
  one architecture means one baseline, and a CI grade and a local grade are then the same
  comparison.
  *Author's note (review round 2 of OPEN-126, 2026-10-05):* "all 15" was the hand list
  `check_oracle_pin.GRADED`. The gate now discovers every recorded oracle block. There are 40, in
  36 files, and every one is aarch64 except the pinned host diagnostic, which is no grade
  (C-127). The rationale shown to the owner holds for all of them.
  *Consequence:* this makes OPEN-126's choice of `ubuntu-24.04-arm` and
  `check_oracle_pin`'s refusal of any non-arm64 `tex-oracle` runner **binding**; E2's
  implementation note no longer awaits the owner. E3's one-off amd64 confirmation is unaffected:
  it measures the difference between the architectures, it does not grade.
- **E10. O-5 (the clock) is ADOPTED TOGETHER WITH E7's clock shim, in one change: grading runs
  with every run-dependent input fixed.** Contracts are regenerated accordingly. Date-dependent
  names are found by explicitly VARYING the fixed clock, not by relying on the real clock.
  *Chosen over:* (i) adopting `FORCE_SOURCE_DATE` alone now; (ii) quantifying verdicts over the
  dates (O-5 option (a)).
  *Rationale (the evidence and argument of OPEN-126 (d), which the owner was shown; no other
  reason is of record):* under `FORCE_SOURCE_DATE=1` 0 of 600
  sample rows moved (MEASURED, OPEN-126 (d)), but `FORCE_SOURCE_DATE` alone does not fix every
  run-dependent input: it does not pin `\pdfrandomseed`, `\pdfelapsedtime` or
  `\pdffilemoddate` (MEASURED 2026-09-29,
  `check_strict_kernel.py` R-CLOCK), so under it a grade would still not be a function of the
  input bytes; adopting it also changes how `gen_contract.py` finds the kernel's date-dependent
  names, so every contract is regenerated; and only the 600 sample rows were measured under it
  (OPEN-126 (d) (i)-(iii)). E7's clock shim could fix the seed and the timers as well as the date
  (OPEN-126 (d) (iv)). The question put to the owner marked the combined option ("date, seed and
  timers at once") as recommended. OPEN-126 (d) made no argument against quantifying over dates
  (option (ii)); no reason for rejecting it is of record.
  *Author's notes, NOT reasons the owner was shown (added by the recording agent, 2026-10-05):*
  adopting `FORCE_SOURCE_DATE` alone now would be one oracle-baseline change, and fixing the rest
  of the run-dependent inputs later a second; and the H.1 pass criterion was met only with the
  clock fixed (§ H.1 result).
  *What this means for the implementation (derived, not separate decisions):* the change is ONE
  oracle-baseline change, made by a follow-up track, not by OPEN-126's branch; until it lands
  `_oracle.PROTOCOL_CLOCK` stays `real` and nothing on `main` fixes the clock in grading. Its
  whole scope (the class census, E7's measurement entry point, the clock in the oracle's identity,
  run-start stamping, the `_oracle.py` comments, varying the fixed clock in `gen_contract.py`, the
  re-grade and regeneration, the `GRADING_CODE_PENDING` producers, CI's tmpfs) is ONE ledger row,
  **OPEN-128** in `docs/v27/PROJECT_STATE.md`, and is not restated here.

## Owner decisions of 2026-10-06

Same rule as above: this is the one place of record. E11 was decided on 2026-10-05 and its
outcome is recorded here. E12–E15 were approved by the owner on 2026-10-06 ("ok, go") after an
audited recommendation: the assistant's re-audit of its own first recommendation (a working
note, not committed; its errors are C-130). The spike's code and evidence are on branch
`spike/v27165-engine-translation`; a file cited as `67ca47df:path` is on that commit (the
branch tip when this was written), not on `main`.

- **E11. A time-boxed heap-representation fix was funded (decided 2026-10-05; outcome recorded
  now).** This is the "profile-guided fix" that H.5's kill criterion allows for (D3). Its terms, as
  recorded at `67ca47df:docs/v27/spike/H5-heap-design.md` (lines 4–9): stage 1, profile and
  design, by the end of 2026-10-06; stage 2, implement and measure, by the end of 2026-10-10;
  "if at the end of the box no representation gives memory that does not grow with the work done
  and a speed at or below 200× pdfTeX on H.5's documents, H.5's kill criterion fires". E8's "no new
  heap representation is funded yet" is superseded by this line. *Outcome* (stage 1: spike commits
  `b9ea746c`, `ee148dcc`; stage 2: `b330a029`, `b3c05b38`, `284ef72c`; E8's runner measurement:
  `67ca47df`; the details are at `67ca47df:docs/v27/spike/H5-heap-design.md` §8 and
  `67ca47df:docs/v27/spike/H3-report.md` § "H.5 stage 2"):
  - **B2 is the model build.** The ten members of the interpreter's fuelled mutual block in
    `67ca47df:docs/v27/spike/h2/coq/Interp.v` were restructured at the source, so that no
    extracted closure holds a state across a call. Each member, and `Main.run`, is proved equal
    to its pre-B2 definition (`67ca47df:docs/v27/spike/h2/coq/RefInterp.v`) by `reflexivity`, in
    `67ca47df:docs/v27/spike/h2/coq/B2Equiv.v`, with no axiom. `Extract.v` (the realizers),
    `driver.ml`, `Boundary.v`, `Values.v`, `Main.v` and the translator are unchanged: **the
    trusted base is unchanged**. B2 adds no realizer; T1, T2 and candidate A's in-place array are
    not in it.
  - **Memory is flat**, apart from the I/O residual [M]. Before B2 the full meaning dump grew by
    ≈ 3.1 MB per name and was killed at ≈ 14.5 GB at 4,000 names on a 16 GB GitHub runner. On B2
    the full 23,519-name dump peaks at 2.46 GB locally and 2.47 GB on the runner; what still
    grows is the I/O lists (≈ 15 kB per name locally, ≈ 43 kB per name between 2,000 and 4,000
    names on the runner). B2's memory property is tested, not proved: a standing retention check,
    whose static half is required because its dynamic half catches only 5 of 10 single-member
    reverts (C-150 on the spike branch).
  - **The full 23,519-name meaning dump on the B2 model build is IDENTICAL to the pinned binary**
    [M], `meanings_sha256` `4879fa65…` (the contract's digest): locally (macOS arm64, 2,673 s CPU,
    `67ca47df:docs/v27/spike/h5/evidence/stage2/fulldump/compare.json`) and on GitHub run
    37397064131 (x86_64, OCaml without flambda, 2,475 s CPU,
    `67ca47df:docs/v27/spike/h3/evidence/meanings/run3-37397064131/`). H.2's INITEX evidence, the
    178-input differential and the round trip (`55629ae0…`) are unchanged on the B2 build.
  - **Speed was NOT fixed.** B2 removes retention, not the cost of the integer conversions, and
    no profile-guided fix to ≤ 200× is in sight (E12).
- **E12. H.5: the meaning-dump proxy counts as H.5's evidence** (H5-heap-design §6, owner
  question 1, option (a)). H.5 is therefore recorded as **killed on the proxy by owner ruling
  (H5 Q1(a))**. The re-audit's corrected wording, which this records: *"The only legitimate form
  is 'killed on the proxy by owner ruling (H5 Q1(a)), A+T1+T2 build'."* Every figure is labelled
  by its build (D3's lines: pass at ≤ 60× pdfTeX per pass, kill above 200× with no profile-guided
  fix in sight):
  - *A+T1+T2 profiling build* (in-place arrays plus the conversion realizers; not a model build;
    a profiling build in E14's sense): **818×** on the whole dump, **≈ 1,540×** marginal
    per name, **59×** on the format load, **122×** at 1,000 names
    (`67ca47df:docs/v27/spike/h5/evidence/fair/fairtable.txt`, interleaved medians). On this build
    the format load and the 1,000-name run are under the kill line; the marginal cost and the
    whole dump exceed it.
  - *B2 model build*: **≈ 11,700×** on the whole dump (2,673 s CPU against the binary's 0.229 s
    median; one run, under a load average of up to 283, not interleaved rounds), and **≈ 315×**
    on the format load (≈ 35.3 s CPU at the end of the load in a retention-probe run of the B2
    build, `67ca47df:docs/v27/spike/h5/evidence/stage2/retprobe/B2-p50/probes.txt`, against the
    binary's 0.112 s median; this ratio is computed by the re-audit and not committed on the spike
    branch).
  - *No profile-guided fix in sight*: H5-heap-design §3.4 estimates every further change together
    at ≈ 370× central and ≈ 150× generous, relative to A+T1+T2 [I, from measured profile shares];
    only the generous case crosses 200×, and only with all four changes at once, which is the
    fallback project (E13).

  What this is **NOT**:
  - it is **not** a measurement on H.5's three documents (the one-line document, the 12-page
    synthetic paper, a 40-page corpus paper), which cannot run in the model yet: a pass reaches
    externals that are Stuck (43 of 188 are modelled), so they wait on the C boundary model
    (OPEN-123). On A+T1+T2 the proxy predicts the one-line document near 60× [I];
  - E4's re-measurement "on a quiet machine with a real document" was **not done**;
  - the ruling **replaces waiting for E11's box** to end on 2026-10-10. It does not apply H.5's
    criterion on its own conditions.
- **E13. The fallback is NOT funded now.** D3's fallback for H.5, "a verified-refinement fast
  interpreter becomes its own project", is a **new funding decision**, not a continuation of the
  spike. It is costed on record at verified-compilation scale: H5-heap-design §3.4 puts the model
  at ≈ 370× central and ≈ 150× generous after every profile-guided change, so ≤ 60× is reachable
  only by code generated from the IR with a verified compilation, "a research project of its own"
  (and the ADR-014 draft §10.2(4) called a proved-equivalent fast interpreter "a CompCert-sized
  proof effort"). It is **deferred until the abstract interpreter is scoped**. Its criteria are
  then pre-registered from the needs measured by that scoping: the cost and turnaround of the
  evidence, and the first-verdict latency on a new configuration. The model stays the
  specification.
- **E14. Realizer policy: evidence builds add NO new unverified realizer rows.**
  - T1 and T2 (the conversion and `Z` realizers) are allowed **only in profiling builds that are
    tagged as such in their provenance**. A gate must refuse evidence from such a build. That gate
    is **not yet implemented**; it is to be implemented later on the spike branch.
  - Zero-trust steps are allowed, e.g. emitting the IR's integer literals as `Z`
    (`67ca47df:docs/v27/spike/H5-heap-design.md` lines 639–642; it repeats H.2's size
    measurement).
  - A PrimInt63 re-expression is **scoped to i32 arithmetic**. TI64, 64-bit words and double bit
    patterns are out of its scope. Its stdlib spec Axioms would join `Print Assumptions`, and
    zarith stays, so the trusted base does not shrink. It is **deferred**.
- **E15. CI grading uses ONE launch definition**: the `ContainerOracle` invocation
  (`scripts/tools/_oracle.py`), run from the arm64 runner host, which already runs Docker
  (`tex-oracle.yml` runs `docker run` on the host; it is not a job container).
  - The in-image grading `docker run` steps of `tex-oracle.yml` and the native grading branch of
    `scripts/tools/_oracle.sh` are **retired**. `NativeOracle` is kept **only as a non-grading
    class** (`HostDiagnostic`'s base and a comparator).
  - The claim is **"one configuration by construction"**, NOT "identical platform". The platform
    residuals are enumerated and are to be measured: the work-root file system (case- and
    Unicode-insensitive locally, virtiofs over APFS, against case-sensitive Linux in CI; the
    local insensitivity is measured, `_oracle.py`'s "ONE FILE, MANY NAMES"; whether it changes
    any real document's grade is not), the kernel, CPU speed against the wall-clock timeout,
    memory, and disk.
  - **OPEN, pending that measurement:** O3.2 (grades of record come only from CI) or O3.3 (a
    VM-local Linux work root for local grading).
  - E15 **supersedes OPEN-128 item (9)** ("match the container's options"): native work
    directories are on the in-image `/tmp` tmpfs and the container's are on the bind mount, so
    matching mount flags cannot make the two configurations equal.
  - Per the approved recommendation it is implemented inside OPEN-128's single re-grade (it
    changes grading code, so it needs a full re-grade, which that row already carries). Nothing on
    `main` implements E15 yet.
- **Open, not decided: O1.2**, a per-configuration preamble snapshot, dumped offline by the
  pinned binary and loaded through the format-load path whose exactness H.3 established. It needs
  an owner ruling on the clause "works where TeX isn't installed" of the owner's 2026-09-29
  answer (Decision, item 2), to be informed by the abstract-interpreter scoping.

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
  `SOURCE_DATE_EPOCH`, 200 of 200 agree. Treating the clock as an input is O-5, decided 2026-10-05 by E10 (fixed clock).
- **The architectures differ in the compile VERDICT, not only in the PDF [M]** (corrected after
  spike review round 2; round 1's record said "in the PDF only", C-103). The same C source means
  different things on the two architectures wherever C leaves the result undefined or
  implementation-defined and the two ISAs or compilers answer differently. Five such classes were
  enumerated from the binaries (report §5.4). Adversarial documents run in the pinned image on
  both architectures show three of them changing rc, log or TeX state, one changing the PDF, and
  one with no difference found:
  - *integer division*: x86_64 traps (SIGFPE) where aarch64 returns 0. `\pdfsnapy 0pt`, a
    pdfTeX primitive with no external file, exits 136 on x86_64 and 0 on aarch64; an Exif
    resolution of INT_MIN/-1 in a JPEG exits 136 and 1;
  - *float-to-int conversion out of range*: x86_64 gives INT_MIN where aarch64 saturates. A valid
    40000×8-pixel JPEG without a resolution is `\wd` = −32768pt with rc 0 on x86_64 and
    "Huge page cannot be shipped out", rc 1, on aarch64; an Exif resolution of 2·10⁹/cm exits 1
    and 0; a map line's huge `SlantFont` changes the log and the PDF, a NaN one the PDF;
  - *signed overflow exploited differently by the two compilers* (aarch64 gcc 10, x86_64
    gcc 11): `\divide` of INT_MIN by INT_MIN, reachable in plain TeX because `\advance` does not
    check integer overflow, gives −1 on aarch64 and 1 on x86_64;
  - *fused multiply-add* (round 1): one `/Rect` byte in a 400,000-link document;
  - *plain `char` signedness*: 317 functions change under `-fsigned-char` (of TeX's tangled
    procedures only four, all in C string handling: file names, the command line, the pool); every TeX-visible
    string primitive among them, swept over all 255 bytes, agrees.
  - On the corpus (200 real papers, 489 evidence documents, 40 traced documents) no difference was
    observed.
  So `FaithfulEngine` is per architecture in substance, not as a formality: the proven tier's
  verdict for a document is a verdict *for one architecture*. What H.2 must do follows per class,
  not per site (report §5.4): the undefined-behaviour members (division by zero or INT_MIN/−1,
  out-of-range conversion, signed overflow) are **Stuck** in `PS`, which is Pascal's own reading
  and needs no per-architecture model; the implementation-defined ones (`char` signedness,
  contraction) are parameters of `FaithfulEngine` taken from that architecture's binary, or the
  affected output is not claimed. Of the 316 division and conversion sites, 196 are open (152 in
  libpng and xpdf); they are H.2's C-boundary work list. All x86_64 runs were emulated.
- **All amd64 evidence is emulated** (qemu-user on an arm64 host): the rebuild, the behaviour runs
  and the format run. A confirmation on a native amd64 host, the CI runner of `tex-oracle.yml`, is
  open (OPEN-123).

## H.2 and H.3 results (recorded on `main` 2026-10-06; full text on the spike branch)

The spike branch's copy of this ADR
(`67ca47df:docs/v27/adr/ADR-015-static-proven-tier-on-translated-engine.md`) has diverged from
this one: it has an H.2 result section and later corrections of the H.1 text, and it lacks
E1–E15. **This copy is the record.** What only the spike copy had is summarised below, with
pointers; the spike branch must merge `main` to take the record (OPEN-123).

- **H.1 (unchanged above): passed only with the clock fixed** [M]. The spike copy's H.1 section
  also carries corrections from later spike review rounds (round 3, C-106; round 4) that this
  copy's H.1 text predates. As that copy states them: a plain `\xleaders` over a glue of 2³¹−2 sp
  wraps `rule_wd + 10` and then divides by 0 (rc 0 on aarch64, SIGFPE on x86_64); of the 316
  division and conversion sites, 15 diverge, 4 are machine-checked unreachable, 77 are translated
  sites the Stuck rule covers and 220 are boundary sites with no evidence either way; and the
  native amd64 run of 2026-10-02 confirmed the behaviour runs and the format run, while the
  rebuild, the corpus comparisons and the gdb traces remain emulated only.
- **H.2: passed; the kill criterion did not fire** [M] (2026-09-30, review round 1 closed
  2026-10-01; `67ca47df:docs/v27/spike/H2-report.md`). 603 of 603 procedures of the tangled
  `pdftex.p` are translated into a Coq deep embedding; Coq accepts the program with its semantics
  `PS` (a fuelled interpreter) and extracts it to OCaml in minutes, under 0.6 GB per file; the
  extracted program runs INITEX through the `*` prompt with terminal output, log file and exit
  status byte-identical to the pinned binary's (the x86_64 `char` configuration against the amd64
  binary under qemu, and a hybrid aarch64 configuration against the arm64 binary). `PS`
  implements E1's Stuck rule, except at 13 pointer-arithmetic sites where it follows the binary.
  The C boundary is the open part: 23 of 189 externals were modelled at H.2, 43 of 188 at H.3's
  checkpoint 2, and the rest are Stuck. The 178-input differential, in both configurations: 134
  identical, 43 Stuck, 1 without a result (`romn`, killed by a 5,000 MB cap), 0 divergent; no row
  changed on the B2 build (E11). Its native amd64 confirmation is in "E3 status" above.
- **H.3: no "H.3 PASSED" is recorded.** Clause by clause (`67ca47df:docs/v27/spike/H3-report.md`):
  - *"round trip byte-exact"*: **met in E6's reading** (model = binary: exit status, terminal
    output, log and the dumped format stream `55629ae0…`), on the B2 build too, **on arm64
    only**; the amd64 configuration of the round trip is open. The difference between the
    re-dumped and the shipped format is accounted for byte by byte, as E6 requires.
  - *"meanings byte-identical to the contract generator's"*: **MET on the B2 model build** (E11:
    `4879fa65…`, locally and on GitHub run 37397064131). It was not met before B2: the model's
    full dump ran out of memory on 16 GB runners (E8's runs 37302258127 and 37306038862).
  - *"F7 explained"*: **explained by H.1** (C-100: the only run-dependent bytes of the shipped
    format are the INITEX run's clock), not re-derived by the model. This meets the literal
    clause, since D3's H.3 work column asks only to "locate F7's byte difference".
  - Kill criterion ("the load cannot be made exact within the spike"): **not fired**; the load is
    exact.
- **H.4 and H.6: not started. H.5: killed on the proxy by owner ruling (E12).** H.4, H.5's
  documents and H.6 share one blocker: the **C boundary model** (kpathsea file input, TFM loading,
  the general C-main command line, the PDF back end), which is unmodelled today.
