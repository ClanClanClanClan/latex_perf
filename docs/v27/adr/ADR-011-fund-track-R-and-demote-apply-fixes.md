# ADR-011 — Fund Track R; take `--apply-fixes` off the recommended path; four measurement decisions

**Status:** Accepted (2026-09-20). **Deciders:** maintainer.
**Supersedes:** nothing. **Related:** OPEN-104, OPEN-105, OPEN-103, OPEN-101, ADR-010.

## Context

A full audit on 2026-09-20 measured the project's position against the repo rather
than against its own prose. Four things it found bear on decisions only the
maintainer can make, and all four had been drifted past at least once before.

**The serving path has not changed since February 2026.** Measured with
`git log -1` per file: `broker.ml` 2026-02-20, `main_service.ml` 2026-02-20,
`rest_api_server.ml` 2026-02-22, `rust/` 2026-02-22 (a `cargo fmt`),
`rest_handlers.ml` 2026-04-24. Over the same window `specs/rules/rules_v3.yaml`
held 660 rule ids at the start and 660 at the end — zero new rules — and the last
40 first-parent commits touched `corpora` 125 times, `latex-parse` 86, `docs` 67,
`scripts` 64, `proofs` 7. Twelve of sixteen ROADMAP tracks are untouched. The
maintainer named real-time and style rules as core on 2026-09-05; agents drifted
past that twice more, and the audit that produced this ADR is itself an instance.

**The auto-fix channel breaks real documents at a rate that is not falling.**
One binary, three windows, measured 2026-09-13 and recorded in OPEN-100: offset
2000 (tuned twice) 0/38, offset 2100 (tuned by the OPEN-097 fix) 1/39, offset 2300
(never used for anything) 7/38. The sharpest part is a CONTROL: window 2300 was
re-measured with the OPEN-097 fix reverted and returned 7/38 — the identical seven
papers. Pooled over genuinely untouched windows the rate is 20/115, flat across
three rounds of individually-correct producer fixes. Meanwhile PROJECT_STATE §1
publishes `breaks_compile 0`, which is a tally over a three-row exception list of
in-house fixtures containing none of the constructs that break documents.

**The flagship soundness number rests on rows nobody compiled.**
`corpora/real_roots/results.json` carries `pdflatex_passes` on 18 of 200 rows;
180 of the 185 true-READY rows have never received the confirming pdflatex pass,
and the artefact's own `measured_at` says so: *"cli-only refresh; pdflatex verdicts
carried forward"*. The protocol reached 13 of 13 compile failures and 5 of 185
compile successes, so the entire deficit sits on the soundness side (OPEN-103).

## Decisions

### 1. Track R is FUNDED, and sequenced behind the safety repair

Fund R. Do not park it, and do not delete the per-keystroke wedge from ROADMAP §0.

Sequencing is part of the decision, because the failure mode here is not
under-funding, it is starting the interesting work before the measurement is
trustworthy. Track R work begins after the soundness-and-fixer-safety train
(OPEN-080/101/103 and the fixer class sweep). Its FIRST deliverable is a
**recorded** cold-path number, not an optimisation: `scripts/bench_wedge.sh`
already prints a `cold_check_ms` column on every `perf-ci` run and the value is
discarded — `check_keystroke_budget.py` contains zero occurrences of `cold` and
`corpora/perf/keystroke_budget.json` has no cold key. The project measures its own
user-facing latency on every PR and throws it away.

**Constraint, binding:** nothing in Track R may be baselined on the maintainer's
laptop. Process invariant 5 already says this; the audit found a sharper reason.
The load average on that machine read 257 on 8 cores while actual CPU use across
all processes was near zero and there were two python processes and no pdflatex —
so even the load guard `check_keystroke_budget` uses to refuse `--record` above
4.0 is reading a number that does not mean what it says. Baseline from an idle CI
runner or not at all.

### 2. `--apply-fixes` comes OFF the recommended path

The flag keeps working and keeps every gate it has. It stops being the documented
default recommendation in the CLI help, the README and the docs site.

A tool that turns a compiling document into a non-compiling one does the same harm
as a false READY through a different channel, and this one is measured at 7 of 38
on data it has never seen, with a reverted-fix control proving the last round of
work moved it by zero. Three rounds is enough evidence that instance-level
producer guards do not move the rate.

**This decision is reversible by exactly one number:** a class-level guard at the
`Fix_guard` choke point that moves an *untouched* window. It may NOT be reversed
on a tuned-window reading — every tuned window in this project's history has read
near zero while the out-of-sample rate stayed flat, and that is the specific error
C-57 records.

### 3. The false-READY number gets published whichever way it moves

Before the OPEN-103 sweep runs: a rise in the measured false-READY rate is a
**publication event, not a regression**. It is written here so the result cannot
be relitigated after it is known, and so no one has to decide under the pressure
of an unwelcome number.

This is the whole premise of the corrections log applied one level up: the project
publishes what it measures, including when measuring better makes the number
worse. The in-sample zero was never evidence of soundness; discovering that is
progress, and a ledger that only ever improves is measuring its own scope.

### 4. `PREMISE-CERTIFIED` is relabelled, not widened

The certificate is printed on 199 of 200 sample-1 documents and 197 of 200
sample-2 documents, including all seven virgin FALSE-READYs. The set of
premise-certified documents is a superset of the set of READY documents on all 400
rows, so the published coverage figure is the true-READY rate restated under
another name; and mechanically the collapse is known — `declared_features` defaults
to `[]` with no production caller passing it, so the `t3_declared` conjunct is
unconditionally true, and D2a proved Channel 1 unreachable for anything the
encoder can build.

**Decision:** publish the decomposition next to the figure and rewrite the printed
verdict string to name only the obligation that can actually fail. Do NOT widen
the model (D3) to make the certificate mean more. Widening a certificate that has
not yet been decided to discriminate is XL effort at the wrong end; re-enter that
question only once the certificate can withhold.

### 5. `\input` containment is NOT added

`\input{../outside/x}` returns READY today and pdflatex compiles it, rc 0 — so the
verdict is **correct**. Bounding resolution to the project root would convert
correct READYs into over-rejections on every compiling paper that uses `../`, and
that prevalence has never been measured.

**Decision:** do not bound it. This is a policy question, not a bug, and it must
not be smuggled in alongside the absolute-path resolver fix. What would change the
answer: a measurement of how many real roots resolve outside their own directory,
and a threat model naming who is hurt by a READY on such a document.

### 6. Release-debt gate threshold: N = 25

`git describe --tags origin/main` currently reads 13 commits past v27.1.63. The
risk is not 13 — it is that nothing watches the number: OPEN-013 records a peak of
102 commits over 47 days with every required context green throughout, during
which the released artefact still contained a fixer measured at a 63.3% break rate,
because every accuracy fix lived only on main.

N = 25 is green today and would have fired around day 34 of that 47-day window.
The gate ships independently of and ahead of the next tag; the tag itself waits for
the OPEN-103 sweep and the fixer class sweep, since cutting one today would ship a
soundness headline built on 180 unconfirmed rows.

## Consequences

- Track R gets an owner and a first deliverable that cannot be satisfied by an
  optimisation nobody measured (OPEN-104).
- The recommended path stops including a channel measured to damage ~1 in 6 unseen
  compiling papers (OPEN-105). Implementation — CLI help, README, docs site — is
  pending and tracked on that row.
- The OPEN-103 sweep can be run without a live argument about what its result means.
- D3 is explicitly deferred, and the deferral has a stated re-entry condition rather
  than being dropped.
- Two things this ADR deliberately does NOT do: it does not park anything, and it
  does not promise a date. ADR-010 parked WS10/WS11 on a compatibility argument;
  nothing here is parked, and Track R's sequencing is a dependency claim, not a
  deprioritisation.
