# ADR-012 — The proven subset becomes CONTRACT-BOUNDED; publish strict and heuristic tiers separately

**Status:** Accepted (2026-09-26). **Deciders:** maintainer.
**Supersedes:** the meaning of "proven-verdict coverage" in `ROADMAP.md` §1 and the
North-Star heading of `PROJECT_STATE.md` §1 before this ADR.
**Related:** OPEN-116 (the programme), OPEN-024, OPEN-034, OPEN-101, ADR-011 decision 4.
**Design:** [`docs/v27/STRICT_TIER_DESIGN.md`](../STRICT_TIER_DESIGN.md).

## Context

Until this ADR the project published *proven-verdict coverage* as its North Star, and
the figure it published was the rate of documents the CLI printed as
`READY … PREMISE-CERTIFIED`. ADR-011 decision 4 already relabelled that certificate,
because it certifies the premises of a Coq theorem over an **abstract** model rather
than the document. The measurements behind this ADR show that the relabelling was
not enough: nothing the CLI printed was a proof about the document, yet the headline
number carried the word *proven*. The facts, measured under the pin
`pdfTeX 3.141592653-2.6-1.40.29` (TeX Live 2026) and recorded in the design:

- **The certificate is wrong in both samples.** The generated block of
  `PROJECT_STATE.md` §1 publishes how often a certified document fails to compile; the
  rate is not near zero on either sample, and sample 2 (virgin) carries FALSE-READYs
  that the certificate accepted.
- **The heuristic tier accepts minimal failing documents.** A battery of minimal
  documents, each exhibiting one pdflatex fatal (`\frac` in text, an undefined control
  sequence, an undefined environment, `$\frac{1}$`, `\newcommand{\text}`, a missing
  graphic, a raw `≈`, cleveref loaded before hyperref, a blank line inside `align`,
  and others), was printed `READY … PREMISE-CERTIFIED` on most of them. M0 rebuilt it
  as `corpora/strict_battery/` and re-measured it: the `summary` block of
  `corpora/strict_battery/manifest.json` is the current count.
- **Composition of per-package facts is not sound.** `revtex4-2` with `tabularx`
  compiles with rc 0 when only the preamble is loaded and fails with `! Extra \or.`
  once the environment is used. 361 of 380 ordered package pairs do overlay, which
  makes composition a good *predictor* and an unacceptable *proof*.
- **Every configuration is distinct.** 200 of 200 sample-2 configurations (class plus
  ordered package loads) are distinct even ignoring options and order, so a fixed,
  shipped cache of contracts can prove almost nothing; a contract has to be generated
  for the configuration in front of the checker.
- **Static arity is not behaviour.** A macro's `#n` arity disagreed with its
  behavioural arity on 121 of 405 macros, so a shape read from a definition is a hint
  and never an attestation.
- **Generating a contract is cheap.** Trace and final-meaning dump of one real
  configuration took 0.2–2.3 s; solo use-site probes cost about 0.11 s each on 6
  workers, and the median paper uses 85 distinct body control sequences. A new
  configuration is attested in seconds.
- **The heuristic tier reads only the root for some channels.** OPEN-024: T3 sees the
  root's bytes only, so raw CJK in an `\input` child is a measured false-READY.

The design merged three independent proposals (semantics-first, attestation-first,
product-first), took semantics-first as the base because the judges preferred it
unanimously, and repaired the fatal flaw shared by the other two: both let composed
per-package contracts reach a PROVEN verdict.

## Decisions

The owner's decisions of 2026-09-26, recorded verbatim:

1. The proven subset is redefined as CONTRACT-BOUNDED: Turing-free text across the whole project closure AND the exact configuration (class + ordered package loads + options + interleaved preamble definers + format hash) has a contract generated and solo-attested under the pinned TeX Live. Inside: an exact Coq-proved decision (READY iff compiles, both directions, w.r.t. a declarative semantics; faithfulness to pdflatex is the named premise Faithful, attested by probes + a >=10k generated differential). Outside: a clearly labelled heuristic tier, never rendered as proof. Impossible-by-design: Turing-complete constructs outside any contract.
2. "Publish both": the North Star becomes strict-tier coverage at zero strict_wrong on a VIRGIN sample; today's premise-certified figure stays published ONLY as a heuristic-tier statistic.
3. On-demand attestation: YES — the checker may run pdflatex on the configuration PREAMBLE and on probe documents only, never on the document body; results cached by hash.
4. Vendored .cls/.sty: ADMITTED by content hash.
5. Benign \def: admitted LATER (M7+), after expand_terminates / subst_preserves_L_S are proved.
6. Exit codes stay 0/1; new --require-proof exits 4 unless the verdict is PROVEN. A wrong reason or location counts as strict_wrong. Any differential disagreement blocks a release. Preamble definers are part of the configuration key.

These answer the design's §H open decisions 1–6 and 8. Decision 7 of §H (draw sample 3
only after the pdfmanagement oracle repair, with sample 2 marked design-seen) is the
design's recommendation and is adopted with this ADR, since the headline strict number
must come from a virgin sample and sample 2 has now been used for design statistics.

## What milestone M0 ships (this ADR's PR)

M0 is the honesty change. **Nothing is proven yet**: the strict-tier membership
predicate is a stub that returns false, so the published strict-tier figure is 0 on
both samples, by measurement.

- One verdict type and one renderer (`latex-parse/src/verdict.ml`). Only its two
  `Proven_` constructors can render the word PROVEN, enforced by construction and by
  a unit test that scans every rendering, including adversarial user data
  (`latex-parse/src/test_verdict.ml`).
- `--compile-check` keeps every machine-read line byte-identical (the
  `MODEL-CONNECTED` line with its `PREMISE-CERTIFIED`/`PREMISE-REJECTED` token, the
  `READY\t`/`NOT-READY\t` token line, and the indented reasons) and adds, after them,
  one `TIER` line and at most three `why not strict:` lines. Every READY now reads
  `LIKELY OK (heuristic; premise-certified) — not a proof`; every NOT-READY reads
  `LIKELY FAIL (heuristic)`; an LP-Foreign document, previously mislabelled as a
  parse failure, reads `FOREIGN`. Exit codes are unchanged.
- `--require-proof` exits 4 unless the verdict is proven, so in M0 it exits 4 on every
  document.
- A closure-scoped boundary scan (`latex-parse/src/strict_boundary.ml`) runs over the
  whole project closure, including local `.sty`/`.cls` files and the `.bbl`, and feeds
  the why-not-strict lines with fix-it nudges. It is diagnostic: it cannot change a
  verdict or an exit code. `--strict-boundary FILE` prints every finding.
- The standing battery `corpora/strict_battery/` with a pdflatex-graded manifest.
- `PROJECT_STATE.md` §1 publishes strict-tier coverage as the North Star and moves the
  premise-certified figures under a heading that names them as a heuristic-tier
  statistic.

## Consequences

- **The published North-Star figure falls to zero and then grows.** That is the honest
  starting point, not a regression: it was never a proof. Sample 2 is now design-seen,
  so the first real strict number is reported on sample 3 (M3).
- **OPEN-024 is closed by construction in the strict tier**, because strict membership
  requires the whole closure to parse in the strict grammar. The heuristic tier is
  unchanged by this ADR, and OPEN-024 stays open there.
- **PROVEN needs pdflatex on the attestation side** (decision 3). The checker never
  compiles the body; it compiles the configuration's preamble and probe documents.
  Without pdflatex the strict tier is capped at the shipped cache, which is close to
  empty because every configuration is distinct.
- **Faithfulness is a named premise, not an axiom.** The Coq bridge takes `Faithful` as
  an explicit hypothesis, so `Print Assumptions … Closed` keeps holding, and a new gate
  will check that `Faithful` is the bridge's only non-structural premise. Faithfulness
  itself is attested by probes and a release-blocking generated differential of at
  least 10,000 documents; any disagreement blocks a release (decision 6).
- **Composition feeds prediction only.** Package contracts can produce `PENDING
  (predicted …)` or a heuristic verdict and can never produce PROVEN.
- **The trusted base is written down** (design §G.2): the pinned engine and format, the
  `Faithful` premise, the oracle protocol, the contract generator, the contract store
  and its reader, the file-system snapshot model, the byte source, the Coq kernel and
  extraction, and the renderer. Heuristic detectors and composed package contracts are
  outside it, because neither can produce or override a PROVEN verdict.
- **Two things this ADR does not do.** It does not change any heuristic verdict: M0
  moves no exit code on the real-paper samples, and that is measured in the PR. It does
  not admit `\def`: benign `\def` waits for the two termination and substitution
  theorems (decision 5), and the why-not-strict nudge tells authors how to rewrite it
  in the meantime.
