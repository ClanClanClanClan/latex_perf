# V27_FIX_PRODUCER_CADENCE — Rolling fix-producer extension to full coverage

**Goal:** Bring the catalogue of 660 lint rules from the current 32
fix-producing rules to full coverage where mechanically safe, with
explicit deferral of NLP-required and unsafe-without-context rules.

**Tag targets:** rolling — v27.0.x patches, then v27.2.x cycles.

**Scope estimate:** 60–80 sessions across 6–9 months at 1 cycle/week.

## Why the cadence

Each fix producer needs:
1. Trigger pattern analysis (what input forms fire the rule?).
2. Safe fix function (what's the minimal byte-edit that resolves
   the rule without breaking surrounding semantics?).
3. Boundary tracking (don't apply inside math/verbatim/comments).
4. Tests (positive cases + boundary-exempt negative cases).
5. `RewritePreservesCST` lemma (the byte-count invariant for the
   new fix mode).
6. Optionally `apply_best_effort` priority assignment.

Established cadence per v26.2.1 → v26.5.0: **3–10 producers per
release cycle**, taking ~1 session per producer in batched form.

## Bucket classification

The 628 remaining rules split by feasibility:

### Bucket A — mechanical, safe everywhere (~200–300 rules)
Pattern-based regex / byte-level fixes that don't require sentence
detection or semantic context. Examples:
- TYPO-NN whitespace normalization between specific token pairs
- SPC-NN trailing-whitespace inside math display modes
- ENV-NN `\begin{X}…\end{X}` argument count pinning
- CMD-NN known macro spelling corrections

**Plan:** Ship in batches of 10–15 per cycle. Existing
`apply_best_effort` infrastructure handles overlap rejection.

### Bucket B — sentence-aware (~150 rules)
Requires sentence boundary detection (existing `Spacy` integration
or a Coq sentence model). Examples:
- TYPO-NN missing space after period (only at sentence end, not in
  abbreviations)
- TYPO-NN capitalization at sentence start
- STYLE-NN passive-voice flagging

**Plan:** Wait for `Spacy` runtime maturity OR ship a conservative
Coq sentence-tokenizer pilot. Multi-cycle effort. ~10 producers
per cycle once the sentence layer is stable.

### Bucket C — context-required, unsafe-without-prompt (~150 rules)
Fixes need user disambiguation (multiple valid options) or risk
breaking semantics. Examples:
- LANG-NN ambiguous language tag (US vs UK English)
- BIB-NN citation format normalization (depends on style file)
- REF-NN `\ref` vs `\eqref` vs `\Cref` choice

**Plan:** Ship with `--apply-fixes-with-prompt` interactive flag
(new CLI surface). User reviews each fix. Multi-cycle.

### Bucket D — defer indefinitely (~30 rules)
Rules whose fix would require running pdflatex (e.g. compile-log
diagnostic rules), or rules that depend on document compilation
state. These don't admit a static fix.

**Plan:** Document as "no fix producer; runtime diagnostic only" in
`rule_contracts.yaml`.

## Stage decomposition

### v27.0.x patch cycles (Bucket A only)
Ship 10–15 mechanical producers per patch release.

**Note (2026-04-30):** The original tag-bindings below were
written assuming v27.0.2/3/4 would each carry a fix-producer
batch.  In practice those tags were repurposed for the T5
wiring cycle (v27.0.2), `apply_edits_assoc` cycle (v27.0.3), and
`cursor-universal` cycle (v27.0.4), so the fix-producer batches
have not yet shipped under these tags.  The aspirational batch
plan is preserved below as a forward-looking template; concrete
tag-bindings will be re-issued as the rolling cadence resumes
(target: first available patch tag after the active proof
cycles complete).

- ~~v27.0.2: TYPO-NN batch (10 rules)~~ — repurposed for T5 wiring
- ~~v27.0.3: SPC-NN + ENV-NN batch (12 rules)~~ — repurposed for apply_edits_assoc
- ~~v27.0.4: CMD-NN + STR-NN batch (15 rules)~~ — repurposed for cursor-universal
- (Future patches): TYPO-NN / SPC-NN+ENV-NN / CMD-NN+STR-NN
  batches resume once the proof cycles release into mainline.
- ...

Each cycle:
1. Pick 10–15 rules from Bucket A (next-up by FAMILY-NNN order).
2. Implement fix functions in `latex-parse/src/fix_producers/`.
3. Add test cases per fix.
4. Add `RewritePreservesCST` byte-count lemmas.
5. Update `rule_contracts.yaml` with `produces_fix: true`.
6. Run `pre_release_check.py` + differential test (0 diffs vs
   prior tag, since fix producers are gated behind
   `--apply-fixes`).
7. Tag patch release.

**Cumulative tracking:** maintain `specs/v27/FIX_PRODUCER_LEDGER.md`
listing each rule's bucket assignment + status (pending / shipped
in vNN / deferred).

### v27.2.0 milestone — Bucket A complete
Goal: all of Bucket A (200–300 rules) shipped. ~20 cycles at
~10/cycle. Estimated 5 months of weekly cadence.

### v27.3.0 milestone — Bucket B pilot
Sentence-aware bucket pilot ships first 30–50 rules. Requires the
sentence-tokenizer pilot to be stable.

### v27.4.0 milestone — Bucket B + C complete
Cumulative coverage of mechanically-safe fixes.

## Multi-session memory protocol

`~/.claude/.../memory/v27_fix_producer_status.md` tracks the
cumulative ledger. Per cycle: open the file, read the next batch
from `FIX_PRODUCER_LEDGER.md`, ship, update.

## Acceptance criteria

- [ ] `specs/v27/FIX_PRODUCER_LEDGER.md` exists with full bucket
  assignments for all 660 rules.
- [ ] At each patch release, ≥10 new producers shipped from Bucket
  A.
- [ ] Bucket D rules carry `produces_fix: false` in
  `rule_contracts.yaml` with documented reason.
- [ ] Differential test passes 0 diffs vs prior tag (default
  invocation; fix producers gated behind `--apply-fixes`).
- [ ] Bucket A shipped fully by v27.2.0 (target).
- [ ] Bucket B + C shipped fully by v27.4.0 (target).
