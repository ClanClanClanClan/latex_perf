# Changelog

All notable changes to LaTeX Perfectionist are documented here.

## [v27.0.61] — 2026-05-27

**+2 fix producers: CJK-001 + CJK-002** (full-width comma U+FF0C →
ASCII `,` / full-width period U+FF0E → ASCII `.`, in ASCII context).

Both rules already existed as diagnose-only Warning-severity checks
that count every U+FF0C / U+FF0E byte sequence in the source.  v27.0.61
adds a fix-set gated by two filters:

1. **Math gate** — offsets inside math segments (via
   `find_math_ranges` / `is_in_math_range`) never receive a fix; CJK
   punctuation inside math is rare but, if present, deliberate.
2. **ASCII context gate** — new helper `is_ascii_context s off` in
   `validators_common.ml` returns true iff the ±32-byte window around
   the candidate (excluding its own 3 bytes) contains strictly more
   ASCII (< 0x80) than extended (≥ 0x80) bytes.  In genuinely-CJK runs
   the heuristic returns false, the count still fires, but no fix
   edit is emitted.  Ties (ascii = extended) resolve to false — only a
   strict majority triggers replacement.

The replace edit is 3 bytes (`\xEF\xBC\x8C` for CJK-001, `\xEF\xBC\x8E`
for CJK-002) → 1 byte (`,` or `.`).  Count semantic preserved from
pre-v27.0.61 (every occurrence is tallied, regardless of math/context).

### Cross-rule note (CHAR-016)

CHAR-016 (`validators_l0.ml:1446`) also fires on U+FF0C and U+FF0E
(among 6 other fullwidth CJK punctuation chars) as a diagnose-only
Warning.  Because CHAR-016 emits no fix-set, there is no overlap at the
edit layer — both diagnostics surface, only CJK-001 / CJK-002's fix
lands at the offset.  Pattern shape mirrors v27.0.56 SPC-035 / TYPO-051
(co-firing diagnostics, single producer at the conflicting offset).

### New helper

`Validators_common.is_ascii_context ?window ?candidate_bytes s off` —
the first positive-context filter in the codebase (analogous to
`is_in_math_range` for the negative-context filter shape).  Defaults
`window=32, candidate_bytes=3`.  Future CJK / CHAR rules can reuse it
when their fix is safe only in majority-ASCII surroundings.

**89 fix-producing rules** (was 87; +2: CJK-001, CJK-002).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 87/458 → 89/458 (~19%);
`docs/index.md` Fix-producing-rules count 87 → 89.

### Counts (v27.0.61 vs v27.0.60)

- 660 catalogued rules (unchanged).
- **89 fix-producing rules** (was 87; +2).
- 92 produces_fix:false (unchanged).
- 479 produces_fix:null / pending (was 481; -2).
- 1,400 theorems / 170 .v files (unchanged).
- 18 pre-release gates + 3 build/test steps (unchanged from v27.0.60).

### Tests

- 9 new tests in `test_typo_fix.ml` (CJK-001 ASCII-context fix;
  CJK-context fires-no-fix; math-skip; multi-occurrence; ASCII-comma
  no-fire — plus the CJK-002 four-test mirror).
- 342/342 fix-producer tests PASS locally (was 333; +9).

### Differential vs v27.0.60

`run_differential_test.py --baseline-ref v27.0.60 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`;
diagnose-only counts unchanged).

## [v27.0.60] — 2026-05-25

**+2 fix producers: SPC-016 + SPC-021** (delete space before `;` / `:`).

Both are strict-subset Warning-severity delegations of TYPO-010
(space-before-punctuation, Info).  Same cross-rule filter delegation
shape as v27.0.56 (SPC-035 / TYPO-051 leading-run filter).

- **SPC-016** — for each `" ;"` (2 ASCII bytes) outside math, emits a
  single-byte delete at the leading-space offset.
- **SPC-021** — same shape for `" :"`.

Both use `find_all_non_overlapping` + `find_math_ranges` for math-aware
fix offsets while preserving the prior count semantic
(`count_substring (strip_math_segments s) needle`).

### Cross-rule integration (TYPO-010 filter)

TYPO-010 (`validators_l0_typo.ml:507`) `mk_fix_edits` `punct_chars` list
shrinks from `[',' '.' ';' ':' '?' '!']` to `[',' '.' '?' '!']`.
TYPO-010 still counts all 6 punct chars (count semantic preserved); only
the fix-set shrinks.  The cross-rule integration test
(`test_typo_fix.ml`) exercises input ` , . ; : ? !` and asserts:

- TYPO-010 fires Info (count 6) and emits 4 fixes (`,` `.` `?` `!`).
- SPC-016 fires Warning (count 1) and emits 1 fix (`;`).
- SPC-021 fires Warning (count 1) and emits 1 fix (`:`).
- Combined fix-set = 6 non-overlapping single-byte deletes / 2-byte
  replaces; `apply_all` yields `a, b. c; d: e? f!`.

### Hygiene bundled in this release

- **`scripts/tools/run_differential_test.py`** — default `--corpus`
  changed from the non-existent `corpora/regression/` to the real
  `corpora/lint/` (330 `.tex` files).  Every release cycle previously
  had to pass `--corpus corpora/lint` explicitly.
- **`docs/expert/` + `docs/coq-proof-handoff.md`** — 5 stale handoff
  files describing a long-resolved build error on the deleted
  `fix-math-strip` branch moved to
  `archive/expert-handoff/coq-fix-math-strip/` with a README explaining
  historical context.  The current proof tree builds clean with 1,400
  theorems / 0 admits / 0 axioms.

**87 fix-producing rules** (was 85; +2: SPC-016, SPC-021).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 85/458 → 87/458 (~19%);
`docs/index.md` Fix-producing-rules count 85 → 87.

### Counts (v27.0.60 vs v27.0.59)

- 660 catalogued rules (unchanged).
- **87 fix-producing rules** (was 85; +2).
- 92 produces_fix:false (unchanged).
- 481 produces_fix:null / pending (was 483; -2).
- 1,400 theorems / 170 .v files (unchanged).
- 18 pre-release gates + 3 build/test steps (`pre_release_check.py`
  gate list is 18 substantive Python checks; the previous CHANGELOG
  entries' "14 pre-release gates" count was stale since
  `check_perf_ratchet` / `check_result_helpers` /
  `check_fix_integration_wired` / `check_cst_structure_lossless` /
  `check_fix_producer_ledger` were added in later cycles).

### Tests

- 7 new tests in `test_typo_fix.ml` (SPC-016: single, multi, math-aware,
  clean; SPC-021: single, multi, math-aware, clean; cross-rule
  integration).
- 1 updated test for TYPO-010 to reflect `;`/`:` delegation.
- 333/333 fix-producer tests PASS (was 323; +10 net after delegation
  test split).

### Differential vs v27.0.59

`run_differential_test.py --baseline-ref v27.0.59 --current-ref HEAD
--corpus corpora/lint`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.59] — 2026-05-23

**+1 fix producer: SPC-025** (delete space before ellipsis `\dots` or
U+2026).

For each match of `" \dots"` (6 bytes) or `" \xe2\x80\xa6"` (4 bytes,
literal U+2026), emits a single-byte delete at the leading space
position.  Two-needle list shape; same as v27.0.17 TYPO-049 (space
after curly opening quote delete).

Cross-rule audit clean:
- TYPO-005 fires on `...` (3 dots → `\dots`), different needle.
- TYPO-053 fires on U+22EF (midline ellipsis), different needle.
- TYPO-010 (space-before-punct) excludes `\dots` (not in punct list).

Count semantic preserved from pre-v27.0.59 (sum of two
`count_substring` calls, overlapping per needle; non-overlapping fix
offsets — neither needle self-overlaps).

Severity Info preserved.

**85 fix-producing rules** (was 84; +1: SPC-025).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 84/458 → 85/458 (~18→19%);
`docs/index.md` Fix-producing-rules count 84 → 85.

### Counts (v27.0.59 vs v27.0.58)

- 660 catalogued rules (unchanged).
- **85 fix-producing rules** (was 84; +1).
- 92 produces_fix:false (unchanged).
- 483 produces_fix:null / pending (was 484; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (SPC-025: `\dots`, U+2026, multi,
  idempotent on no-leading-space).
- 323/323 fix-producer tests PASS (was 319).

### Differential vs v27.0.58

`run_differential_test.py --baseline-ref v27.0.58 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.58] — 2026-05-23

**+1 fix producer: SPC-028** (collapse runs of 2+ consecutive `~` NBSPs
to a single `~`).

For each maximal run of 2-or-more consecutive `~` (LaTeX
non-breaking-space) chars, emits a single delete edit covering the
N-1 surplus tildes (keeps the first, drops the rest).  Same shape
family as v27.0.43 TYPO-055 (`\,\,` collapse) and v27.0.15 TYPO-042
(`??+` collapse).

Count semantic preserved from pre-v27.0.58 (`count_substring s "~~"`,
overlapping: 3 tildes = 2 matches, 4 = 3, etc.).  The fix emits ONE
edit per RUN regardless of run length, so fix-edit count and
diagnostic count diverge on long runs — same pattern as TYPO-042 /
TYPO-055.

No cross-rule audit conflict: SPC-028 is the only rule firing on `~`.

Severity Warning preserved.

**84 fix-producing rules** (was 83; +1: SPC-028).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 83/458 → 84/458;
`docs/index.md` Fix-producing-rules count 83 → 84.

### Counts (v27.0.58 vs v27.0.57)

- 660 catalogued rules (unchanged).
- **84 fix-producing rules** (was 83; +1).
- 92 produces_fix:false (unchanged).
- 484 produces_fix:null / pending (was 485; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 5 new tests in `test_typo_fix.ml` (SPC-028: pair, triple, long run,
  single ~ untouched, no-tilde idempotent).
- 319/319 fix-producer tests PASS (was 314).

### Differential vs v27.0.57

`run_differential_test.py --baseline-ref v27.0.57 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.57] — 2026-05-22

**+1 fix producer: CHAR-012** (U+200D Zero-Width Joiner → delete).

Deletes each U+200D codepoint (3 bytes UTF-8 `E2 80 8D`). Simplest
single-needle delete shape; mirrors v27.0.41 CHAR-014 (U+FFFD) and
the v27.0.37..40 CHAR-006..009 batch.

Note: legitimate ZWJ uses exist in emoji sequences (e.g. 👨‍💻 = man
+ ZWJ + computer), but those are extraordinarily rare in LaTeX source
and are precisely what the rule was already warning about — the spec
description "outside ligature context" reflects that the typical
ZWJ-in-LaTeX is accidental (Word/Slack paste).  The current rule body
fires unconditionally; the fix matches that semantic.

Cross-rule audit verified clean: only HI-001 (Hindi-specific count-only
rule for ZWJ/ZWNJ adjacent to halant U+094D) also touches U+200D, and
it produces no fix — no overlap.

Severity Info preserved.  Each delete: 3 bytes → 0 bytes.

**83 fix-producing rules** (was 82; +1: CHAR-012).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 82/458 → 83/458;
`docs/index.md` Fix-producing-rules count 82 → 83.

### Counts (v27.0.57 vs v27.0.56)

- 660 catalogued rules (unchanged).
- **83 fix-producing rules** (was 82; +1).
- 92 produces_fix:false (unchanged).
- 485 produces_fix:null / pending (was 486; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (CHAR-012: single, multi, file
  boundaries, idempotent on plain ASCII).
- 314/314 fix-producer tests PASS (was 310).

### Differential vs v27.0.56

`run_differential_test.py --baseline-ref v27.0.56 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.56] — 2026-05-21

**+2 fix producers (batch): SPC-030 + SPC-035** (leading-whitespace deletion).
**Plus TYPO-051 leading-run filter** (cross-rule conflict resolution).

Both rules detect lines starting with a specific whitespace codepoint
(3 bytes UTF-8) and emit a single delete edit covering the entire
leading run:

- **SPC-030**: leading U+3000 ideographic-space (`E3 80 80`).
- **SPC-035**: leading U+2009 thin-space (`E2 80 89`).

Both are exact mirrors of v27.0.55 SPC-019 (trailing U+3000) but at
line-start.  Per the v27.0.41 batching policy: same family (SPC),
homogeneous pattern (leading-run delete), disjoint byte sequences,
per-rule + cross-rule tests, batch size 2 (≤5).

Count semantic preserved: pre-v27.0.56 each rule counted lines whose
FIRST 3 bytes match its needle; the fix may delete multiple
consecutive codepoints per matched line but emits exactly one edit
per matched line.

**TYPO-051 leading-run filter (cross-rule fix):** caught by the
in-cycle end-to-end CLI audit, the new SPC-035 conflicted with
v27.0.16 TYPO-051 (every U+2009 outside math wrapped as
`\thinspace{}`) on line-start U+2009 — both rules emitted edits
on the same byte range, causing `--apply-fixes` to refuse with an
overlap error.  Resolution: TYPO-051's fix-offset filter now skips
U+2009 positions belonging to a line-start leading run (delegating
them to SPC-035, whose delete is the more correct fix — a
`\thinspace{}` at line start would render as an unwanted opening
thin-space).  Count semantic for TYPO-051 unchanged (still counts
every U+2009); the fix-set shrinks at leading-run positions only.

**82 fix-producing rules** (was 80; +2: SPC-030 + SPC-035).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 80/458 → 82/458 (~17% → ~18%);
`docs/index.md` Fix-producing-rules count 80 → 82.

### Counts (v27.0.56 vs v27.0.55)

- 660 catalogued rules (unchanged).
- **82 fix-producing rules** (was 80; +2).
- 92 produces_fix:false (unchanged).
- 486 produces_fix:null / pending (was 488; -2).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 11 new tests in `test_typo_fix.ml`:
  - 8 for SPC-030 + SPC-035 (per-rule: single, multi-run, middle
    untouched, idempotent on clean text; plus cross-rule disjoint-needle).
  - 3 for TYPO-051 leading-run filter (skips leading single, skips
    multi-leading-run, coexists with SPC-035 non-overlapping).
- 310/310 fix-producer tests PASS (was 299).

### Differential vs v27.0.55

`run_differential_test.py --baseline-ref v27.0.55 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.55] — 2026-05-21

**+1 fix producer: SPC-019** (trailing U+3000 ideographic space → delete).

For each line ending in one-or-more U+3000 chars (3 bytes UTF-8
`E3 80 80`), emits a single delete edit covering the entire trailing
run.  Custom line-scanner (vs the pre-v27.0.55 `any_line_pred` count
helper) because the fix needs absolute byte offsets, not just a count.

Count semantic preserved: pre-v27.0.55 counted lines whose LAST 3
bytes equal `E3 80 80` (i.e. lines with ≥1 trailing U+3000).  The
fix may delete multiple consecutive U+3000 chars per matched line
(the entire trailing run), so count and edit-set agree on the
count (one edit per line) while the edit length varies.

Last-line-without-newline case handled (EOF terminates the final
line scope).  Severity Warning preserved.

**80 fix-producing rules** (was 79; +1: SPC-019).

Plus standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 79/458 → 80/458;
`docs/index.md` Fix-producing-rules count 79 → 80.

### Counts (v27.0.55 vs v27.0.54)

- 660 catalogued rules (unchanged).
- **80 fix-producing rules** (was 79; +1).
- 92 produces_fix:false (unchanged).
- 488 produces_fix:null / pending (was 489; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 5 new tests in `test_typo_fix.ml` (SPC-019: single trailing,
  multi-trailing-run collapse, middle U+3000 preserved, EOF line,
  idempotent on clean text).
- 299/299 fix-producer tests PASS (was 294).

### Differential vs v27.0.54

`run_differential_test.py --baseline-ref v27.0.54 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.54] — 2026-05-19

**+1 fix producer: CHAR-017** (fullwidth Latin letters U+FF21..U+FF3A
and U+FF41..U+FF5A → ASCII A-Z and a-z).

Replaces each fullwidth Latin codepoint (3 bytes UTF-8) with its
ASCII equivalent (1 byte):
- U+FF21..U+FF3A (Ａ..Ｚ, `EF BC A1..BA`) → ASCII A..Z;
  byte mapping `b2 - 0x60`.
- U+FF41..U+FF5A (ａ..ｚ, `EF BD 81..9A`) → ASCII a..z;
  byte mapping `b2 - 0x20`.

The NFKC-canonical fullwidth → halfwidth transform; replacement
direction is unambiguous (fullwidth Latin letters in LaTeX source
are almost universally accidental, typically from CJK paste).
Reuses the pre-v27.0.54 custom range scanner shape, same pattern
as v27.0.35 ENC-016 (fullwidth digits) but with two range branches
and per-branch offset.

Severity Warning preserved.  Each replace: 3 bytes → 1 byte.

**79 fix-producing rules** (was 78; +1: CHAR-017).

Plus the standard per-cycle cadence-doc bump:
`V27_FIX_PRODUCER_CADENCE.md` Bucket A line 78/458 → 79/458; and
`docs/index.md` Fix-producing-rules count 78 → 79.

### Counts (v27.0.54 vs v27.0.53)

- 660 catalogued rules (unchanged).
- **79 fix-producing rules** (was 78; +1).
- 92 produces_fix:false (unchanged).
- 489 produces_fix:null / pending (was 490; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (CHAR-017: uppercase pair,
  lowercase pair, mixed-case word HELLO, idempotent on plain ASCII).
- 294/294 fix-producer tests PASS (was 290).

### Differential vs v27.0.53

`run_differential_test.py --baseline-ref v27.0.53 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.53] — 2026-05-19

**+1 fix producer: CHAR-018** (precomposed Latin ligatures U+FB00..04 → ASCII).

Replaces each precomposed Latin ligature codepoint with its ASCII letter
sequence: ﬀ (U+FB00, `EF AC 80`) → `ff`, ﬁ (U+FB01) → `fi`,
ﬂ (U+FB02) → `fl`, ﬃ (U+FB03) → `ffi`, ﬄ (U+FB04) → `ffl`.
LaTeX's font ligature-substitution will re-form the glyph at
typeset time, so the visual output is preserved while making the
source portable across input encodings and fonts.

N-needle replace shape (5 needles, non-uniform replacement strings).
No math/escape/URL filter — these ligature characters carry no math
semantics and shouldn't appear inside math regions anyway. Same
shape family as v27.0.41 CHAR-005/013/014 batch.

**78 fix-producing rules** (was 77; +1: CHAR-018).

Plus post-v27.0.52 audit cleanup:
- `README.md` H1 title updated `v27.0.3` → `v27.0.53` (frozen since
  v27.0.4 era; ~48 stale cycles. Caught by line-1 grep audit;
  bundled here rather than as standalone doc-only PR).
- `V27_FIX_PRODUCER_CADENCE.md` Bucket A line bumped 77/458 → 78/458,
  per the v27.0.52 "bump every release" rule.
- `docs/index.md` Fix-producing-rules count bumped 77 → 78.

### Counts (v27.0.53 vs v27.0.52)

- 660 catalogued rules (unchanged).
- **78 fix-producing rules** (was 77; +1).
- 92 produces_fix:false (unchanged).
- 490 produces_fix:null / pending (was 491; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (CHAR-018: single fi, all-five
  combined, multi-fi, idempotent on plain ASCII).
- 290/290 fix-producer tests PASS (was 286).

### Differential vs v27.0.52

`run_differential_test.py --baseline-ref v27.0.52 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.52] — 2026-05-19

**+1 fix producer: TYPO-061** (`×` U+00D7 → `$\times$` in text mode).

Wraps each Unicode multiplication sign that appears OUTSIDE math
in inline math `$\times$` (8 bytes ASCII), realising the spec's
"prefer `\times` via math mode" guidance.  Text-mode negative-filter
shape — same as v27.0.44 CHAR-019 (U+2212 minus → ASCII `-`).
The math-mode counterpart (× inside math) is left alone; users
authoring math intentionally with × can switch to `\times` manually.

Count semantic preserved (pre-v27.0.52 `strip_math_segments`
counter), so 0 diffs vs v27.0.51 on the lint corpus.

**77 fix-producing rules** (was 76; +1: TYPO-061).

Plus `V27_FIX_PRODUCER_CADENCE.md` Bucket A acceptance-criterion
line bumped 75/458 (v27.0.50) → 77/458 (~17%) (v27.0.52), per the
established "bump every release that ships a producer" rule.

### Counts (v27.0.52 vs v27.0.51)

- 660 catalogued rules (unchanged).
- **77 fix-producing rules** (was 76; +1).
- 92 produces_fix:false (unchanged).
- 491 produces_fix:null / pending (was 492; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (TYPO-061: text-mode fix; math
  region skipped; multi-match; idempotent on clean `\times`).
- 286/286 fix-producer tests PASS (was 282).

### Differential vs v27.0.51

`run_differential_test.py --baseline-ref v27.0.51 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.51] — 2026-05-19

**+1 fix producer: MATH-097** (`=>` → `\implies` inside math).

ASCII arrow `=>` (2 bytes) replaced by the canonical LaTeX implication
macro `\implies` (8 bytes ASCII) inside math regions, subject to the
same before-byte exclusion as the count regex `[^=!<>\\]=>`: skip
when the preceding byte is in `{=,!,<,>,\}` so `==>`, `<=>`, `\=>`,
`>=>`, `!=>`, and any escaped form is never corrupted.

Math-mode-only positive filter; same shape as MATH-010 / MATH-082 /
MATH-106 / MATH-108 / MATH-015 / MATH-078.  Severity Info preserved.
Count semantic preserved (uses pre-v27.0.51 padded-segment regex
match), so 0 diffs vs v27.0.50 on the lint corpus.

**76 fix-producing rules** (was 75; +1: MATH-097).

Plus post-v27.0.50 audit cleanup: `V27_FIX_PRODUCER_CADENCE.md`
Bucket A acceptance-criterion line updated from "72/458 (~16%)
shipped as of v27.0.47" to "75/458 (~16%) shipped as of v27.0.50"
(caught by the in-cycle audit; bundled here rather than as a
standalone doc-only PR).

### Counts (v27.0.51 vs v27.0.50)

- 660 catalogued rules (unchanged).
- **76 fix-producing rules** (was 75; +1).
- 92 produces_fix:false (unchanged).
- 492 produces_fix:null / pending (was 493; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 5 new tests in `test_typo_fix.ml` (MATH-097: math-only fix; outside
  math skipped; multi-arrow; before-byte exclusion guards `==>`,
  `<=>`, `\=>`; idempotent on clean `\implies`).
- 282/282 fix-producer tests PASS (was 277).

### Differential vs v27.0.50

`run_differential_test.py --baseline-ref v27.0.50 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.50] — 2026-05-18

**+1 fix producer: MATH-010** (`÷` U+00F7 → `\div` inside math).

The spec's "prefer \frac or solidus" advice asks for an expression
RESTRUCTURING (`a÷b → \frac{a}{b}` or `a/b`) — a context-dependent
edit requiring argument parsing.  Replacing `÷` with the equivalent
`\div` macro is the conservative minimum-surprise fix: same glyph,
correct math-mode spacing, no semantic restructuring.  The
diagnostic still fires to encourage the user to consider the
restructuring option; the auto-fix gives them at least the
canonical macro form.

Math-mode-only positive filter; same shape as MATH-082 / MATH-106 /
MATH-108 / MATH-015 / MATH-078.  Severity Warning preserved.  Each
replace: 2 bytes UTF-8 → 4 bytes ASCII.

**75 fix-producing rules** (was 74; +1: MATH-010).

### Counts (v27.0.50 vs v27.0.49)

- 660 catalogued rules (unchanged).
- **75 fix-producing rules** (was 74; +1).
- 92 produces_fix:false (unchanged).
- 493 produces_fix:null / pending (was 494; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (MATH-010).
- 277/277 fix-producer tests PASS (was 273).

### Differential vs v27.0.49

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.49] — 2026-05-17

**+1 fix producer: MATH-078** (`-->` → `\longrightarrow` inside math).

The canonical LaTeX long-arrow macro renders with correct typographic
spacing; the hand-typed `-->` renders as minus + minus + greater-than
sign with no math-mode adjustment.  Math-mode-only positive filter,
same shape as MATH-015 / MATH-082 / MATH-106 / MATH-108.  Severity
Info preserved.  Each replace: 3 bytes → 15 bytes.

**74 fix-producing rules** (was 73; +1: MATH-078).

### Counts (v27.0.49 vs v27.0.48)

- 660 catalogued rules (unchanged).
- **74 fix-producing rules** (was 73; +1).
- 92 produces_fix:false (unchanged).
- 494 produces_fix:null / pending (was 495; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (MATH-078).
- 273/273 fix-producer tests PASS (was 269).

### Differential vs v27.0.48

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.48] — 2026-05-17

**Stale-checkbox doc fix + 1 new fix producer.**

### 1. Plan checkbox drift fixed

`V27_FIX_PRODUCER_CADENCE.md` had three acceptance-criteria
checkboxes that were unchecked despite being shipped long ago:
- ledger exists with 660 rules (done v27.0.34)
- Bucket D `produces_fix: false` annotations (done v27.0.42, now
  92 false-annotations covering Bucket D + NLP + redundant +
  Reserved + pending-refinement)
- differential 0 diffs vs prior tag (done v27.0.5, enforced every
  cycle)

`V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` had five unchecked items
that are all clearly shipped in v27.0.4 (we're at v27.0.48):
- ADMISSIBILITY_MAP cursor-universal entry
- docs/MERGING_GUARANTEES.md citation
- ApplyEditsAssoc.v file header
- CHANGELOG v27.0.4 entry
- Tag v27.0.4

All checked with evidence pointers.

### 2. MATH-015 fix producer (`\stackrel{` → `\overset{` inside math)

`\stackrel` is a plain-TeX legacy macro; `\overset` (amsmath) takes
the same `{top}{bottom}` argument structure and is the canonical
form.  The fix swaps only the macro name; the opening brace and
subsequent arguments are untouched.  Math-mode-only positive
filter, same shape as MATH-082 / MATH-106 / MATH-108.  Severity
Warning preserved.  Each replace: 10 bytes → 9 bytes.

**73 fix-producing rules** (was 72; +1: MATH-015).

### Counts (v27.0.48 vs v27.0.47)

- 660 catalogued rules (unchanged).
- **73 fix-producing rules** (was 72; +1).
- 92 produces_fix:false (unchanged).
- 495 produces_fix:null / pending (was 496; -1).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 4 new tests in `test_typo_fix.ml` (MATH-015).
- 269/269 fix-producer tests PASS (was 265).

### Differential vs v27.0.47

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.47] — 2026-05-17

**+2 fix producers: MATH-106 + MATH-108 math-aware replace batch.**

Both rules share the v27.0.46 MATH-082 shape exactly — math-mode-only
single-needle replace with positive `is_in_math_range` filter (the
target macros are math-mode-only, so the fix must skip text-mode
occurrences).  Disjoint byte sequences (`\not=` vs U+00B7), zero
cross-rule overlap.

- **MATH-106** — `\not=` (5 bytes) → `\neq` (4 bytes).  `\not=` is the
  TeX-primitive negation that overlays a slash on `=`; the
  semantically equivalent `\neq` is shorter and universally preferred
  by LaTeX style guides.  rules_v3.yaml default_severity=Info,
  fix=auto_replace.  Severity Info preserved.
- **MATH-108** — `·` (U+00B7 middle dot, 2 bytes UTF-8 `\xc2\xb7`) →
  `\cdot` (5 bytes).  In math mode `·` renders with wrong spacing
  for scalar product; `\cdot` is the correct macro.  Severity Info
  preserved.

**72 fix-producing rules** (was 70; +2: MATH-106, MATH-108).

### Counts (v27.0.47 vs v27.0.46)

- 660 catalogued rules (unchanged).
- **72 fix-producing rules** (was 70; +2).
- 92 produces_fix:false (unchanged).
- 496 produces_fix:null / pending (was 498; -2).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).

### Tests

- 9 new tests in `test_typo_fix.ml` (4 MATH-106 + 4 MATH-108 +
  1 combined cross-rule).
- 265/265 fix-producer tests PASS (was 256).

### Differential vs v27.0.46

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.46] — 2026-05-16

**Comprehensive spec cleanup cycle.** Addresses every remaining audit
finding from the v27.0.45 ultrathink audit.

### 1.  ENC-002 + SPC-012 redundancy properly resolved

Pre-v27.0.46: ENC-002 (`Byte-order mark U+FEFF present in middle of
file`, Error) and SPC-012 (`BOM not at file start`, Error) both
detected the same condition (BOM at non-leading offset) and BOTH
emitted IDENTICAL delete edits at IDENTICAL offsets.  Two diagnostics
for one source issue + duplicate fix-edit emission that
`apply_best_effort` had to deduplicate.  CHAR-021 was already
annotated `produces_fix: false` against this redundancy, but the
underlying runtime double-emission persisted.

Fix (proper, not bandaid):

- **SPC-012 reverts to count-only** at the runtime level
  (`mk_result_with_fix` → `mk_result`).  ENC-002 retains the canonical
  fix; the user sees one fix edit per interior BOM.
- **Bilateral `conflicts_with` declaration** added to
  `scripts/tools/generate_rule_contracts.py` `hand_audit_overrides`:
  `ENC-002 ↔ SPC-012`.  The runtime conflict resolver now suppresses
  the SPC-012 diagnostic in favor of ENC-002 (equal severity Error;
  ENC-002 wins by id-lexicographic order).
- **SPC-012 dropped from `SHIPPED_VERSIONS`** in the ledger generator.
- **SPC-012 moved to `produces_fix: false`** with the documented
  reason chain.
- Validator-DAG warning count rises from 5 to 6, all 6 are
  intentional bilateral declarations.

### 2.  Reserved-rule annotations (14 rules)

`rules_v3.yaml` carries 14 rules with `maturity: Reserved` — they
are placeholders for future spec work, lacking runtime
implementations and definitions beyond a one-line description.

Pre-v27.0.46 these had `produces_fix: null` (Bucket A pending),
mis-classifying them as eligible for fix-producer work.

Annotate all 14 explicitly as `produces_fix: false` with the
`⟦Reserved⟧` reason:

- CHAR-001, CHAR-002, CHAR-003 (3)
- MATH-001 — MATH-005, MATH-007, MATH-008 (7)
- PDF-001 — PDF-004 (4; previously fell under generic Bucket D
  annotation but now carry the more-precise Reserved reason)

### 3.  MATH-082 fix producer (`\!\!` → `\!` inside math)

Two consecutive negative thin spaces (`\!\!`, 4 bytes) compose to
roughly `-1/3 em` — overwhelmingly a typo, no standard LaTeX idiom
produces this exact byte sequence.  Math-aware fix mirrors v27.0.7
TYPO-005 / v27.0.44 TYPO-053 shape but with the math filter
INVERTED (positive — `\!` is a math-mode-only macro).

### Counts (v27.0.46 vs v27.0.45)

- 660 catalogued rules (unchanged).
- **70 fix-producing rules** (was 70; -1 SPC-012 retracted, +1
  MATH-082 added — net unchanged).
- **92 produces_fix:false** (was 81; +1 SPC-012, +10 newly-Reserved
  CHAR/MATH).  The 4 Reserved PDF entries' reason was tightened
  from the generic Bucket D to the precise Reserved reason — same
  produces_fix:false count.
- **498 produces_fix:null / pending** (was 511; -13).
- 1,400 theorems / 170 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 6 conflict declarations in validator DAG (was 5; +1 bilateral
  ENC-002 ↔ SPC-012).

### Tests

- 5 new tests in `test_typo_fix.ml` (1 SPC-012 no-fix verification +
  4 MATH-082 fix coverage).
- 256/256 fix-producer tests PASS (was 251).
- 32/32 math-ranges tests PASS.

### Differential vs v27.0.45

0 diffs across 330 corpus files (SPC-012's diagnostic suppression
and ENC-002's exclusive fix emission preserve the corpus-level
fix-application output; MATH-082's fix is gated behind
`--apply-fixes`).

## [v27.0.45] — 2026-05-16

**Spec-hardening cycle — no new fix producer.** Addresses two
long-standing pre-existing issues flagged in prior audits.

### 1. CHAR-005 VPD ↔ runtime reconciliation

Pre-v27.0.45 the VPD declared CHAR-005 as `byte_ge` 128 (any high
byte), the Coq generated proof certified that predicate, and the
OCaml runtime instead checked the low control range
`c <= 0x1F` excluding TAB/LF/CR + the bytes covered by
CHAR-006/007/008.  The Coq soundness theorem was mathematically
valid but certified the wrong predicate; my v27.0.41 CHAR-005 fix
producer shipped using OCaml semantics, deepening the gap.

Fix:
- Added `string_has_byte_in_range_excluding` to
  `proofs/RegexFamily.v`.
- Added `byte_range_excluding` pattern family to
  `scripts/infra/proof_farm/gen_coq_proofs.py`.
- Updated `specs/rules/vpd_patterns.json` CHAR-005 to
  `byte_range_excluding` 0..31 excluding `[7, 8, 9, 10, 12, 13]` —
  mirrors the OCaml runtime exactly.
- Regenerated `proofs/generated/L0_CHAR.v`.  The soundness theorem
  for `char_005_chk` now certifies the runtime semantics.

0 admits / 0 axioms preserved (the `qed_text_sound` tactic is
generic over any `string -> bool` predicate).

### 2. Direct unit tests for `find_math_ranges` + `is_in_math_range`

These helpers in `validators_common.ml` are load-bearing for 7+
math-aware fix producers (TYPO-001/004/005/012/046, TYPO-053,
CHAR-019).  Pre-v27.0.45 they were only tested INDIRECTLY through
individual producer tests.

`latex-parse/src/test_math_ranges.ml` (new): 32 direct test cases
covering empty, no-math, all 11 named envs, inline/display/paren/
bracket, escape semantics, unclosed math at EOF, and per-byte
consistency between `find_math_ranges` and `is_in_math_range`.

### Counts (v27.0.45 vs v27.0.44)

- 660 catalogued rules (unchanged).
- **70 fix-producing rules** (unchanged; v27.0.44 added TYPO-053
  and CHAR-019 in parallel which both landed before v27.0.45).
- 81 produces_fix:false (unchanged).
- 509 produces_fix:null / pending (unchanged).
- **1,400 theorems / 170 .v files** (was 1,382 / 165; +18 theorems
  and +5 files from regenerating stale generated proofs that hadn't
  picked up CMD-015/016/017, several LAY rules, and entire missing
  families STRUCT/SYS/PRT/PRJ added to the catalogue in prior cycles.
  This pre-existing drift is now corrected.  The new
  `string_has_byte_in_range_excluding` helper itself is a Fixpoint
  not a Theorem so does not contribute to the theorem count).
- 14 pre-release gates (unchanged).

### Tests

- 32 new tests in `test_math_ranges.ml`.
- 241/241 existing fix-producer tests still PASS.

### Differential vs v27.0.44

0 diffs across 330 corpus files (CHAR-005's runtime detection is
unchanged — only the Coq model changed to match it).

## [v27.0.44] — 2026-05-14

**+2 fix producers: math-aware single-needle replace batch.**

Both rules use the same pattern (mirrors v27.0.7 TYPO-005): count
preserves the pre-v27.0.44 semantic; fix uses
`find_all_non_overlapping` + `is_in_math_range` to emit replace
edits only at non-math offsets.  Disjoint byte sequences
(`e2 8b af` vs `e2 88 92`); zero cross-rule overlap.

- **TYPO-053** — U+22EF MIDLINE HORIZONTAL ELLIPSIS → `\dots`.
  In math, U+22EF could be intended as a Unicode-input equivalent
  of `\cdots` (centered dots); the fix preserves that and only
  rewrites text-mode occurrences to the canonical macro.  Each
  replace: 3 bytes → 5 bytes.  Severity Warning preserved.
- **CHAR-019** — U+2212 MINUS SIGN → `-` (ASCII hyphen).  Inside
  math, U+2212 is the typographically correct minus character;
  outside, it has no role.  Pre-v27.0.44 the count already
  filtered to text mode via `strip_math_segments`; the fix emits
  replace edits at the same text-mode offsets.  Each replace:
  3 bytes → 1 byte.  Severity Info preserved.

**70 fix-producing rules** (was 68; +2: TYPO-053, CHAR-019).

### Counts (v27.0.44 vs v27.0.43)

- 660 catalogued rules (unchanged).
- **70 fix-producing rules** (was 68; +2).
- 81 produces_fix:false (unchanged).
- 509 produces_fix:null / pending (was 511; -2).
- 1,382 theorems / 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 9 new tests in `test_typo_fix.ml` (5 TYPO-053 + 4 CHAR-019,
  including math-skip positive and negative cases, plus 1 combined
  cross-rule cross-needle test).

### Differential vs v27.0.43

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.43] — 2026-05-14

**+1 fix producer + 12 new produces_fix:false annotations.**

### New fix producer

- **TYPO-055** (`\,\,` → `\,`, collapse consecutive thin-spaces).
  Pure non-overlap replace.  A double thin-space is always a typo
  — there is no LaTeX construct where the literal four-character
  sequence `\,\,` is the intended output.

### New produces_fix:false annotations (12 rules)

Continues closing the cadence acceptance criterion #3 picture.

**Redundant with shipped producer:**
- TYPO-063 — same U+2011 byte as ENC-018 (v27.0.31).
- SPC-007  — `\n\n\n+` collapse already in TYPO-008.
- SPC-013  — whitespace-only paragraphs covered by SPC-002.
- SPC-014  — mixed LF/CRLF normalised by ENC-013.
- SPC-024  — blank-line whitespace covered by SPC-002.

**Cannot auto-fix (semantics ambiguous or unrecoverable):**
- CHAR-021 — U+FEFF inside paragraph (BOM conflict).
- ENC-001  — mixed UTF-8/Latin-1 detection (ambiguous encoding).
- ENC-003  — invalid UTF-8 byte sequences are unrecoverable.
- ENC-008  — Private-Use Area codepoints (application-defined).
- ENC-009  — same as ENC-008 (different PUA range).
- ENC-010  — variation selectors modify valid presentation.
- ENC-011  — overlaps with shipped CHAR-005 control-byte range.

**68 fix-producing rules** (was 67; +1: TYPO-055).
**81 produces_fix:false** (was 69; +12).
**511 produces_fix:null / pending** (was 524; -13).

### Counts (v27.0.43 vs v27.0.42)

- 660 catalogued rules (unchanged).
- **68 fix-producing rules** (was 67; +1: TYPO-055).
- **81 produces_fix:false** (was 69; +12).
- 1,382 theorems / 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 5 new TYPO-055 tests in `test_typo_fix.ml`.
- 241/241 fix-producer tests PASS (was 236).

### Differential vs v27.0.42

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.42] — 2026-05-13

**Closes cadence acceptance criterion #3** — no new fix producer.
Every rule in `specs/rules/rule_contracts.yaml` now carries a
`produces_fix` annotation (true / false / null) plus, for the false
case, a `fix_status_reason` describing why the rule will not ship a
producer.

Three categories of `produces_fix: false` (69 rules total):

- **Bucket D** (62 rules — FIG/FONT/PDF/L3/SYS families): defer
  indefinitely per cadence plan §Bucket D; rules depend on pdflatex
  runtime / compile-log / external-binary state and cannot be
  statically fix-produced from source bytes alone.
- **NLP-deferred** (4 rules — TYPO-019/020/030/031): Bucket B,
  require sentence tokenizer / language model.
- **Redundant or pending-refinement** (3 rules):
  - CHAR-010, CHAR-011: redundant with shipped ENC-020 (LRM/RLM
    are already deleted by ENC-020's dual-needle pattern; shipping
    a separate producer would emit duplicate edits at the same
    offset).
  - CHAR-022: current detection range U+E0000–U+E007F covers TAG
    letters U+E0020–U+E007F used inside flag emoji sequences
    post Unicode 8.0 (e.g. 🏴 + tag-letters for regional flags).
    Auto-fix would corrupt valid flag emoji.  Deferred until
    detection is narrowed to U+E0000–U+E001F (deprecated
    language-tag range only).

Implementation: `scripts/tools/generate_rule_contracts.py` gains a
`pick_produces_fix` helper that imports `SHIPPED_VERSIONS` from the
ledger generator (single source of truth, drift-checked).  No OCaml
runtime changes; `rule_contract_loader.ml` tolerates the new
optional fields.

**67 fix-producing rules** (unchanged — no new producer).

### Counts (v27.0.42 vs v27.0.41)

- 660 catalogued rules (unchanged).
- **67 fix-producing rules** (unchanged).
- **69 rules explicitly `produces_fix: false`** (was: field absent).
- **524 rules pending** (`produces_fix: null`).
- 1,382 theorems / 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

236/236 fix-producer tests PASS (unchanged).  No behavioural change
in any rule.

### Differential vs v27.0.41

0 diffs across 330 corpus files.

## [v27.0.41] — 2026-05-12

**First batch-cadence release: +3 fix producers in one PR** —
CHAR-005, CHAR-013, CHAR-014.  Marks the transition from
one-producer-per-release to homogeneous-pattern batching.

Each rule is a different already-proven pattern; three disjoint
byte ranges; zero cross-rule overlap with any shipped producer.
Combined-source test exercises the rewrite engine's multi-rule
conflict-aware merging.

- **CHAR-005** — control chars U+0000–U+001F (excluding TAB/LF/CR
  and the bytes covered by CHAR-006/007/008).  Severity Error.
  Pattern: single-byte-delete with exclusion guard.
- **CHAR-013** — bidi isolates U+2066–U+2069 (LRI/RLI/FSI/PDI).
  Severity Warning.  Pattern: N-needle list (4 needles, all 3-byte
  UTF-8 sharing prefix `e2 81`).  Mirrors v27.0.26 ENC-022.
- **CHAR-014** — Unicode replacement character U+FFFD.  Severity
  Warning.  Pattern: single 3-byte needle.  Mirrors v27.0.22
  ENC-007 / v27.0.33 ENC-023.

**67 fix-producing rules** (was 64; +3: CHAR-005/013/014).

### Batching policy

A batch is safe iff:
1. Same-family, homogeneous pattern shapes (no mixed-family batches);
2. Disjoint byte ranges across all rules in the batch and against
   every shipped producer;
3. Pure delete (no replacement decisions, no math context, no escape
   detection);
4. Each rule has its own dedicated test set + a combined cross-rule
   test exercising the rewrite engine.

The differential vs prior tag gate (already enforced) catches any
behavioural regression at corpus level regardless of which rule
introduced it.

### Counts (v27.0.41 vs v27.0.40)

- 660 catalogued rules (unchanged).
- **67 fix-producing rules** (was 64; +3: CHAR-005/013/014).
- 1,382 theorems / 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 14 new tests in `test_typo_fix.ml` (5 + 4 + 4 + 1 cross-rule).
- 236/236 fix-producer tests PASS.

### Differential vs v27.0.40

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

### Excluded from this first batch (notes for follow-on)

- **CHAR-022** (deprecated tag chars U+E0000–U+E007F): scouted, but
  current range covers U+E0020–U+E007F TAG letters used by flag
  emoji post Unicode 8.0.  Naive delete would corrupt 🏴-class
  flags.  Needs refinement (narrow to U+E0000–U+E001F language-tag
  range) before shipping.
- **CHAR-010 / CHAR-011** (LRM/RLM): already covered by v27.0.25
  ENC-020.  Annotate as `produces_fix: false` in a future cycle.

## [v27.0.40] — 2026-05-12

**+1 fix producer: CHAR-009 (Delete U+007F delete)** — fourth and final
CHAR-family single-byte-delete producer.  Closes the CHAR-006..009
block opened in v27.0.37 (backspace), continued in v27.0.38 (bell)
and v27.0.39 (form feed).  Identical shape; just a different needle
(`\x7f`).  Severity Warning preserved.

**64 fix-producing rules** (was 63; +1: CHAR-009).

### Counts (v27.0.40 vs v27.0.39)

- 660 catalogued rules (unchanged).
- **64 fix-producing rules** (was 63; +1: CHAR-009).
- 1,382 theorems (unchanged).
- 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 5 new CHAR-009 tests in `test_typo_fix.ml`.
- 222/222 fix-producer tests PASS.

### Differential vs v27.0.39

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.39] — 2026-05-12

**+1 fix producer: CHAR-008 (Form feed U+000C delete)** — third
CHAR-family producer.  Identical single-byte-delete shape to
v27.0.37 CHAR-006 and v27.0.38 CHAR-007.  Form feed is a legacy
page-break marker that some editors emit; LaTeX uses `\newpage` /
`\clearpage`, so bare U+000C in source is exclusively a paste/legacy
artifact.  Severity Warning preserved.

**63 fix-producing rules** (was 62; +1: CHAR-008).

### Counts (v27.0.39 vs v27.0.38)

- 660 catalogued rules (unchanged).
- **63 fix-producing rules** (was 62; +1: CHAR-008).
- 1,382 theorems (unchanged).
- 165 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 5 new CHAR-008 tests in `test_typo_fix.ml`.
- 217/217 fix-producer tests PASS.

### Differential vs v27.0.38

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.38] — 2026-05-12

**+1 fix producer: CHAR-007 (Bell U+0007 delete)** — second CHAR-family
producer.  Identical single-byte-delete shape to v27.0.37 CHAR-006,
just a different needle.  Bell (`\x07`) is an ASCII control byte
with no role in LaTeX source; exclusively paste/OCR artifact.

**Also: docs hygiene** — corrects long-standing `171 Coq files` claim
in README.md / docs/PROOFS.md / docs/PROOF_GUIDE.md.  The authoritative
count from `governance/project_facts.yaml` is `proof_files_total: 165`
(55 core + 109 generated + 1 ML).  Drift dated back to v27.0.10 (file
count grew 169 → 172 across the apply_edits_assoc + T5 + WS8 cycles
but the README text was never bumped, and the archive subdir is
excluded by the authoritative counter so the true tracked total is
165 not 172).  Not enforced by any gate previously; now consistent.

**62 fix-producing rules** (was 61; +1: CHAR-007).

### Counts (v27.0.38 vs v27.0.37)

- 660 catalogued rules (unchanged).
- **62 fix-producing rules** (was 61; +1: CHAR-007).
- 1,382 theorems (unchanged).
- **165 .v files** (corrected from stale `171`; unchanged in fact).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 5 new CHAR-007 tests in `test_typo_fix.ml`.
- 212/212 fix-producer tests PASS.

### Differential vs v27.0.37

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.37] — 2026-05-12

**+1 fix producer: CHAR-006 (Backspace U+0008 delete)** — opens the
CHAR family for fix production.  Pattern: scan bytes for `\x08`,
emit one `Cst_edit.delete` per occurrence, total complexity
O(N).  No regex, no math-awareness needed (control bytes are
unambiguous in any context).  Tests cover single, multiple,
boundary (BOF/EOF), and clean inputs.

This is the simplest possible fix-producer shape — single-byte
needle, plain delete, no escape detection, no overlap concerns —
and serves as the template for CHAR-007 (bell), CHAR-008 (form
feed), CHAR-009 (delete) which follow the identical pattern in
upcoming releases.

**61 fix-producing rules** (was 60; +1: CHAR-006).

### Counts (v27.0.37 vs v27.0.36)

- 660 catalogued rules (unchanged).
- **61 fix-producing rules** (was 60; +1: CHAR-006).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 14 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

- 5 new CHAR-006 tests in `test_typo_fix.ml`: single backspace,
  multiple, BOF, EOF, clean input.
- 207/207 fix-producer tests PASS.

### Differential vs v27.0.36

0 diffs across 330 corpus files (fix gated behind `--apply-fixes`).

## [v27.0.36] — 2026-05-11

**FIX_PRODUCER_LEDGER automation + pre-release drift gate** (no new
fix producer).  Resolves a post-v27.0.34 audit finding that the
ledger drifted: ENC-016 shipped in v27.0.35 but the ledger still
said "pending".  Root cause: ledger was a manual artifact; nothing
prevented drift between code and docs.

Three changes:

1. **`scripts/tools/generate_fix_producer_ledger.py`** — proper tool
   that reads all 660 rule IDs from `rule_contracts.yaml`, maintains
   a `SHIPPED_VERSIONS` dict (hand-edited per release), cross-checks
   against actual fix producers discovered in the validator source
   (`mk_result_with_fix` calls), and regenerates the ledger.  Supports
   `--check` mode for CI gating.

2. **`scripts/tools/check_fix_producer_ledger.py`** — pre-release
   gate that runs the generator with `--check` and fails if the
   on-disk ledger differs from the generated content OR if
   `SHIPPED_VERSIONS` drifts from code.

3. **`scripts/tools/pre_release_check.py`** — wires the new gate
   into the existing suite, making it gate #14.

Ledger refreshed with current state — ENC-016 now correctly marked
"shipped in v27.0.35".

Going forward: every new fix producer cycle must update
`SHIPPED_VERSIONS` + regenerate the ledger.  The gate enforces this.

**60 fix-producing rules** (unchanged — docs/automation release).

### Counts (v27.0.36 vs v27.0.35)

- 660 catalogued rules (unchanged).
- **60 fix-producing rules** (unchanged).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- **14 pre-release gates** (was 13; +1: `check_fix_producer_ledger`).
- 9 required-checks on `main` (unchanged).

### Tests

No new tests (no rule-behavior change).  202/202 fix-producer tests
PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.35 --current-ref HEAD`:
**0 diffs across 330 corpus files** (no rule behavior change).

## [v27.0.35] — 2026-05-11

**ENC-016 fix producer (fullwidth digits U+FF10–FF19 → ASCII 0-9).**
Replaces each fullwidth digit (3 bytes UTF-8 `ef bc 90..99`) with its
ASCII equivalent (1 byte `30..39`).  NFKC-canonical fullwidth →
halfwidth transform; direction is unambiguous (fullwidth digits in
LaTeX source are almost universally accidental, typically from CJK
paste).  Replacement byte derived from the third needle byte:
`b2 - 0x60` maps `0x90..0x99` to `0x30..0x39`.  Reuses v27.0.28
ENC-012's custom range scanner pattern.  Severity Warning preserved.

**60 fix-producing rules** (was 59; +1: ENC-016).

### Counts (v27.0.35 vs v27.0.34)

- 660 catalogued rules (unchanged).
- **60 fix-producing rules** (was 59; +1: ENC-016).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- single U+FF10 → '0' (positive: range start)
- single U+FF19 → '9' (positive: range end)
- full 10-char range → '0'..'9' (multi-match)
- does not fire on clean source (negative)
- does not fire on prefix-byte coincidence (U+FF0F, U+FF1A share
  `\xef\xbc` prefix but outside digit-byte range)
- idempotent on ASCII-fixed source

196 → 202 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.34 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.34] — 2026-05-11

**Docs-only: create `specs/v27/FIX_PRODUCER_LEDGER.md` (cadence plan
acceptance criterion).**  No new fix producer; no code changes.

`V27_FIX_PRODUCER_CADENCE.md` required a ledger tracking bucket
assignment (A/B/C/D) + shipping status for all 660 catalogued rules.
This file had been missing across the v27.0.5+ rolling cadence.

Generated ledger contents:
- Summary: 660 total / 59 shipped / 597 pending / 4 NLP-deferred
- Tentative bucket distribution: A=458, B=53, C=87, D=62
- Per-family breakdown for all 52 rule families
- Per-rule table (660 rows) with bucket + confidence + status
- Acceptance-criteria status against the cadence plan
- Next-pick guidance for upcoming cycles

Bucket assignments for shipped rules are CONFIRMED.  Assignments for
unshipped rules are TENTATIVE (heuristic-by-family) and should be
re-confirmed during each shipping audit.

**59 fix-producing rules** (unchanged — docs-only release).

### Counts (v27.0.34 vs v27.0.33)

- 660 catalogued rules (unchanged).
- **59 fix-producing rules** (unchanged).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

No new tests (no code change).  196/196 fix-producer tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.33 --current-ref HEAD`:
**0 diffs across 330 corpus files** (no rule behavior change).

## [v27.0.33] — 2026-05-10

**ENC-023 fix producer (narrow NBSP U+202F → regular NBSP U+00A0).**
Replaces each U+202F (3 bytes UTF-8: `e2 80 af`) with the canonical
regular non-breaking space U+00A0 (2 bytes UTF-8: `c2 a0`).  Both
preserve the no-break property; U+00A0 is the conventional NBSP
outside French typography (where U+202F is the narrow variant used
for thin spacing before colon/semicolon/etc.).  Severity Warning
preserved.

Returns to new-fix-producer cadence after v27.0.32's perf-only
release.

**59 fix-producing rules** (was 58; +1: ENC-023).

### Counts (v27.0.33 vs v27.0.32)

- 660 catalogued rules (unchanged).
- **59 fix-producing rules** (was 58; +1: ENC-023).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

4 new test cases:
- single U+202F → U+00A0 (positive)
- multiple U+202F all replaced (multi-match)
- does not fire on clean source (negative)
- idempotent (U+00A0 not in scope)

192 → 196 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.32 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.32] — 2026-05-10

**Performance: TYPO-046 adjacent-pair detection O(B×E) → O(B+E).**
The v27.0.19 round-1 audit fix (detect adjacent
`\begin{math}\end{math}` empty math envs to avoid the `$$` collision
when both delimiters are replaced with `$`) used `List.mem` against
`end_offsets` per begin — O(B×E) total.  This release replaces the
linear scans with `Hashtbl` lookups (O(1) per check) for O(B+E)
total.  Same semantics (verified by 192/192 tests still passing); no
new fix producer.

This is a release of an existing fix producer's INTERNAL
implementation, prompted by the user's live-editing-perf concern that
surfaced during the v27.0.31 cycle (where ENC-018's URL backscan was
O(N²) and got rewritten to O(N) forward-pass).

**58 fix-producing rules** (unchanged — perf-only release).

### Counts (v27.0.32 vs v27.0.31)

- 660 catalogued rules (unchanged).
- **58 fix-producing rules** (unchanged).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

No new tests (perf-only change to existing producer).  192/192
fix-producer tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.31 --current-ref HEAD`:
**0 diffs across 330 corpus files** (semantically equivalent
implementation).

## [v27.0.31] — 2026-05-10

**ENC-018 fix producer (NBHY U+2011 → `-`, URL + math-aware).**
Replaces each U+2011 (3 bytes UTF-8: `e2 80 91`) outside math AND
outside `\url{...}` with a regular hyphen-minus `-` (1 byte).

Pivot from pre-v27.0.31 implementation: scans original source
directly with `find_math_ranges` (rather than
`strip_math_segments`+s_text) so collected offsets map back to source
positions for fix-edit emission.  The URL backscan logic is preserved
(look back for `\url{` not preceded by `}`).

Inside URLs, U+2011 is sometimes intentional (preventing breaks in
hyphenated URLs) — the rule and fix both skip those.  Severity Info
preserved.

**58 fix-producing rules** (was 57; +1: ENC-018).

### Counts (v27.0.31 vs v27.0.30)

- 660 catalogued rules (unchanged).
- **58 fix-producing rules** (was 57; +1: ENC-018).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- plain text U+2011 → `-` (positive)
- inside `\url{}` preserved (URL skip)
- inside `$..$` math preserved (math skip)
- mixed (URL preserves, text fixes)
- does not fire on clean source (negative)
- multiple text NBHYs all replaced

186 → 192 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.30 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.30] — 2026-05-10

**ENC-013 fix producer (normalize mixed CRLF/LF line endings to LF).**
Pre-existing rule fires when source contains BOTH `\r\n` (CRLF) and
bare `\n` (LF) sequences; count is fixed at 1 (binary state).  The
fix replaces every `\r\n` with `\n`, leaving an all-LF result.  LF is
the cross-platform convention for source code (Git auto-converts on
Windows checkout).  Severity Info preserved.

**Distinct from prior ENC fixes**: emits N replace edits where N
depends on the CRLF count, but the rule's count remains 1.  The fix
is transformational (replaces 2 bytes with 1) rather than purely
deletive.

**57 fix-producing rules** (was 56; +1: ENC-013).

### Counts (v27.0.30 vs v27.0.29)

- 660 catalogued rules (unchanged).
- **57 fix-producing rules** (was 56; +1: ENC-013).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- mixed CRLF + LF → all CRLFs converted
- single CRLF + LF → one edit
- pure LF source (no fire — not mixed)
- pure CRLF source (no fire — not mixed)
- consecutive CRLF runs → each normalized

181 → 186 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.29 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.29] — 2026-05-10

**ENC-014 fix producer (delete UTF-16 BOM at file start, single edit
at offset 0).**  The UTF-16 BOM only ever appears at file start
(`\xFF\xFE` LE or `\xFE\xFF` BE, 2 bytes).  Distinct from prior ENC
fixes: ENC-014 has a FIXED match position rather than scanning the
whole source — the simplest possible single-edit producer.  Severity
Error preserved.  CAVEAT: this fix does not "convert" UTF-16 to
UTF-8 — if the rest of the file is genuine UTF-16, deletion leaves
garbled UTF-8 output; correct only for stray BOMs at the start of an
otherwise-UTF-8 source.

**56 fix-producing rules** (was 55; +1: ENC-014).

### Counts (v27.0.29 vs v27.0.28)

- 660 catalogued rules (unchanged).
- **56 fix-producing rules** (was 55; +1: ENC-014).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- LE BOM at file start → deleted
- BE BOM at file start → deleted
- does not fire on clean source (negative)
- does not fire on UTF-8 BOM (different bytes, ENC-002's scope)
- minimal source (BOM + 1 content byte) → content preserved

176 → 181 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.28 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.28] — 2026-05-10

**ENC-012 fix producer (delete U+0080–U+009F C1 controls, custom range
scanner).**  Pivots from N-needle list (v27.0.25-v27.0.27) to a custom
range scanner — single source pass, more efficient than 32
`List.concat_map` scans for the 32-char C1 range.  All 32 codepoints
share UTF-8 prefix `\xc2` with last byte in `\x80..\x9f`.  Severity
Error preserved (C1 controls can corrupt compilation downstream).

**55 fix-producing rules** (was 54; +1: ENC-012).

### Counts (v27.0.28 vs v27.0.27)

- 660 catalogued rules (unchanged).
- **55 fix-producing rules** (was 54; +1: ENC-012).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

7 new test cases:
- single U+0080 (range start) → deleted
- single U+009F (range end) → deleted
- single U+0090 (mid-range) → deleted
- three C1 chars in same input
- does not fire on U+007F (just below range, different encoding)
- does not fire on U+00A0 NBSP (just above range, prefix-byte coincidence)
- idempotent on already-cleaned source

169 → 176 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.27 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.27] — 2026-05-10

**ENC-024 fix producer (delete U+202A–U+202E bidi embedding/override
chars, 5-needle list).**  Deletes each of LRE (U+202A), RLE (U+202B),
PDF (U+202C), LRO (U+202D), RLO (U+202E).  All five are 3-byte UTF-8
sharing prefix `e2 80`, differing only in the third byte.  ENC-020
(v27.0.25) handles invisible bidi MARKS (LRM/RLM); this rule handles
the stronger EMBEDDINGS/OVERRIDES.  Extends the v27.0.26 ENC-022
N-needle list pattern to 5 needles.

**54 fix-producing rules** (was 53; +1: ENC-024).

### Counts (v27.0.27 vs v27.0.26)

- 660 catalogued rules (unchanged).
- **54 fix-producing rules** (was 53; +1: ENC-024).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

8 new test cases:
- single LRE, RLE, PDF, LRO, RLO each → deleted (positive ×5)
- all five chars in same input
- does not fire on clean source (negative)
- idempotent on already-cleaned source

161 → 169 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.26 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.26] — 2026-05-10

**ENC-022 fix producer (delete U+FFF9–FFFB interlinear annotation
chars, 3-needle list).**  Deletes each interlinear annotation char in
the range U+FFF9 (ANCHOR), U+FFFA (SEPARATOR), U+FFFB (TERMINATOR).
All three are 3-byte UTF-8 sequences sharing the prefix `ef bf` and
differing only in the third byte.  Used for Ruby-style annotations in
Asian text — never appropriate in LaTeX source.

Extends the v27.0.25 ENC-020 dual-needle pattern to an N-needle list
via `List.fold_left` (count) + `List.concat_map` (offsets).

**53 fix-producing rules** (was 52; +1: ENC-022).

### Counts (v27.0.26 vs v27.0.25)

- 660 catalogued rules (unchanged).
- **53 fix-producing rules** (was 52; +1: ENC-022).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- single ANCHOR (U+FFF9) → deleted (positive)
- single SEPARATOR (U+FFFA) → deleted (positive)
- single TERMINATOR (U+FFFB) → deleted (positive)
- all three chars in same input
- does not fire on clean source (negative)
- idempotent on already-cleaned source

155 → 161 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.25 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.25] — 2026-05-10

**ENC-020 fix producer (delete U+200E/U+200F LRM/RLM bidi marks,
dual-needle).**  First multi-needle ENC fix producer.  Deletes each
U+200E (Left-to-Right Mark, 3 bytes `e2 80 8e`) and each U+200F
(Right-to-Left Mark, 3 bytes `e2 80 8f`).  Both are bidirectional
control marks that influence the visual rendering order of mixed
RTL/LTR text — invisible in editors and almost universally accidental
in LaTeX source.  Mirrors v27.0.22-v27.0.24 ENC deletion shape but
extends to dual-needle (compare v27.0.17 TYPO-049 dual-needle pattern).

**52 fix-producing rules** (was 51; +1: ENC-020).

### Counts (v27.0.25 vs v27.0.24)

- 660 catalogued rules (unchanged).
- **52 fix-producing rules** (was 51; +1: ENC-020).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- single LRM → deleted (positive)
- single RLM → deleted (positive)
- both LRM and RLM in same input (3 marks)
- boundary marks at start/middle/end (4 marks)
- does not fire on clean source (negative)
- idempotent on already-cleaned source

149 → 155 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.24 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.24] — 2026-05-06

**ENC-021 fix producer (delete U+2060 WORD JOINER).**  Mirrors
v27.0.22 ENC-007 / v27.0.23 ENC-017 shape (single short UTF-8 needle,
mechanical deletion).  Pattern: U+2060 (3 bytes UTF-8: `e2 81 a0`).
The WORD JOINER prevents line-breaking between adjacent characters;
like the soft hyphen and zero-width space, it is invisible in editors
and almost universally accidental in LaTeX source.  LaTeX provides
`~` (NBSP) and `\mbox{}` for intentional break-prevention.

**51 fix-producing rules** (was 50; +1: ENC-021).

### Counts (v27.0.24 vs v27.0.23)

- 660 catalogued rules (unchanged).
- **51 fix-producing rules** (was 50; +1: ENC-021).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- single word joiner → deleted (positive)
- multiple word joiners all deleted (multi-match)
- word joiner at start/middle/end (boundary cases)
- does not fire on clean source (negative)
- idempotent on already-cleaned source

144 → 149 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.23 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.23] — 2026-05-06

**ENC-017 fix producer (delete U+00AD soft hyphen).**  Mirrors
v27.0.22 ENC-007 shape (single short UTF-8 needle, mechanical
deletion).  Pattern: U+00AD (2 bytes UTF-8: `c2 ad`).  The soft hyphen
is a discretionary line-break marker — invisible in editors but
instructs renderers to break the word at that position if needed.  In
LaTeX source it is almost always accidental (typically introduced via
web/rich-text paste); LaTeX has its own discretionary-break primitive
(`\-`) that should be used instead.  No math context concerns:
U+00AD is wrong everywhere in source.

**50 fix-producing rules** (was 49; +1: ENC-017).

### Counts (v27.0.23 vs v27.0.22)

- 660 catalogued rules (unchanged).
- **50 fix-producing rules** (was 49; +1: ENC-017).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- single soft hyphen → deleted (positive)
- multiple soft hyphens all deleted (multi-match)
- soft hyphen at start/middle/end (boundary cases)
- does not fire on clean source (negative)
- idempotent on already-cleaned source

139 → 144 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.22 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.22] — 2026-05-06

**ENC-007 fix producer (delete U+200B zero-width space).**  First fix
producer in the ENC family beyond ENC-002 (BOM deletion).  Pivots
cycle from TYPO family (pool thinning) to ENC family (22+ unfilled
rules).  Pattern: U+200B (3 bytes UTF-8: `e2 80 8b`).  Fix: simple
deletion.  Zero-width spaces are invisible in editors but cause
rendering quirks and copy-paste corruption — they are almost
universally accidental in LaTeX source (typically introduced via
web/rich-text paste).  No math context concerns: U+200B is wrong
everywhere in source.

**49 fix-producing rules** (was 48; +1: ENC-007).

### Counts (v27.0.22 vs v27.0.21)

- 660 catalogued rules (unchanged).
- **49 fix-producing rules** (was 48; +1: ENC-007).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- single ZWSP → deleted (positive)
- multiple ZWSP all deleted (multi-match)
- ZWSP at start/middle/end (boundary cases)
- does not fire on clean source (negative)
- idempotent on already-cleaned source

134 → 139 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.21 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.21] — 2026-05-05

**TYPO-012 fix producer (digit + apostrophe → digit + `^\prime`,
math-only).**  Inside math (`$...$`), `5'` denotes prime notation;
outside math it could be possessive (the 1980's) or feet/minutes
(5'2"), so the fix applies ONLY inside math.  The math filter is
POSITIVE (`is_in_math_range pos`) here — opposite of the v27.0.6+
pattern (`not (is_in_math_range pos)`) — because `'` after digit only
unambiguously means prime inside math.  Count semantic preserved
(rule fires on all matches).

**48 fix-producing rules** (was 47; +1: TYPO-012).

### Counts (v27.0.21 vs v27.0.20)

- 660 catalogued rules (unchanged).
- **48 fix-producing rules** (was 47; +1: TYPO-012).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- math `$f(5')$` → `$f(5^\prime)$` (positive)
- text `1980's` NOT fixed (math-only, conservative)
- two math primes → two edits
- does not fire on clean source
- idempotent on already-fixed math
- mixed math/text: count both, fix only math

128 → 134 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.20 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.20] — 2026-05-05

**TYPO-028 fix producer (`$$…$$` → `\[…\]`, pair-matching,
escape-aware).**  Pairs adjacent unescaped `$$` offsets greedily:
first → `\[`, second → `\]`.  Round-1 audit guards: (1)
odd-prior-backslash escape skip — `\$$` is `\$` (escaped dollar) +
`$` (open inline math), not a display-math delimiter; (2) count
semantic preserved via `count_substring s "$$" / 2` so the
differential output vs v27.0.19 is unchanged.  The fix uses the more
precise non-overlapping offsets, which can diverge on consecutive
runs like `$$$` (rule still warns but no pair → no fix).

**47 fix-producing rules** (was 46; +1: TYPO-028).

### Counts (v27.0.20 vs v27.0.19)

- 660 catalogued rules (unchanged).
- **47 fix-producing rules** (was 46; +1: TYPO-028).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

7 new test cases:
- basic positive (`$$ X $$` → `\[ X \]`)
- two disjoint pairs (4 edits)
- `$$$$` empty display math → `\[\]` (valid LaTeX)
- does not fire on clean source
- skips `\$$` (escaped, no fire)
- accepts `\\$$` (line break + real `$$`, fire)
- odd `$$$` (3 chars) → count fires but no fix (no pair)

121 → 128 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.19 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.19] — 2026-05-05

**TYPO-046 fix producer (`\begin{math}…\end{math}` → `$…$`,
escape-aware).**  Each `\begin{math}` (12 bytes) becomes `$` (1 byte);
each `\end{math}` (10 bytes) becomes `$` (1 byte) — the rewrite engine
sorts edits before applying.  Round-1 audit guard: skip matches where
the leading `\` is preceded by an odd number of backslashes —
`\\begin{math}` parses as line-break followed by literal text, and the
naive fix would corrupt this into `\$`.  Same odd-backslash-count
pattern as v27.0.14 TYPO-032 and v27.0.8 TYPO-001.

**46 fix-producing rules** (was 45; +1: TYPO-046).

### Counts (v27.0.19 vs v27.0.18)

- 660 catalogued rules (unchanged).
- **46 fix-producing rules** (was 45; +1: TYPO-046).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- basic positive (`\begin{math}x+y\end{math}` → `$x+y$`)
- two disjoint math envs (4 edits)
- does not fire on clean source
- no prior backslashes → command → fix applies
- truly-escaped (1 prior backslash) → skipped from count and fix

114 → 119 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.18 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.18] — 2026-05-05

**TYPO-017 fix producer (accent braces removal, math-aware).**
Pattern `\<accent>{<letter>}` (5 bytes) → `\<accent><letter>` (3
bytes).  Braces-removal is semantically identical in LaTeX and avoids
the UTF-8 inputenc dependency that the alternative full UTF-8
conversion would require (works on legacy docs without
`\usepackage[utf8]{inputenc}`).  Math-aware on fix offsets only.  The
accent character class is text-mode only (apostrophe, caret, backtick,
doublequote, tilde, equals, period), so math accents like `\hat{x}`
are not in scope by construction.

**45 fix-producing rules** (was 44; +1: TYPO-017).

### Counts (v27.0.18 vs v27.0.17)

- 660 catalogued rules (unchanged).
- **45 fix-producing rules** (was 44; +1: TYPO-017).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- `\'{e}` → `\'e` (acute accent positive)
- all 7 text-mode accents in one source (multi-match)
- does not fire on already-braces-removed form (idempotent)
- does not fire on multi-letter braces (regex requires single letter)
- skips `\'{e}` inside `$..$` math (math-aware audit)

109 → 114 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.17 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.17] — 2026-05-05

**TYPO-049 fix producer (delete space after curly opening quote,
math-aware).**  Pattern U+201C+space or U+2018+space → delete the
trailing ASCII space (1-byte delete at `match_offset+3`); the opening
quote itself is preserved.  Math-aware on fix offsets only; the count
uses the same dual `count_substring` sum as pre-v27.0.17 so the
differential output vs v27.0.16 is unchanged.  Multiple-spaces case
only deletes the FIRST space — TYPO-018 (collapse double space)
handles the residual run.

**44 fix-producing rules** (was 43; +1: TYPO-049).

### Counts (v27.0.17 vs v27.0.16)

- 660 catalogued rules (unchanged).
- **44 fix-producing rules** (was 43; +1: TYPO-049).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

6 new test cases:
- `delete space after U+201C` (positive, double opening quote)
- `delete space after U+2018` (positive, single opening quote)
- `both quote types in same input` (multi-match)
- `does not fire on clean source` (negative)
- `only deletes FIRST space when multiple follow` (TYPO-018 interaction)
- `skips opening-quote+space inside $..$ math` (math-aware audit)

103 → 109 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.16 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.16] — 2026-05-05

**TYPO-051 fix producer (U+2009 figure space → `\thinspace{}`,
math-aware).**  Replace each 3-byte UTF-8 figure space outside math
with `\thinspace{}`.  The trailing `{}` empty group is critical: bare
`\thinspace` followed by a letter (the common case, e.g.
`5 m`) would tokenize as the undefined command
`\thinspacem`.  In math, the LaTeX-idiomatic thin space is `\,` which
differs from `\thinspace`, so the fix conservatively skips math
contexts.

**43 fix-producing rules** (was 42; +1: TYPO-051).

### Counts (v27.0.16 vs v27.0.15)

- 660 catalogued rules (unchanged).
- **43 fix-producing rules** (was 42; +1: TYPO-051).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- `U+2009 between number and unit becomes \thinspace{}` (positive)
- `empty group {} guards against \thinspaceLETTER` (correctness audit)
- `two disjoint U+2009 produce two edits` (multi-match)
- `does not fire on clean source` (negative)
- `skips U+2009 inside $..$ math` (math-aware audit)

98 → 103 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.15 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.15] — 2026-05-04

**TYPO-042 fix producer (collapse `??...?` to single `?`,
math-aware).** Mirrors TYPO-027 (`!!!` → `!`).  Each maximal run of
two-or-more consecutive `?` is replaced with a single `?` via
`find_consecutive_runs s '?' ~min_len:2`.  Math-aware on fix offsets
only; the count uses `count_substring s "??"` (overlapping semantics)
so the differential output vs v27.0.14 is unchanged for non-math
input.

**42 fix-producing rules** (was 41; +1: TYPO-042).

### Counts (v27.0.15 vs v27.0.14)

- 660 catalogued rules (unchanged).
- **42 fix-producing rules** (was 41; +1: TYPO-042).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- `collapses ?? to single ?` (positive)
- `collapses arbitrary-length run to single ?` (5 question marks → 1)
- `two disjoint runs produce two edits` (multi-match)
- `does not fire on single ?` (negative)
- `skips ?? inside $..$ math` (math-aware audit)

93 → 98 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.14 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.14] — 2026-05-03

**TYPO-032 fix producer (delete comma before `\cite`, math-aware on
fix offsets).**  Pattern `,[ ]*\cite` (comma + zero-or-more spaces +
`\cite`) is a typographic anti-pattern; the fix deletes the comma
(single-byte delete edit at the match start) and preserves the spaces
and `\cite`.  Math-aware via `find_math_ranges` on the fix offsets
only; the count preserves the pre-v27.0.14 semantic so the
differential output vs v27.0.13 is unchanged.

**41 fix-producing rules** (was 40; +1: TYPO-032).

### Counts (v27.0.14 vs v27.0.13)

- 660 catalogued rules (unchanged).
- **41 fix-producing rules** (was 40; +1: TYPO-032).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases:
- `deletes comma before \cite` (positive)
- `deletes comma even with no space before \cite` (no-space variant)
- `two disjoint comma+\cite produce two edits` (multi-match)
- `does not fire on clean source` (negative)
- `skips comma+\cite inside $..$ math` (math-aware audit)

86 → 91 tests PASS.

### Differential test

`run_differential_test.py --baseline-ref v27.0.13 --current-ref HEAD`:
**0 diffs across 330 corpus files** (fix gated behind `--apply-fixes`).

## [v27.0.13] — 2026-05-03

**TYPO-039 fix producer (URL → `\url{}`, math + already-wrapped
aware).**  Wraps each non-math, not-already-wrapped URL match
with `\url{URL}`.  Skip if URL is already inside `\url{}` or
the URL slot of `\href{}`.  Reuses v27.0.6 `find_math_ranges`
helper.

**40 fix-producing rules** (was 39; +1: TYPO-039).

### Counts (v27.0.13 vs v27.0.12)

- 660 catalogued rules (unchanged).
- **40 fix-producing rules** (was 39; +1: TYPO-039).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

4 new test cases:
- `bare URL becomes \url{...}` (positive)
- `two URLs get two wraps` (multi-match)
- `does not fire when already wrapped` (`\url{}` skip)
- `does not fire on URL inside \href slot` (`\href{}` skip)

79 → 83 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.12`.

## [v27.0.12] — 2026-05-03

**TYPO-029 fix producer (NBSP after `\ref`, math-aware).**  Pattern
`\ref{X} y` (regular space between `}` and a letter) is rewritten
to `\ref{X}~y`.  Reuses v27.0.6 `find_math_ranges` helper for
math-aware filtering.

**39 fix-producing rules** (was 38; +1: TYPO-029).

### Counts (v27.0.12 vs v27.0.11)

- 660 catalogued rules (unchanged).
- **39 fix-producing rules** (was 38; +1: TYPO-029).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

4 new test cases:
- `space after \ref{X} becomes ~` (positive)
- `two \ref sites get two replacements`
- `does not fire when ~ already present`
- `does not fire on \ref followed by punctuation`

74 → 78 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.11`.

## [v27.0.11] — 2026-05-03

**TYPO-034 fix producer (delete spurious space before `\footnote`,
math-aware).**  Each ` \footnote` occurrence outside math has the
leading space deleted.  Convention: footnote marks should attach
directly to the preceding word with no space.  Reuses v27.0.6
`find_math_ranges` helper.

**38 fix-producing rules** (was 37; +1: TYPO-034).

### Counts (v27.0.11 vs v27.0.10)

- 660 catalogued rules (unchanged).
- **38 fix-producing rules** (was 37; +1: TYPO-034).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

4 new test cases:
- `deletes space before \footnote` (positive)
- `two footnote sites get two deletions`
- `skips \footnote inside math`
- `does not fire on clean source`

70 → 74 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.10`.

## [v27.0.10] — 2026-05-03

**TYPO-038 audit refinement.**  Round-1 audit of v27.0.9 caught
two correctness issues in the `already_wrapped` prefix-byte
check:

1. **False-positive**: `Send to mailto:alice@x.com` (literal text
   "mailto:" without a `\href`) had its email skipped, because
   the check matched the bare `mailto:` prefix.
2. **False-negative** for what we want to FIX: `\textbf{label}{a@b.io}`
   had its email skipped, because the check matched the bare
   `}{` prefix without verifying it was inside a `\href`.

Plus the squash-merge of PR #340 dropped the round-1 integration
test (commit `1026e1b`) — third recurrence of
`feedback_squash_merge_drops_late_commits.md`.

**Fix**: replace the prefix-byte check with `find_href_mailto_ranges`,
which scans for the literal `\href{mailto:` opener and walks to
the matching `}{...}` closer.  Only emails whose start offset
falls within a complete `\href{mailto:...}{...}` range are
treated as already-wrapped.

Restored the dropped integration test plus added two new tests
covering the false-positive and false-negative cases.

### Counts (v27.0.10 vs v27.0.9)

- 660 catalogued rules (unchanged).
- **37 fix-producing rules** (unchanged — refinement to existing
  TYPO-038, not a new producer).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

3 new test cases (1 restored + 2 new):
- `math + wrapped + plain integration` (restored from `1026e1b`)
- `literal mailto: text is NOT skipped` (round-1 false-positive)
- `non-href two-arg command does NOT mask email` (round-1
  false-negative)

67 → 70 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.9` (corpus has no
edge cases that exercise the audit findings; refinement is a
correctness improvement that doesn't affect typical inputs).

## [v27.0.9] — 2026-05-03

**TYPO-038 fix producer (email → `\href{mailto:...}{...}`,
math-aware + already-wrapped detection).**  Wraps each
non-math, not-already-wrapped email match.  Reuses v27.0.6
`find_math_ranges` helper and adds `already_wrapped` check
that detects emails preceded by `mailto:` (already inside
the link's URL slot) or `}{` (already inside the link's
display slot).

**Semantic shift from pre-v27.0.9**: the old TYPO-038 counted
ALL email patterns including those already inside `\href{mailto:}`
wrappers, so the rule fired on already-correct documents.  The
v27.0.9 form counts only UNWRAPPED non-math emails — matching
the rule's stated intent ("E-mail address not in \href").
Differential test passes 0 diffs vs v27.0.8 (corpus has no
pre-wrapped emails so the semantic shift is invisible to
existing tests).

**37 fix-producing rules** (was 36; +1: TYPO-038).

### Counts (v27.0.9 vs v27.0.8)

- 660 catalogued rules (unchanged).
- **37 fix-producing rules** (was 36; +1: TYPO-038 with
  already-wrapped detection + math filtering).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

3 new test cases:
- `bare email becomes \href{mailto:...}{...}` (positive)
- `two emails get two wraps` (multi-match)
- `does not fire on clean source` (pre-wrapped detection)

64 → 67 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.8`.  Semantic shift
in detection has no effect on the corpus (no pre-wrapped
emails present).

## [v27.0.8] — 2026-05-03

**TYPO-001 fix producer (ASCII straight quote → curly,
math-aware via alternation).**  Closes the v27.0.5 / v27.0.6
deferred TYPO-001 deferral.  Disambiguation: index-based
ALTERNATION across straight-quote occurrences outside math —
even-index → U+201C (left/opening), odd-index → U+201D (right/
closing).  Works for well-formed documents with matched pairs
("hello"-style → curly-pair); for odd-count input, gives best-
effort with parity-determined trailing quote.

Reuses v27.0.6 `find_math_ranges` helper.  Count semantic
preserved: count_char on strip_math_segments output (math-mode
quotes don't fire, same pre-v27.0.8 behaviour); fix emits at
original-string offsets through find_math_ranges.

**With this cycle, all three v27.0.5 deferrals are resolved:**
- TYPO-004 (curly-quote conversion) — shipped v27.0.6
- TYPO-005 (`...` → `\dots`) — shipped v27.0.7
- TYPO-001 (ASCII quote → curly) — shipped v27.0.8

**36 fix-producing rules** (was 35; +1: TYPO-001).

### Counts (v27.0.8 vs v27.0.7)

- 660 catalogued rules (unchanged).
- **36 fix-producing rules** (was 35; +1: TYPO-001 with
  alternation + math filtering).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases in `latex-parse/src/test_typo_fix.ml`:
- `matched pair becomes curly-pair via alternation`
- `two matched pairs alternate correctly` (4 quotes → 4 edits)
- `skips quotes inside $..$ math`
- `does not fire when quotes only in math`
- `does not fire on clean source`

56 → 61 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.7`.

## [v27.0.7] — 2026-05-03

**TYPO-005 fix producer (`...` → `\dots`, math-aware).**  Reuses
the v27.0.6 `find_math_ranges` helper to filter match offsets.
Math-mode ellipsis (`$1, 2, ..., n$`) is detected (count
unchanged: stripped buffer) but NOT auto-fixed; text-mode `...`
is replaced with `\dots`.

**Pattern divergence from TYPO-004**: count uses
`count_substring (strip_math_segments s) "..."` (overlapping
count for severity, preserves the pre-v27.0.7 detection
semantic — math-only `...` doesn't fire); fix uses
`find_all_non_overlapping s "..." |> filter (not in math)`
(non-overlapping for non-conflicting edits).  Documented
inline; matches the established TYPO-002/003 overlapping-vs-
non-overlapping precedent.

**35 fix-producing rules** (was 34; +1: TYPO-005).  TYPO-001
still deferred — needs open-vs-close curly-quote
disambiguation (likely alternation heuristic in v27.0.8+).

### Counts (v27.0.7 vs v27.0.6)

- 660 catalogued rules (unchanged).
- **35 fix-producing rules** (was 34; +1: TYPO-005 with
  math-aware filtering).
- 1,382 theorems (unchanged).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Tests

5 new test cases in `latex-parse/src/test_typo_fix.ml`:
- `... in text becomes \dots` (text-mode positive)
- `skips ... inside $..$ math` (inline math preservation)
- `skips ... inside \[..\] display math` (display preservation)
- `does not fire when ... is only in math` (count semantic
  preserved)
- `does not fire on clean source`

51 → 56 tests PASS.

### Differential test

0 diffs across 330 corpus files vs `v27.0.6`.  Fix gated behind
`--apply-fixes`; baseline output unchanged.

## [v27.0.6] — 2026-05-02

**Math-range helper unblocks deferred fix producers.** Adds
`find_math_ranges` + `is_in_math_range` to `validators_common.ml`,
exposing half-open byte ranges of math segments rather than
producing a stripped buffer.  Fix producers can now filter match
offsets that fall inside math segments without changing detection-
time count behaviour.

Math syntaxes recognised: inline `$..$`, **display `$$..$$`
(matched-pair detection — deliberately MORE correct than
`strip_math_segments`, which uses a single-`$` toggle that parses
`$$x$$` as two empty math + literal middle)**, paren math
`\(...\)`, bracket math `\[...\]`, and 11 named math environments
(`equation`, `align`, `gather`, `multline`, `eqnarray`,
`displaymath`, plus starred variants and `math`).  Verbatim
(`\verb|...|`) and comments (`% ...`) deliberately not tracked —
matches the established cadence of v26.x fix producers.

**Wired into TYPO-004** (deferred from v27.0.5 cycle): ` `` ` →
U+201C left double quote, `''` → U+201D right double quote,
**but only outside math**.  `''` inside `$f''(x)$` (double-prime
notation) is detected (count) but not auto-fixed.  Test suite
covers ten math/non-math contexts: inline `$..$`, display
`$$..$$` (round-2 audit fix), paren `\(..\)` (round-6 audit),
bracket `\[..\]`, `\begin{equation}` env, math-only input (no
fix edits), text-only (fix applies), escaped `\$` (round-1
audit), three interleaved math regions (round-1 audit), and
backtick-pair-inside-math symmetry (round-5 audit).

**34 fix-producing rules** (was 33; +1: TYPO-004).  TYPO-005 +
TYPO-001 still deferred — same helper applies, but they need
context-dependent open-vs-close logic (TYPO-001) or math-aware
count semantics distinct from the existing strip_math behaviour
(TYPO-005).  Tracked for v27.0.7+.

### Counts (v27.0.6 vs v27.0.5)

- 660 catalogued rules (unchanged).
- **34 fix-producing rules (was 33; +1: TYPO-004 with math-aware
  filtering)**.
- 1,382 theorems (unchanged; fix-producer cycle, not a proof cycle).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Differential test

0 diffs across 330 corpus files vs `v27.0.5` (default invocation).
Fix producer gated behind `--apply-fixes`; baseline output
unchanged.

## [v27.0.5] — 2026-05-02

**Fix-producer cadence resumes.** v27.0.5 opens the rolling Bucket A
fix-producer cycle (per `specs/v27/V27_FIX_PRODUCER_CADENCE.md`)
deferred by the v27.0.0–v27.0.4 proof-stack work. One mechanical
producer shipped:

- **TYPO-010** (space before punctuation): each `<space><,.;:?!>`
  pair drops the leading space, leaving the punctuation in place.
  Operates on the raw byte stream; the `L0_TOKEN_AWARE` path uses
  the stricter token-level count but emits the same byte edits.
  Math/verbatim concerns: in math, spaces are insignificant so
  removing space before comma is benign; verbatim corruption
  matches the existing TYPO-002/003 pattern (no boundary tracking
  in v26.x fix producers either) — accepted per established
  cadence.

**Deferred from this batch (audit-caught correctness concern):**
TYPO-004 (` ``…'' ` → curly quotes) was implemented but reverted
during round-1 audit.  Reason: `''` in LaTeX math is double-prime
notation (e.g., `$f''(x)$`), so auto-replacing with U+201D would
corrupt math source.  Proper fix requires a math-range helper
that exposes "is offset X inside a math segment" — tracked for
v27.0.6 cycle, where the same helper unblocks TYPO-005
(` ... ` → `\dots`) and TYPO-001 (open vs close curly quote).

**33 fix-producing rules** (was 32; +1).  TYPO-010 ships with E2E
unit tests in `latex-parse/src/test_typo_fix.ml` (positive cases,
multi-pattern cases, no-fire negatives) and exercises the existing
`apply_fixes_best_effort` infrastructure unchanged.

**Plus: CI fix.** `scripts/perf_summary.sh` removed an
`OPAMSWITCH=l0-testing` override that broke `perf-nightly` on
GitHub Actions runners (the nightly workflow had been failing every
night since 2026-04-28; preceding gates all passed, only the
post-gate CSV summary step errored). Switch override now respects
the ambient opam environment per CI norms (PR #335).

### Counts (v27.0.5 vs v27.0.4)

- 660 catalogued rules (unchanged).
- **33 fix-producing rules (was 32; +1: TYPO-010)**.
- 1,382 theorems (unchanged; this is a fix-producer cycle, not a
  proof cycle).
- 171 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Differential test

0 diffs across 330 corpus files vs `v27.0.4` (default invocation).
Fix producers gated behind `--apply-fixes`; baseline output
unchanged.

## [v27.0.4] — 2026-05-01

**Cursor-universal cycle complete: universal runtime correspondence.**
The OCaml `Cst_edit.apply_all` (sort ascending + cursor walk) and the
Coq `apply_edits_parallel` (sort descending + sequential applier)
produce the same byte stream for **every valid edit list** —
mechanically certified, not just the four corpus-level reflexivity
Examples shipped at v27.0.3.

**1,382 theorems / 171 .v files / 0 admits / 0 axioms** (v27.0.3
had 1,342 / 171; +40 from `proofs/ApplyEditsAssoc.v` cursor-universal
Stages 1–5).

### Headline theorem

```coq
Theorem apply_edits_cursor_eq_parallel :
  forall (src : bytes) (es : list edit),
    distinct_starts es ->
    pairwise_non_overlapping es ->
    (forall e, In e es -> edit_wf e) ->
    (forall e, In e es -> e.(e_end) <= length src) ->
    apply_edits_cursor src es = apply_edits_parallel src es.
```

`Print Assumptions apply_edits_cursor_eq_parallel` returns "Closed
under the global context".

### Shipped (5 stage PRs + Stage 6 docs + this release-bump)

| PR | Stage | Content |
|---|---|---|
| #325 | Stage 1 | symmetric ascending-sort permutation + sortedness lemmas (`insert_asc_swap_distinct`, `sort_by_start_asc_perm`, `sort_by_start_asc_sorted`, `sort_by_start_asc_id_when_sorted`, `insert_asc_preserves_sorted`, `ascending_sorted` Inductive) |
| #326 | Stage 2 | bridge lemma `sort_by_start_desc_eq_rev_asc` (descending-sort = reverse of ascending-sort on `distinct_starts` inputs) + 9 supporting lemmas + 4 reflexivity Examples |
| #328 | Stage 3 | `cursor_walk_canonical` Fixpoint + `apply_edits_cursor_aux_shape` (cursor-walk = canonical, unconditional) + plan-signature variant + 2 Examples |
| #329 | Stage 4 (substantive) | `apply_edits_concrete_rev_sorted_shape` — for sorted-ascending non-overlapping in-bounds distinct-starts well-formed edits, the parallel applier on `rev sorted_asc` equals the cursor walk's canonical form. 14 supporting lemmas covering take/drop ↔ firstn/skipn bridges, predicate cons-inversions, and two cursor_walk_canonical manipulation lemmas |
| #330 | Stage 5 (UNIVERSAL HEADLINE) | `apply_edits_cursor_eq_parallel` Qed combining Stages 1–4 via `pairwise_non_overlapping_perm` + four sort-permutation precondition lifts |
| #332 | Stage 6 | wire universal extension into `proofs/ADMISSIBILITY_MAP.md` + `docs/MERGING_GUARANTEES.md` + `proofs/ApplyEditsAssoc.v` file header (no "future extension" framing remains) |

### Why the universal extension matters

Without this cycle: the v27.0.3 runtime-correspondence claim is
mechanised on 4 representative inputs (Stage 5b reflexivity Examples)
but not universally. The user-facing docs say "achievable via
induction; multi-session future extension" — exactly the deferral
pattern that `feedback_no_multi_week_dismissal` corrects against.

With this cycle: the runtime-Coq correspondence is mechanically
certified for every valid edit list (any size, any shape that
satisfies `distinct_starts /\ pairwise_non_overlapping /\ edit_wf
/\ in-bounds`). The "queued as future" framing is replaced with a
shipped theorem reference.

### Plan signature deviations (documented inline)

- **Stage 3** ships `cursor_walk_canonical` as a Coq Fixpoint
  rather than a "non-recursive byte-mapping function" (any
  non-recursive form for variable-length lists is just a fold over
  a recursive helper — observably equivalent). Predicate naming
  uses repo-style lowercase (`ascending_sorted`,
  `non_overlapping_from`, `all_in_bounds`). The shipped
  `apply_edits_cursor_aux_shape` is unconditional; a plan-signature
  `_with_preconds` variant is also shipped.
- **Stage 4** strengthens preconditions with `distinct_starts` +
  per-element `edit_wf` (rules out same-start insertions and
  negative-range edits where the equation would fail). Both
  additional preconditions are present in Stage 5's user-facing
  theorem signature.

### Round-9 audit fix: lost-during-squash dup removal

A late-pushed commit (`19ce776`, removing a duplicate
`apply_edits_concrete_singleton` accidentally added in Stage 4 PR
#329) was lost from PR #330's squash merge per
`feedback_squash_merge_drops_late_commits`. The dup re-appeared on
main; cherry-picked back into PR #332 (commit `086d02b`). Verified
post-merge that only the authoritative
`RewritePreservesCST.v:290` definition remains.

### Differential test

0 diffs across 330 corpus files vs `v27.0.3`. v27.0.4 is purely
formal/Coq + docs — no runtime change.

### Counts (v27.0.4 vs v27.0.3)

- 660 catalogued rules (unchanged).
- 32 fix-producing rules (unchanged).
- 1,382 theorems (was 1,342; +40 from `ApplyEditsAssoc.v`
  cursor-universal Stages 1–5).
- 171 .v files (unchanged; cursor-universal extends
  `ApplyEditsAssoc.v` only).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

## [v27.0.3] — 2026-04-30

**`apply_edits` associative-reorder cycle complete.** Closes the
v26.4-deferred `apply_edits_concrete_associative_subset` theorem
under the corrected name `apply_edits_parallel_perm` (the original
form was provably FALSE — see Stage 2 file-header counter-example).
Substantive headline: for permutation-equivalent edit lists with
distinct start positions, the parallel applier produces equal byte
streams. Closed under the global context.

**1,342 theorems / 171 .v files / 0 admits / 0 axioms** (v27.0.2
had 1,321 / 170; +21 from `proofs/ApplyEditsAssoc.v` Stages 1–5b).

### Shipped (5 stage PRs + this release-bump)

| PR | Stage | Content |
|---|---|---|
| #319 | Stage 1 | `proofs/ApplyEditsAssoc.v` scaffolded with `non_overlapping` predicate + 5 sanity lemmas |
| #320 | Stage 2 | parallel-application Fixpoint (sort by `e_start` descending + `apply_edits_concrete`); documented FALSE original Stage 4 form via 6-byte counter-example |
| #321 | Stage 3 | sort idempotence + sorted equivalence + plan revision |
| #322 | Stage 4 (substantive headline) | `apply_edits_parallel_perm` Qed via insertion-sort permutation invariance on distinct-key inputs |
| #323 | Stage 5 + 5b | ADMISSIBILITY_MAP wire-in + new `docs/MERGING_GUARANTEES.md` user-facing doc + Stage 5b cursor-walk Coq mirror of OCaml `Cst_edit.apply_all` (4 corpus-level reflexivity Examples + empty-list base lemmas); plus `V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` (7-stage plan committing the universal extension as v27.0.4 work) |

### Headline theorem

```coq
Theorem apply_edits_parallel_perm :
  forall src es1 es2,
    Permutation es1 es2 ->
    distinct_starts es1 ->
    apply_edits_parallel src es1 = apply_edits_parallel src es2.
```

`Print Assumptions apply_edits_parallel_perm` returns "Closed
under the global context".

### Why the original form was false

For non-overlapping edits e1 = (1,3,"X") and e2 = (4,5,"YZ") on
src "abcdef":
- `apply_edits_concrete src [e1;e2]` → "aXdeYZ" (e2's offset 4
  hits modified-buffer "aXdef"[4]='e')
- `apply_edits_concrete src [e2;e1]` → "aXdYZf" (e1's offset 1
  hits modified-buffer "abcdYZf"[1]='b')
- Sequential applier interprets offsets relative to the *current*
  buffer, not the original source — so reordering changes output.

The parallel applier (sort descending by `e_start`, then apply via
`apply_edits_concrete`) IS order-invariant because applying the
rightmost edit first leaves all smaller offsets unchanged in the
remaining buffer.

### Runtime correspondence (mechanised at corpus level)

`proofs/ApplyEditsAssoc.v` Stage 5b adds `apply_edits_cursor` —
a Coq mirror of the OCaml `Cst_edit.apply_all` algorithm
(ascending sort + cursor walk through original src) — and 4
reflexivity Examples proving `apply_edits_cursor src es =
apply_edits_parallel src es` on representative inputs. The
**universal extension** is committed as
`specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md` (7 stages,
target tag v27.0.4).

### New documents

- `docs/MERGING_GUARANTEES.md` (user-facing): two-appliers
  explanation, counter-example, substantive theorem statement,
  `distinct_starts` edge cases, runtime correspondence, see-also
  references.
- `specs/v27/V27_APPLY_EDITS_CURSOR_UNIVERSAL_PLAN.md`: 7-stage
  plan for the universal `apply_edits_cursor_eq_parallel` theorem.
- `proofs/ADMISSIBILITY_MAP.md`: new "Rewrite engine —
  associative-reorder (DISCHARGED in v27.0.3)" entry.

### Differential test
0 diffs across 330 corpus files vs `v27.0.2`. v27.0.3 is purely
formal/Coq + docs — no runtime change.

### Counts (v27.0.3 vs v27.0.2)
- 660 catalogued rules (unchanged).
- 32 fix-producing rules (unchanged).
- 1,342 theorems (was 1,321; +21 from ApplyEditsAssoc.v Stages 1–5b).
- 171 .v files (was 170; +1: `proofs/ApplyEditsAssoc.v`).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

## [v27.0.2] — 2026-04-29

**v27 T5 wiring complete.** Closes the last "Genuinely multi-week
items needing stage-decomposed plans" deferred from v27.0.1: `T5_safe`
substantively wired to `T5_wrapper` via the 6-stage plan in
`specs/v27/V27_T5_WIRING_PLAN.md`. The WS8 capstone is now fully
spec-compliant end-to-end — every T0–T5 predicate substantively
connects to its LP-Core wrapper or canonical source. No more `True`
placeholders for the supported-profile capstone.

**1,321 theorems / 170 .v files / 0 admits / 0 axioms** (v27.0.1
had 1,317 / 169; +4 from `T5_concrete` stages 2–5 + `PdflatexT5Wired`
catalogue instance + corollary).

### Shipped (5 stage PRs + this release-bump)

| PR | Stage | Content |
|---|---|---|
| #313 | Stage 1 | `proofs/T5_concrete.v` scaffolded with `rule_id := string` + placeholder predicates |
| #314 | Stage 2 | `pdflatex_rule_safety_rule_proof` (Qed) + `pdflatex_T5_safe_stage2` (Qed) Section closure of `T5_wrapper.T5_rule_safe` |
| #315 | Stage 3 | `pdflatex_rule_passes_pred` made Section-parametric in `rule_catalogue : list rule_id` (avoids circular dep with `Generated.Catalogue`); refined to `In r rule_catalogue` |
| #316 | Stage 4 | `pdflatex_no_static_violation_pred` refined from `True` to `Forall (In rule_catalogue) rules`; discharge proof now consumes the premise via `Forall_forall` |
| #317 | Stage 5 | `proofs/PdflatexModel.v::pdflatex_T5_safe` rewritten from `True` to universal-over-catalogue substantive form; new `proofs/generated/PdflatexT5Wired.v` derives the `Generated.Catalogue.all_proved_rule_ids`-specific instance + corollary for the full catalogue |

### Architectural note

The natural source of truth for "rules with per-rule QEDs" is
`LaTeXPerfectionist.Generated.Catalogue.all_proved_rule_ids`. But
`Generated` already depends on `LaTeXPerfectionist`, so direct import
from main-library files (`T5_concrete`, `PdflatexModel`) creates a
circular theory dependency. The Stage 3+5 design solves this:

- `T5_concrete.v` uses a Section variable `rule_catalogue` so the
  catalogue is parametric, not imported.
- `PdflatexModel.v::pdflatex_T5_safe` is universal over the catalogue
  at the predicate level.
- `proofs/generated/PdflatexT5Wired.v` (in `Generated`, downstream)
  derives the `all_proved_rule_ids`-specific instance.

This keeps the WS8 capstone in the main library while the
catalogue-specific witness lives where it can see both
`PdflatexModel` and `Catalogue`.

### Honest scope (v27 WS9+ deferred per `V27_T5_WIRING_PLAN.md`)

A fully project-attached "no rule fires on p" claim — connecting
per-rule QEDs to actual span emissions via a runtime validator
emit-relation model — remains genuinely multi-day work and is
honestly deferred to v27 WS9+. Stage 4's `Forall (In rule_catalogue)
rules` shape is the strongest substantive predicate without that
runtime bridge.

### Remaining v27 multi-week plans (per the plan files)

- `specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md` — operational pdflatex
  semantics (token-driven aux/log evolution) — 7 stages, capstone tag
  v27.1.0
- `specs/v27/V27_FIX_PRODUCER_CADENCE.md` — bucket-classified rolling
  cadence (628 rules) — v27.0.x → v27.4.0
- `specs/v27/V27_L3_AST_PLAN.md` — L3 AST migration — 10 stages,
  capstone tag v27.2.0
- `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md` — apply_edits
  associative-reorder — 6 stages

### Differential test
0 diffs across 330 corpus files vs `v27.0.1`. v27.0.2 is purely
formal/Coq — no runtime change.

### Counts (v27.0.2 vs v27.0.1)
- 660 catalogued rules (unchanged).
- 32 fix-producing rules (unchanged).
- 1,321 theorems (was 1,317; +4 from T5 stages 2–5 + PdflatexT5Wired).
- 170 .v files (was 169; +1: `proofs/generated/PdflatexT5Wired.v`).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

## [v27.0.1] — 2026-04-28

**v27 WS8 spec-compliance follow-up.** Closes 3 of the 4 items the
v27.0.0 CHANGELOG misclassified as "Deferred to v27 WS9+" — they
were closeable in 90 minutes total once attempted, not multi-day.
Proof-only release; 0 differential diffs vs v27.0.0 across 330
corpus files.

**1,317 theorems / 169 .v files / 0 admits / 0 axioms** (v27.0.0
had 1,312 / 169; +5 from the new `_holds` lemmas + extended marker
predicates).

### Closed in this release

1. **T0/T1/T4 wired to LP-Core wrappers** (per `V27_WS8_PLAN.md` §2
   original mandate):
   - `pdflatex_T0_accepts (_ : pdflatex_project) := forall (n :
     ParserSound.node), exists flat, ParserSound.flatten n = flat`,
     discharged by `pdflatex_T0_accepts_holds` (Qed) via
     `T0_wrapper.T0_parser_accepts`.
   - `pdflatex_T1_admissible (_ : pdflatex_project) := forall c1
     c2 : UserExpand.catalog, acyclic c1 -> acyclic c2 -> ... ->
     acyclic (merge c1 c2)`, discharged by
     `pdflatex_T1_admissible_holds` (Qed) via
     `T1_wrapper.T1_expansion_admissible_merge`.
   - `pdflatex_T4_coherent (_ : pdflatex_project) := forall labels,
     ProjectSemantics.labels_unique labels -> forall n f1 f2,
     In (n,f1) labels -> In (n,f2) labels -> f1 = f2`, discharged
     by `pdflatex_T4_coherent_holds` (Qed) via
     `T4_wrapper.T4_labels_unique_packaged`.
   - `pdflatex_compile_safe`'s capstone proof updated: the four
     T0/T1/T4/T5 hypothesis discharges now go through the
     corresponding `_holds` lemmas instead of `exact I`.

2. **Extended fatal-marker detection set**:
   - `fatal_markers : list (list nat)` now contains
     `fatal_marker_exclamation_fatal` ("! Fatal"),
     `fatal_marker_emergency_stop` ("! Emergency stop"), and
     `fatal_marker_runaway_argument` ("Runaway argument").
   - `log_no_fatal log := forall m, In m fatal_markers ->
     contains_subseq m log = false` (universal quantifier form).
   - `empty_log_no_fatal` and `singleton_log_no_fatal` re-proved.
     Capstone proofs unchanged: they go through these lemmas, not
     specific markers.

3. **Engine-generic capstone aliases**:
   - `xelatex_compile_safe := pdflatex_compile_safe`.
   - `lualatex_compile_safe := pdflatex_compile_safe`.
   - The pass-iteration model is engine-agnostic; explicit aliases
     document that the carrier-level result extends to xelatex /
     lualatex profiles whose engines `BuildProfileSound.profile_admits`
     accepts.

### Honest deferral framing (corrected from v27.0.0)

Genuinely multi-week items that NEED stage-decomposed plan files
(see `specs/v27/`):

- **`T5_safe` substantive wiring** — `T5_wrapper` is Section-parametric
  in concrete `rule_id` / `rule_passes` / `no_static_violation`;
  bridging requires linking to the per-rule QED chain in
  `proofs/generated/`. Plan: `specs/v27/V27_T5_WIRING_PLAN.md`.
- **Faithful operational pdflatex semantics** — the abstract
  `pdflatex_step` is a counter; faithful would model real aux/log
  evolution per token. Plan: `specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md`.
- **Rolling fix-producer cadence** — 32 of 660 catalogued rules
  have producers; remaining 628 split by complexity bucket. Plan:
  `specs/v27/V27_FIX_PRODUCER_CADENCE.md`.
- **L3 AST migration** — `docs/L3_ROADMAP.md` is the existing
  multi-stage plan; revised in `specs/v27/V27_L3_AST_PLAN.md`.
- **`apply_edits_concrete_associative_subset` Coq theorem** — needs
  parallel-application Fixpoint over original-source offsets. Plan:
  `specs/v27/V27_APPLY_EDITS_ASSOC_PLAN.md`.

### Differential test
0 diffs across 330 corpus files vs `v27.0.0`. v27.0.1 is purely
formal/Coq — no runtime change.

### Counts (v27.0.1 vs v27.0.0)
- 660 catalogued rules (unchanged).
- 32 fix-producing rules (unchanged).
- 1,317 theorems (was 1,312; +5 from `_holds` lemmas + extended
  `log_no_fatal` + xelatex/lualatex aliases).
- 169 .v files (unchanged).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

## [v27.0.0] — 2026-04-28

**v27 WS8 capstone — `pdflatex_compile_safe` shipped with Qed.**

The compile-guarantee stack (`proofs/CompileProgress.v` T6 +
`proofs/CompileWellFormed.v` T7) is now discharged unconditionally
for the pdflatex profile. Both load-bearing hypotheses
(`compile_progress_rule`, `output_wellformed_rule`) close as
substantive Qed-proved lemmas in `proofs/PdflatexModel.v` against
an explicit pass-iteration model. `Print Assumptions
pdflatex_compile_safe` returns "Closed under the global context"
— zero axioms, zero admits.

**1,312 theorems / 169 .v files / 0 admits / 0 axioms** (v26.5.0
had 1,298 / 162; +14 from PdflatexModel.v Stages 2–6).

### Shipped (6 cycle PRs + this release-bump)

| PR | Stage | Content |
|---|---|---|
| #285 | Stage 1 | `proofs/PdflatexModel.v` scaffold: carriers, Section closures, `True` placeholder predicates |
| #288 | Stage 2 | `pdflatex_pass_state` Fixpoint + `iterate_step` + termination theorem `pdflatex_pass_count_bounded` (5-pass bound) |
| #289 | Stage 3 | First substantive `compile_progress_rule` discharge (refined further in Stage 6) |
| #290 | Stage 4 | `pdf_artefact` / `log_artefact` records + `valid_pdf_graph` + `pdf_log_wellformed` |
| #303 | Stage 5 | Substantive `output_wellformed_rule` discharge with `_v5`-suffixed predicates |
| #310 | Stage 6 capstone | Unify `_v5` chain into canonical names, strengthen `compilation_succeeds` to require `log_no_fatal`, ship unconditional `pdflatex_compile_safe` Qed |

### Headline theorem

```coq
Theorem pdflatex_compile_safe :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    project_well_typed p ->
    profile_supported pf ->
    exists out,
      pdflatex_produces p pf out /\
      pdflatex_compilation_succeeds p pf /\
      pdflatex_output_format_well_formed out.
```
Witness: `canonical_artefact (iterate_step pdflatex_initial_state
pdflatex_pass_max)`. The proof composes `pdflatex_T6_discharged`
(via `pdflatex_bounded_terminates_universal`) with
`pdflatex_T7_discharged` plus `iterate_step_log_unchanged` +
`empty_log_no_fatal` to close every conjunct.

### Predicate map (delivered)

- T2_closed  := `ProjectClosure.project_closed`
- T3_compatible := `BuildProfileSound.profile_admits ...`
- T0/T1/T4/T5 := `True` (deferred to v27 WS9+ — bridging to the
  LP-Core wrappers requires accessor functions on `build_graph` for
  per-domain carriers; multi-day per wrapper)
- bounded_terminates := `exists k <= 5, converged at k`
- compilation_succeeds := `exists k <= 5, converged at k /\
  log_no_fatal at k`
- produces := `exists k <= 5, out = canonical_artefact (iterate_step
  initial k)`
- output_format_well_formed := `pdf_log_wellformed (fst out) (snd
  out)` (= `valid_pdf_graph (fst) /\ log_no_fatal (snd)`)

See `proofs/ADMISSIBILITY_MAP.md` T6 + T7 entries for the full
discharge chain and `specs/v27/V27_WS8_PLAN.md` §2 for the
plan-vs-delivered diff.

### Faithfulness scope (v27 WS9+)

The capstone is unconditional under the counter-bounded
pass-iteration abstraction in `PdflatexModel.v`. Tying that
abstraction to a faithful operational pdflatex semantics (real
aux/log evolution, real fatal-marker emission, full set of fatal
markers beyond `! Fatal`, T0/T1/T4/T5 wiring through their
wrappers) is queued for the v27 WS9+ workstream.

### Differential test
0 diffs across 330 corpus files vs `v26.5.0`. WS8 is purely
formal/Coq — no runtime change. Same fix-producing rule set as
v26.5.0.

### Counts (v27.0.0 vs v26.5.0)
- 660 catalogued rules (unchanged).
- 32 fix-producing rules (unchanged).
- 1,312 theorems (was 1,298; +14 from WS8 stages 2–6).
- 169 .v files (was 162; +7 from PdflatexModel.v + companion files).
- 13 pre-release gates (unchanged).
- 9 required-checks on `main` (unchanged).

### Deferred to v27 WS9+
- T0/T1/T4/T5 wiring through their LP-Core wrappers (multi-day
  per wrapper — accessor functions on `build_graph` required).
- Faithful operational pdflatex semantics (real aux/log evolution).
- Extended fatal-marker detection set (currently only `! Fatal`).
- xelatex / lualatex profile discharge (still hypothesis-parametric).

## [v26.5.0] — 2026-04-27

v26.5.0 opens **v27 WS8** — the multi-session discharge of the
last two `HYPOTHESIS-PARAMETRIC` entries in
`proofs/ADMISSIBILITY_MAP.md` (T6 `compile_progress_rule` and T7
`output_wellformed_rule`) — and ships the §7 boundary-tracked
fix-producer batch. Plan in `specs/v27/V27_WS8_PLAN.md`.
**1,298 theorems / 162 .v files / 0 admits / 0 axioms** (v26.4.0
had 1,291 / 161; +7 from `PdflatexModel.v` Stage 1).

### Shipped (2 cycle items)

- **v27 WS8 Stage 1 — scaffold + plan** (`V27_WS8_PLAN.md` §1
  Stage 1).
  - `specs/v27/V27_WS8_PLAN.md` — full 6-stage roadmap with
    cross-session memory-handoff protocol.
  - `proofs/PdflatexModel.v` — concrete carriers
    (`pdflatex_project := build_graph`,
    `pdflatex_profile := { engine; features }`,
    `pdflatex_artefact := list nat` — Stage 4 refines), T2 + T3
    tied to existing concrete predicates (`project_closed`,
    `profile_admits`); T0/T1/T4/T5 use `True` placeholders that
    Stage 2 refines. Section-closure theorems
    (`pdflatex_T6_modulo_compile_progress_rule`,
    `pdflatex_T7_modulo_output_wellformed_rule`,
    `pdflatex_T6_stage1`, `pdflatex_T7_stage1`,
    `pdflatex_compile_safe_stage1`) — 7 added.
  - `proofs/ADMISSIBILITY_MAP.md` — T6 + T7 entries annotated
    "Stage 1 in flight".
  - `_CoqProject` — registers PdflatexModel.v.

  **Honest framing:** Stage 1's `True`-predicate discharge is
  degenerate by design — Section-closure is what matters here.
  Stages 2–5 refine each placeholder to substantive content;
  Stage 3 + 5 supply the actual rule discharges; Stage 6 ships
  the unconditional `pdflatex_compile_safe` Qed at v27.0.0.

- **§7 fix-producer batch** (4 rules, boundary-tracked):
  - `TYPO-016` space before `\cite/\ref` → `~` (NBSP).
  - `TYPO-026` en-dash between digits in page range → `--`
    (LaTeX double-hyphen).
  - `SPC-008` indented paragraph-start → strip leading
    whitespace (`\item` lines exempt).
  - `SPC-011` trailing whitespace before `\n` inside `$$…$$`
    displays → strip the run.

  5 new test cases in `latex-parse/src/test_typo_fix.ml`
  (4 positive + 1 SPC-008 negative for `\item` exemption). Total:
  **37 cases** (was 32). Total fix-producing rules now: **32**
  (3 v26.2.1 + 10 v26.3.0 + 10 v26.3.1 + 5 v26.4 + 4 v26.5).

### Differential test
0 diffs across 330 corpus files vs `v26.4.0`. The new fix
producers are gated behind the `--apply-fixes` family of flags;
default (no flag) output is byte-identical. WS8 Stage 1 is purely
formal/Coq — no runtime change.

### Counts
- 660 catalogued rules (unchanged).
- 32 fix-producing rules (was 28).
- 17 pre-release gates (unchanged).
- 36 GitHub Actions workflows (unchanged).
- 9 required-checks on `main` (unchanged).

### v27 WS8 multi-session protocol
Per `specs/v27/V27_WS8_PLAN.md` §3 + memory file
`~/.claude/.../memory/v27_ws8_status.md`, Stages 2–6 each open
with reading the plan + memory, do their bounded session's
worth of Coq work, end by updating memory + ADMISSIBILITY_MAP
annotations + (when content closes) tagging an alpha. The
capstone — unconditional `pdflatex_compile_safe` Qed — tags as
v27.0.0.

### Deferred to v26.6 / v27 (unchanged from v26.4.0 deferral list)
- Rolling fix producers for the remaining ~628 rules.
- L3 AST migration (multi-month).
- `apply_edits_concrete_associative_subset` Coq theorem
  (parallel-application Fixpoint, multi-week).

## [v26.4.0] — 2026-04-27

v26.4.0 ships conflict-aware rewrite merging (the headline feature
deferred from `V26_2_PLAN.md` line 631), the §1.2 stronger
`apply_edits` Coq theorems, and 5 more rolling fix producers. Plan
in `specs/v26/V26_4_PLAN.md`. **1,291 theorems / 161 .v files / 0
admits / 0 axioms** (v26.3.1 had 1,281 / 161; +10 lemmas across the
RewritePreservesCST extensions).

### Shipped (3 items + spec polish)

- **Conflict-aware rewrite merging** (`V26_4_PLAN.md` §1.1). Two new
  primitives in `Cst_edit`:
  - `apply_best_effort : string -> t list -> string * t list * t list`
    walks the edit list in order, accepts each edit if it doesn't
    conflict with an already-applied one, otherwise lands it in
    `skipped`. Output is byte-equal to `apply_all` over the
    `applied` subset (cannot fail by construction). Pure insertions
    at the same offset stay compatible per existing `conflicts`
    semantics — they all land in `applied` in input order.
  - `apply_with_priority : string -> (t -> int) -> t list -> ...`
    stable-sorts by descending priority then dispatches to
    `apply_best_effort`. Higher-priority edits dominate conflicting
    lower-priority ones; equal priority falls back to input order.

  CLI:
  - `--apply-fixes-best-effort` runs the best-effort path; reports
    skipped edits to stderr; exits 0 even when some edits were
    skipped (the partial-fix output is the contract).
  - `--apply-fixes-best-effort-for RULE-ID` is the same, restricted
    to one rule id.
  - The strict `--apply-fixes` mode is preserved for back-compat;
    its overlap-error message now hints at the new flag.

  7 new test cases in `latex-parse/src/test_cst_edit.ml` (no-conflict,
  first-wins, same-offset insertions, priority dominates, equal-priority
  input-order tiebreak, agrees with `apply_all` on disjoint input,
  third-edit-conflict).

- **Stronger `apply_edits` Coq theorems** (`V26_4_PLAN.md` §1.2,
  optional stretch). 10 new theorems in
  `proofs/RewritePreservesCST.v`:
  - `length_take_le`, `length_drop` — bounded-index length lemmas.
  - `edit_added`, `edit_removed` — nat aliases for byte-change
    measures.
  - `apply_one_edit_length` — the headline byte-count theorem:
    `length (apply_one_edit src e) = length src + edit_added e -
    edit_removed e` under `edit_wf` + bounded `e_end`.
  - 3 specialisation corollaries (balanced, pure insertion, pure
    deletion).
  - `apply_edits_concrete_singleton`, `apply_edits_concrete_cons` —
    fold-style decomposition.
  - `take_drop`, `take_drop_length` — standard prefix/suffix laws.

  **Honest non-discharge:** the associative-reorder claim
  (`apply_edits_concrete_associative_subset` mentioned in the plan)
  does NOT hold for the SEQUENTIAL `apply_edits_concrete` (each
  edit applies on the EVOLVING source, so offsets shift even for
  non-overlapping edits). Modelling the OCaml runtime's
  parallel-application surface in Coq is multi-week scope; deferred
  to v26.5+.

- **5 mechanical fix producers** (`V26_4_PLAN.md` §1.3, partial):
  - `TYPO-014` space before percent → strip the space.
  - `TYPO-021` capital after ellipsis (ASCII or Unicode) without
    space → insert a single space.
  - `TYPO-025` space before en-dash in number range → delete the
    space-run.
  - `SPC-009` ASCII `~` or UTF-8 NBSP at line start → strip.
  - `SPC-010` two spaces after sentence-ending period → collapse to
    one space.

  7 new test cases in `latex-parse/src/test_typo_fix.ml`
  (one per rule plus extra cases for TYPO-021's Unicode form and
  SPC-009's UTF-8 NBSP form). Total: **28 fix-producing rules**
  (was 23 at v26.3.1).

  The plan's §1.3 budget was 10; honest revision in PR #283 trimmed
  to 5 — the remaining 5 candidates either need careful boundary-
  tracking (TYPO-016, SPC-008, SPC-011) or duplicate existing fixes
  (STRUCT-003 ≈ TYPO-006). They roll into v26.5.

- **Spec polish** (PR #283): `V26_4_PLAN.md` §1.3 + §3 + §6 honest
  post-execution revision so the plan reflects what actually
  shipped (5/10 fix producers, 3 PRs not 2, differential test
  verified).

### CI hygiene shipped during the cycle

- **Format job timeout** bumped 15→30 min after upstream package
  mirror flakes (gitlab.inria.fr serving corrupted menhir/fix
  archives intermittently); Coq packages restored after a brief
  attempt to drop them broke `dune fmt` itself (it parses every
  dune file in the project, including `proofs/dune`'s
  `(coq.theory ...)` stanza).

### Differential test
0 diffs across 330 corpus files vs `v26.3.1`. The new fix
producers are gated behind `--apply-fixes` / `--apply-fixes-for` /
`--apply-fixes-best-effort{,-for}`; default (no flag) output is
byte-identical.

### Counts
- 660 catalogued rules (unchanged).
- 28 fix-producing rules (was 23).
- 17 pre-release gates (unchanged from v26.3.1).
- 36 GitHub Actions workflows (unchanged).
- 9 required-checks on `main` (unchanged).

### Deferred to v26.5 / v27
Per `V26_4_PLAN.md` §2 + §5 + memory:
- Rolling fix producers for the remaining ~632 rules (incl. the
  v26.4 §1.3 leftover 5 candidates).
- L3 AST migration (multi-month per `docs/L3_ROADMAP.md`).
- `apply_edits_concrete_associative_subset` Coq theorem (requires
  parallel-application Fixpoint, multi-week).
- v27 WS8 — T6/T7 discharge against `proofs/PdflatexModel.v` (the
  only `HYPOTHESIS-PARAMETRIC` entries left in
  `proofs/ADMISSIBILITY_MAP.md` after this release).

## [v26.3.1] — 2026-04-26

v26.3.1 discharges the two `V26_3_PLAN.md` §1.3 deferred items that
turned out tractable in-session, ships 10 more rolling fix
producers, and absorbs the substantial CI-hygiene cleanup sequence
from PRs #273–#278. Plan in `specs/v26/V26_3_1_PLAN.md`.
**1,281 theorems / 161 .v files / 0 admits / 0 axioms** (v26.3.0
had 1,261 / 159; +20 lemmas across the two concrete-discharge files).

### Shipped (3 items)

- **CSTRoundTrip.Section_lossless DISCHARGED**
  (`proofs/CSTRoundtripConcrete.v`, ~250 LoC). Two layers of concrete
  carriers: `Trivial_subset` (sanity, singleton-builder) and
  `Linewise_subset` (non-degenerate, splits at every line-feed
  boundary; `parse := split_at_lf`; `in_subset := no_nul_byte`).
  Both Section hypotheses (`builder_partitions`,
  `parse_serialize_is_id_on_subset`) close unconditionally; the
  Section's two in-section theorems re-export as
  `cst_byte_lossless_concrete` and `cst_structure_lossless_concrete`.
- **RewritePreservesSemantics.Semantic_preservation DISCHARGED**
  (`proofs/RewritePreservesSemanticsConcrete.v`, ~140 LoC).
  Concrete byte-filter tokenizer
  (`token := nat`, `tokens := filter (negb ∘ is_ws_byte)`).
  Both Section hypotheses (`tokens_ws_empty`, `tokens_concat`) close
  unconditionally; three in-section theorems re-export as
  `ws_replacement_preserves_tokens_concrete`,
  `ws_deletion_preserves_tokens_concrete`,
  `ws_insertion_preserves_tokens_concrete`. Limitation documented
  in `proofs/ADMISSIBILITY_MAP.md`: byte-level filter does not
  model `Parser_l2`'s lookahead semantics; stronger discharge is
  v27 WS7 work.
- **10 mechanical fix producers** (rolling work, `V26_3_1_PLAN.md`
  §1.1):
  - `TYPO-006` tab character → 4-space replacement
  - `TYPO-007` trailing whitespace → strip per line
  - `TYPO-008` 3+ blank lines → collapse to 2
  - `TYPO-009` `~` at line start → delete
  - `TYPO-013` single ASCII back-tick → curly U+2018
  - `TYPO-015` `\%\%` → `\%`
  - `SPC-002` whitespace-only line → empty line
  - `SPC-003` mixed tab+space indent → all-space (preserve depth)
  - `SPC-004` bare CR (not in CRLF) → LF
  - `SPC-005` trailing tab → strip trailing tab run

  11 new test cases in `latex-parse/src/test_typo_fix.ml`
  (one per rule plus a "leave double `` ` ` `` alone" case for
  TYPO-013). Total fix-producing rules now: **23**
  (3 v26.2.1 + 10 v26.3.0 + 10 v26.3.1).

### CI hygiene (PRs #273–#278, between v26.3.0 and v26.3.1)

- **Spec-drift workflow** wasn't running on `main` for ~3 days
  (PR #273 fixed the YAML colon-in-name parse error).
- **Required-checks** on `main` extended with `spec-drift`
  (PR #276; source-of-truth: `.github/required-status-checks.json`).
  Branch-protection gate set to 9 contexts.
- **Messages-validate** flipped from `|| true` to strict
  `FAIL_ON_MISMATCH=1` (PR #276).
- **Catalogue ↔ runtime contract** future-proofed via new
  `runtime_message` field on `rules_v3.yaml` (PR #275). Generator
  `scripts/tools/sync_runtime_messages.py` is idempotent.
- **9 silent-failure scope bugs** in pre-release gates closed:
  `validate_messages.sh`, `validate_catalogue.py`,
  `check_severity_drift.py`, `check_proof_substance.py`,
  `check_unused_hypotheses.py`, `check_code_quality.py`
  (3 sub-gates), `check_result_helpers.py`,
  `check_mli_doc_coverage.py`, `check_doc_refs.py`
  (PRs #277, #278). Each fixed gate now reports an input-count in
  its PASS message or refuses to silent-pass on empty input.

### Differential test
0 diffs across 330 corpus files vs `v26.3.0`. The new fix producers
are gated behind `--apply-fixes` / `--apply-fixes-for`; default
(no flag) output is byte-identical.

### Counts
- 660 catalogued rules (unchanged).
- 23 fix-producing rules (was 13).
- 17 pre-release gates (unchanged from v26.3.0).
- 36 GitHub Actions workflows (unchanged).

### Deferred to v26.4 / v27
Per `V26_3_1_PLAN.md` §2 + memory:
- Rolling fix producers for the remaining ~637 rules.
- L3 AST migration (multi-month).
- Conflict-aware rewrite merging (currently strict-rejects overlap).
- v26.3.0 item D extension (apply_edits stronger semantics).
- v27 WS8 — T6/T7 discharge against `proofs/PdflatexModel.v`
  (the only `HYPOTHESIS-PARAMETRIC` entries left in
  `proofs/ADMISSIBILITY_MAP.md` after this release).

## [v26.3.0] — 2026-04-25

v26.3.0 discharges the v26.2.1 §8 deferred-list (in-cycle subset) plus
two additional items from the v26.2 horizon. Plan in
`specs/v26/V26_3_PLAN.md`. **1,261 theorems / 159 .v files / 0 admits
/ 0 axioms** (v26.2.1 had 1,257; +4 from item D's concrete
`apply_edits` discharge).

### Shipped (8 items, A–H)

- **A. BOM-aware STRUCT-001 insertion** — leading UTF-8 BOM
  (`EF BB BF`) detected; `\documentclass{article}\n` inserted at
  byte 3 (after BOM) so the BOM stays at file start.
- **B. `--apply-fixes-for RULE-ID` CLI flag** — restricts the
  apply-fixes pass to results matching one rule id. `collect_fix_edits`
  gains `?filter_id`. New CLI tests confirm filter inclusion /
  exclusion.
- **C. CST structure-lossless runtime gate (gate #17)** — new test
  `test_cst_structure_lossless.ml` runs a curated subset of corpora
  (15 roundtrip + 6 v26_2_1 fixtures, excluding unclosed / >1MB) and
  asserts `parse(serialize(parse(src))) = parse(src)`. New script
  `check_cst_structure_lossless.py` wired into `pre_release_check`.
- **D. `RewritePreservesCST.apply_total` Section discharge** —
  concrete `apply_edits_concrete` (byte-splicing model in Coq) plus
  trivial `apply_total_concrete`. Two unconditional theorems
  (`rewrite_preserves_byte_lossless_concrete`,
  `rewrite_empty_preserves_concrete`) close the Section. +4 theorems.
  `ADMISSIBILITY_MAP.md` flag flipped DISCHARGED.
- **E. 10 rolling fix producers** — closes plan §3 item E in full
  (initial 5 + a deferred-batch 5 closed in the same cycle):
  TYPO-018 collapses runs of 2+ spaces; TYPO-022 strips space
  before closing brace; TYPO-024 deletes trailing dash + whitespace
  at line ends (CRLF-aware via regex `[ \t\r]*$`); TYPO-027
  collapses `!!`+ runs to a single `!`; TYPO-033 rewrites `et.al`
  to `et al.`; TYPO-035 inserts NBSP (U+00A0 = 0xC2 0xA0 UTF-8)
  before French punctuation `; : ! ?`; TYPO-037 strips space
  before comma; STRUCT-002 inserts `Untitled` placeholder inside
  empty `\section{...}` braces; ENC-002 and SPC-012 each delete
  every interior 3-byte BOM (`EF BB BF`) occurrence while preserving
  any leading BOM. Two new helpers (`find_consecutive_runs`,
  `mk_replace_edits`) factor the common scan-and-edit pattern.
- **F + G. xelatex / lualatex `.aux` parser support** —
  `aux_state.ml`'s `recognized_ignored` list extended with
  engine-specific macros. Note: per `V26_2_PLAN.md` §2.2 the
  verification requirement was "3 real `.aux` files produced by
  running [the engines] on documents from `corpora/`". v26.3.0
  ships hand-synthesised representative fixtures (matching the
  format documented in each engine's manual) — replacement with
  genuine engine-generated samples is v26.4 scope, pending a CI
  runner provisioned with all three engines. Engine-specific tokens
  recognised: `\xetexversion`, `\luatexversion`,
  `\luatexkv*`, `\pgfsyspdfmark`, etc.). New `corpora/aux/` directory
  with 3 minimal hand-synthesised fixtures + README. New test
  `test_aux_state_engines.ml` confirms zero parse warnings on each
  engine's fixture.
- **H. `edf_scheduler` per-class tier queues** — `drain` rewritten
  from single-sort with `class_priority_offset` trick to explicit
  per-class buckets, drained A → B → C → D, each tier internally
  ordered by raw priority. The §11.2 invariant is now structural
  rather than emergent. `class_priority_offset` /
  `effective_priority` retained for backwards compatibility (tests
  still query them).

### Multi-cycle scope (deferred to v26.3.1 / v26.4)

Per `V26_3_PLAN.md` §1.3, items genuinely requiring multi-week effort
land in successor cycles:

- `CSTRoundTrip.Section_lossless` full discharge (2 hypotheses;
  needs concrete `cst_abs` partition model + parse/serialize). Per
  `V26_2_PLAN.md` §10, the full discharge specifically must cover
  `\verb`, catcode mutations, and `\lstlisting` constructs — the
  three LaTeX features whose byte-lossless reasoning is non-trivial.
  v26.3.0 ships only the hypothesis-parametric Section + the
  runtime structure-lossless gate (item C) on a curated subset.
- `RewritePreservesSemantics.Semantic_preservation` full discharge
  (2 hypotheses; needs minimal Coq tokenizer model on trivia chunks).
- Rolling fix producers for the remaining ~647 rules.
- L3 AST migration per `docs/L3_ROADMAP.md`.
- Automatic conflict-aware rewrite merging (`V26_2_PLAN.md` §10
  deferral). v26.3.0 ships strict overlap rejection in `--apply-fixes`
  (`E.apply-fixes.overlap` + exit 2); a future cycle adds smart
  merging where compatible edits can be combined instead.

### Gates

**17 pre-release gates** (was 16 at v26.2.1, +1 for
`check_cst_structure_lossless`).

Test suites green on HEAD: `[typo-fix] PASS 14`,
`[fix-integration] PASS 6`, `[apply-fixes-cli] PASS 14`,
`[cst-structure-lossless] PASS 18 fixtures`,
`[aux-engines] PASS 3`, `[edf-scheduler] PASS 21`,
`[validators-struct] PASS 12` (includes STRUCT-002 fix assertion),
`[enc-char-spc]` includes ENC-002 + SPC-012 fix assertions,
`[cli] PASS 22`. All pre-existing suites unchanged.

`run_differential_test.py --baseline-ref v26.2.1 --current-ref HEAD
--corpus corpora/lint --expected-diff-keys ""` → **0 diffs / 330
files**. v26.3.0 is additive at the validator-output level.

### Semver

Additive. New fix producers attach `Some edits` to firings that
previously had `None`; default-mode TSV output is unchanged. The
new CLI flag and gate are net-new. No existing API removed.

## [v26.2.1] — 2026-04-25

v26.2.1 closes the fix-producer track deferred from v26.2.0. Every
item in the v26.2.0 `Deferred to v26.2.1 / v26.3` fix-producer
sub-list has shipped; the remaining deferrals are now exclusively
v26.3 scope (see `specs/v26/V26_2_1_PLAN.md` §8).

The cycle landed as five sequentially-stacked feature PRs plus a
release-bump PR:

- **PR #265** — `result.fix` field + `mk_result` helpers (PR #1).
- **PR #266** — STRUCT-001 fix producer (PR #2).
- **PR #267** — TYPO-002 / TYPO-003 fix producers (PR #3).
- **PR #268** — `--apply-fixes` CLI + `L0_APPLY_FIXES` env (PR #4).
- **PR #269** — E2E `test_rule_fix_integration` + CHANGELOG +
  consumer migration doc (PR #5).
- **PR #270** — release-bump + final spec polish (test split,
  BOM fixture, governance + opam + docs version refresh, drift
  cleanup of v26.2.0-era stale 1,252/157 doc figures).

### Shipped (v26.2.1 plan)

- **`Validators_common.result.fix : Cst_edit.t list option`** — new
  field + `mk_result` / `mk_result_with_fix` constructors. All 673
  existing record literals across 15 validator / test files were
  migrated through the helpers via a one-shot OCaml-aware script
  (`scripts/tools/migrate_result_literals.py`, deleted in PR #270
  per plan §3 PR #1; the parser was inlined into
  `check_result_helpers.py` so the gate stays self-contained).
  New gate `scripts/tools/check_result_helpers.py` (pre-release #15)
  forbids raw 4-field `{ id; severity; message; count }` literals
  in validator sources.
- **Type deviation from v26.2.0 CHANGELOG:** the field is
  `Cst_edit.t list option`, **not** `Cst_edit.t option`. TYPO-002/003
  aggregate `count` per document and need one edit per match; a list
  is required. Empty `Some` rejected by the helper.
- **STRUCT-001 fix producer** — emits a single
  `Cst_edit.insert ~at:0 "\documentclass{article}\n"` on missing
  `\documentclass`.
- **TYPO-002 / TYPO-003 fix producers** — one
  `Cst_edit.replace (off..off+2) "–"` (resp. `…+3 "—"`) per
  non-overlapping match offset found by the new
  `find_all_non_overlapping` helper. Rule `count` retains its
  overlap-count semantics via `count_substring` for back-compat; fix
  list is strictly non-overlapping. On pathological input like
  `----`, fix-count may be smaller than rule-count (documented).
- **`--apply-fixes` CLI flag + `L0_APPLY_FIXES` env gate** — runs
  validators, flattens `r.fix`, applies via `Rewrite_engine.apply`
  (which wraps `Cst_edit.apply_all`), emits modified source to
  stdout. Overlapping fixes → stderr `E.apply-fixes.overlap` +
  exit 2. Decision (per `V26_2_PLAN.md` §3.2 B3): all-or-nothing
  only; `--apply-fixes-for RULE-ID` stays v26.3 scope.
- **`test_rule_fix_integration.ml`** (new) — E2E pipeline test for
  STRUCT-001 / TYPO-002 / TYPO-003: fire → collect fixes → apply
  via `Rewrite_engine.apply_and_reparse` → assert rule no longer
  fires. 6 cases. Inputs live in `corpora/fixtures/v26_2_1/`
  (6 curated files + README, including a UTF-8 BOM fixture per
  plan §6 R3) and are loaded via `(deps (source_tree ...))` in
  `latex-parse/src/dune`.
- **`scripts/tools/check_fix_integration_wired.py`** (new, gate #16)
  — verifies the E2E test, its dune stanza, and the fixture files
  are all in place so CI can't accidentally detach the pipeline.
- **`docs/v26_2/FIX_STYLE_GUIDE.md`** refreshed to the v26.2.1 API
  (list + helper exemplars).
- **`docs/MIGRATION_v26.2_to_v26.2.1.md`** (new) — consumer-side
  migration notes: helper usage, the deviation from the CHANGELOG
  type, and the new `--apply-fixes` CLI mode.

### Gate count

- **16 pre-release gates** (was 14 at v26.2.0, +1 for PR #1's
  `check_result_helpers`, +1 for PR #5's
  `check_fix_integration_wired`).
- Test suites: `[typo-fix] PASS 6`, `[fix-integration] PASS 6`,
  `[apply-fixes-cli] PASS 10`, `[validators-struct] PASS 11`,
  `[cli] PASS 22`. All pre-existing test files continue green.
- `run_differential_test.py --baseline-ref v26.2.0 --current-ref HEAD
  --corpus corpora/lint --expected-diff-keys ""` → 0 diffs over
  330 files; v26.2.1 is byte-additive at the validator-output
  level (the only new payload is `r.fix`, not exposed in the TSV).

### Deferred to v26.3 (explicit)

- Rolling fix producers for the remaining ~657 rules.
- `--apply-fixes-for RULE-ID` granularity flag.
- CST structure-lossless runtime gate (corpus-scoped).
- `edf_scheduler.ml` per-class scheduling full rewrite.
- Three Section-level Coq discharges: `CSTRoundTrip.Structure_lossless`
  (2 hypotheses), `RewritePreservesCST.Rewrite_preserves` (1), and
  `RewritePreservesSemantics.Semantic_preservation` (2). See
  `proofs/ADMISSIBILITY_MAP.md` discharge-unit notes.
- xelatex / lualatex `.aux` parser variants.
- L3 AST migration (`docs/L3_ROADMAP.md`).

### Semver

Additive. `fix` defaults to `None`. Downstream consumers that
constructed `Validators_common.result` record literals directly must
migrate to `mk_result` / `mk_result_with_fix` (see
`docs/MIGRATION_v26.2_to_v26.2.1.md`). The new CLI flag +
env var are net-new; existing invocations are unaffected.

## [v26.2.0] — 2026-04-23

v26.2 closes the memo §16.3 compile-guarantee stack and CST/rewrite
foundation. The cycle ran as two pre-releases (`v26.2.0-alpha1` on
2026-04-22 shipped the compile-guarantee stack; `v26.2.0-alpha2` the
same day shipped the CST round-trip and rewrite engine) before this
final tag.

### Shipped

**Compile-guarantee contract (memo §5, §16.3):**

- `Project_model` / `Build_graph` / `Aux_state` / `Compile_contract` —
  typed project representation, fourth artefact-dependency graph,
  brace-balanced `.aux` parser, and `check_ready_to_compile` that runs
  T2 (project closure), T3 (engine/feature compatibility), T4
  (duplicate-label coherence from `.aux`) at runtime. T0/T1/T5 are
  delegated to the existing Parser_l2 / UserExpand / Validators.run_all
  pipeline.
- `specs/v26/compilation_guarantee_stack.md` + `compilation_profiles.yaml`
  formalize the T0–T7 theorem stack and engine metadata.
- Proofs: `ProjectClosure.v` (T2), `BuildProfileSound.v` (T3; decidable
  + pointwise↔bulk ↔ every-engine-has-compatible-feature),
  `CompileProgress.v` (T6, hypothesis-parametric per ADR-004),
  `CompileWellFormed.v` (T7, hypothesis-parametric), plus thin
  wrappers `T0_wrapper.v`, `T1_wrapper.v`, `T4_wrapper.v`,
  `T5_wrapper.v`. `proofs/ADMISSIBILITY_MAP.md` documents v27 WS8
  discharge targets.

**Byte-lossless CST + rewrite engine (memo §16.3):**

- `Parser_l2.loc` gains `end_offset : int` so CST spans are computable
  without rescanning. The only breaking-ish change; every `loc` record
  literal needs the new field.
- `Stable_spans` — `{start_offset; end_offset}` spans with
  `shift_after` / `damaged_by` edit-model.
- `Cst` + `Cst_of_ast` — byte-lossless CST variants (CToken / CTrivia /
  CGroup / CEnvironment / CMathInline / CMathDisplay / CVerbatim /
  CUnparsed); `of_source` post-process builder (ADR-008). **345/345
  corpora files round-trip** (verified at runtime by
  `test_cst_roundtrip.ml`).
- `Cst_edit` — edit algebra with half-open byte ranges, conflict
  detection (insertions at same offset don't conflict; strict-overlap
  rejected), `apply_all` batch application, `shift_after` for rebase.
- `Rewrite_engine` — thin wrapper over `Cst_edit.apply_all` +
  `Cst_of_ast.of_source`. `apply` + `apply_and_reparse`.
- Proofs: `CSTRoundTrip.v` (abstract byte-lossless partition model,
  plus hypothesis-parametric structure-lossless section for v26.3
  discharge), `RewritePreservesCST.v`, `RewritePreservesSemantics.v`
  (whitespace-for-whitespace replacement preserves tokens).
- `docs/CST_ROUNDTRIP_SCOPE.md` defines the two-level scope.

**Documentation:**

- `docs/MIGRATION_v26.1_to_v26.2.md`, `docs/ARCHITECTURE_DIAGRAM.md`,
  `docs/PROOF_RELATIONSHIPS.md`, `docs/PARSER_L2_AUDIT.md`,
  `docs/COMPILATION_GUARANTEE.md`.
- `docs/v26_2/` — plan + 5 sub-docs (USER_PERSONAS, ROLLBACK_DRILL,
  COMMUNICATION_PLAN, FIX_STYLE_GUIDE, CORPUS_LICENSING) + 8 ADRs.

**Infrastructure:**

- `scripts/tools/run_differential_test.py` — plan §3.3 HARD BLOCK gate
  that diffs v26.1.0 baseline output against HEAD on
  `corpora/regression/`. v26.2 expects zero non-fix diffs since
  validators weren't modified; v26.3+ uses `--expected-diff-keys fix`
  once rule-fix producers ship.
- `corpora/roundtrip/` — 15 synthetic edge cases (empty,
  whitespace-only, deeply-nested, unclosed math/group/env, verbatim
  with special characters, unicode, many-args, trailing whitespace,
  CRLF lines).

### Deferred to v26.2.1 / v26.3

- `validators_common.result.fix : Cst_edit.t option` — ~40 record-
  literal refactor, split into a dedicated PR to keep review size
  manageable.
- `--apply-fixes` CLI flag + per-rule fix producers for STRUCT-001,
  TYPO-002, TYPO-003.
- E2E `test_rule_fix_integration.ml` (validator → fixes → rewrite →
  parse-verify).
- CST structure-lossless runtime gate (corpus-scoped).
- Full per-class scheduling in `edf_scheduler.ml` beyond the priority
  offsets shipped in v26.1.

### Proof deltas since v26.1.0

- `+12` new theorems in the compile-guarantee stack (T0-T7 + wrappers)
- `+3` in CST round-trip (CSTRoundTrip.v)
- `+6` in rewrite preservation (RewritePreservesCST.v + RewritePreservesSemantics.v)
- Zero admits, zero axioms across the v26.2 additions.

Exact final counts: 157 .v files, 1,252 theorems/lemmas. See
`governance/project_facts.yaml` and `docs/PROOF_RELATIONSHIPS.md`.

## [v26.1.0] — 2026-04-21

### Post-merge audit rounds (PRs #241, #242, and #243)

Six audit passes after the initial P1 merge unearthed progressively deeper issues that earlier rounds missed. Each was closed with substantive changes and a CI gate to prevent regression.

- **Conflict resolution wiring** (PR #241 p1.3). `conflicts_with` is now consumed by `run_all`: severity DESC, count ASC, id_lex ASC picks the winner; TYPO-003 suppresses TYPO-002 on `---`. Five concrete conflict edges populated.
- **BuildLog LAY-025/026/027 tautologies** (PR #241 p1.4). Replaced `P -> P` with `build_ctx`-parameterised firing predicates and persistence theorems using `has_event_preserved`. 12 QED, zero `Proof. auto. Qed.`.
- **Five uncatalogued utility rules** (PR #241 p1.4). `no_tabs` / `unmatched_braces` / `require_documentclass` / `missing_section_title` / `DOC-STRUCT` renamed to `STRUCT-001..005`, added to `rules_v3.yaml` + contracts. `default_meta` has zero live callsites.
- **Family-level DAG edges** (PR #241 p1.4). LAB/REF/BIB/CITE/CMD/ENV/MATH/FIG/TAB/VERB/STYLE/STRUCT families get default consumes/provides. Empty-consumes 93% → 56%.
- **Three more load-bearing proof tautologies** (PR #242 p1.5). `PartialParseLocality.v` / `RepairMonotonicity.v::repair_restores_trust_outside_boundaries` / `ValidatorGraphProofs.v::cycle_detection_sound` + `dependency_respects_topo_order` — all rewritten with substantive bodies (`lia`, `andb_false_iff`, two-step transitivity).
- **Anti-tautology CI gate** (PR #242 p1.5). `proof.yml` rejects `Proof. auto. Qed.` / `Proof. trivial. Qed.` in the ten memo-load-bearing proof files. Escape hatch via `(* ANTI-TAUT-OK: reason *)`.
- **Memo §11.2 per-class scheduling** (PR #243 p1.6). `evidence_scoring.ml` caps Class D confidence at Low and Class C at Medium without a live build profile. `edf_scheduler.ml` gains a `execution_class` field with priority offsets (A=0, B=1e6, C=2e6, D=3e6) so hot-path rules dominate scheduling regardless of layer/chunk proximity. Tests in `test_edf_scheduler.ml` verify class dominance.
- **Runtime-type bindings for E2 + DAG proofs** (PR #243 p1.6). `RepairMonotonicity.v` adds `partial_cst_trust_zone` Coq record mirror of `Partial_cst.trust_zone` with `forget_confidence` projection; `partial_cst_zone_trusted_under_bounded_repair` transports the E2 theorem to runtime-shaped records. `ValidatorGraphProofs.v` adds `validator_meta_v26` with string IDs (via list nat) + `find_by_id_unique`.
- **Three regression gates** (PR #243 p1.6). `check_regression_gates.py` enforces (1) `_CoqProject` lists every non-archive `.v`, (2) every rule_id matches `FAMILY-NNN`, (3) mutation-uncovered count ≤ 35 (P1.4 baseline). Wired into `spec-drift.yml`.

## [v26.1.0-draft] — 2026-04-20

Memo-mandated v26 substrate delivery (`specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md`). Closes memo §4, §6, §10, §11, §12, §15 items that slipped past v26.0.0. After two internal audit rounds the scope was split into three honest buckets below.

### Shipped and runtime-enforced

These changes are real behaviour changes in the runtime or proof tree; tests pin the behaviour.

- **Language contract + tier gating** (memo §4). `specs/v26/language_contract.{md,yaml}` defines LP-Core / LP-Extended / LP-Foreign tiers. `latex-parse/src/language_profile.{ml,mli}` + `unsupported_feature.{ml,mli}` implement the classifier. CLI `--profile` flag; REST `L0_PROFILE_OVERRIDE` env var. **PR #241 (p1.2)** wires tier gating into `Validators.run_all`: when the active profile is `LP_Foreign`, rules whose contract declares `project_scope: lp_core_or_extended` are skipped; only `Any_tier` rules (the Class C build-coupled set) fire. Proven with `test_tier_gating.ml` (4 cases). `proofs/LanguageContract.v` — 6 QED.

- **Rule contracts drive the validator metadata** (memo §10, §15.4). `specs/rules/rule_contracts.yaml` + `.json` (654 entries × 11 fields) + `latex-parse/src/rule_contract_loader.{ml,mli}` replace `Validator_dag.default_meta` in `validators.ml` for every catalogued rule. Missing contracts are a fatal startup error (`Rule_contracts_missing` exception). Internal-utility rules (`no_tabs`, `unmatched_braces`, `DOC-STRUCT`) still use `default_meta`; `Validator_dag.default_meta` is `[@@deprecated]`. `scripts/tools/generate_rule_contracts.py` + `check_rule_contracts.py` drift gate enforces contract ↔ runtime parity. `proofs/ValidatorGraphProofs.v` +4 QED (7 total).

- **Execution-class runtime classification** (memo §11). `execution_class.classify` now reads the real A/B/C/D from `rule_contracts.yaml` instead of returning A-or-C. Class D (STYLE family) is routed out of `run_all` and reached through `run_with_policy Execution_policy.with_advisory` or the CLI `--advisory` flag. CI drift gate verifies every runtime Class C id in `execution_class.ml` has `execution_class: C` in the contract — this turns the abstract `ExecutionClasses.v` theorems into a runtime-enforced invariant. `proofs/ExecutionClasses.v` — 6 QED.

- **Editing-semantics proofs** (memo §6). `proofs/RepairMonotonicity.v` E2 strengthened with `repair_restores_trust_outside_boundaries` — the dependency-boundary hypothesis is genuinely consumed, not decorative (5 QED). `proofs/StableNodeIds.v` E3 binds to real AST via `parser_located_node` mirror + `Node_id.of_located` OCaml constructor, now called from `Partial_cst.zone_id` so every trust zone carries a stable ID across edits (8 QED). `latex-parse/src/error_recovery.is_repaired_with_deps` + `dependency_boundary` type.

- **Expanded compile-log pack** (memo §16.2). PR #235 added LAY-025/026/027 (rerun, citation undefined, font substitution) as Class C rules; `proofs/BuildLog.v` proves their conditional soundness (6 QED after the 3 new ones).

- **Spec catch-up**. `specs/rules/rules_v3.yaml`: added LAY-025/026/027 (PR #237) plus CMD-015/016/017 (user macro), PRJ-001..004 (project graph), PRT-001/002 (partial document trust) that existed in the runtime since v26.0 but never made it into the spec (PR #241 p1.1-#4). Totals: **654 specified / 638 shipped**. `scripts/validate_catalogue.py` L0-only early return removed.

- **UserMacro proof wrappers with real content** (memo §16.1). `proofs/UserMacroTermination.v` — `empty_catalog_acyclic`, `singleton_acyclic`, `add_entry_acyclic`, `count_refs_monotone` (4 non-trivial QEDs); `proofs/UserMacroRegistrySound.v` — `user_macro_registry_merge_sound` via `merge_acyclic`, disjoint-names specialisation, acyclicity-under-reverse-merge (3 QEDs). The tautological `input = input` placeholders from the first P1.1 draft were replaced after the second audit.

- **Machine-readable support matrix at memo path** (memo §12). `docs/SUPPORT_MATRIX.md` + `docs/SUPPORT_MATRIX.yaml` (moved to the memo §12.1 path, from `specs/v26/support_matrix.yaml`). YAML is source-of-truth; spec-drift workflow validates schema.

- **Governance regeneration**. `governance/project_facts.yaml` — version v26.1.0, 654/638 counts, `by_proof_class` includes `formal_conditional: 3`, `by_execution_class` populated (A=172, B=416, C=17, D=49). `generated/project_facts.json` mirror emitted by generator (memo §16.1 asked for JSON). `governance/project_facts.contract.yaml` updated.

### Shipped as metadata; enforcement partial or deferred

These are real artefacts but the runtime does not yet fully consume them; callers still need to reach them explicitly.

- **Per-class scheduling** (memo §11.2). `rule_contracts.yaml` tags every rule with A/B/C/D, and `execution_class.classify` returns the real class. But `evidence_scoring.ml` and `edf_scheduler.ml` do NOT yet weight results or priority by class — Class D confidence is not capped, Class C does not get a dedicated EDF budget. The taxonomy is enforced at registration/classification time; per-class scheduling is v26.2 work and pairs with the compile-guarantee stack.

- **Rule DAG edges** (memo §10.3). 44 of 654 contracts have non-empty `consumes` (Class C: compile-log; L3 file rules: image/pdf/font metadata; ML-gated: ml_confidence_map). `depends_on` and `conflicts_with` are empty for every rule today. `Validator_dag.build_dag` produces a correct but largely edgeless DAG — this is the honest state for pattern-match leaf rules. VPD-overlap-derived conflict edges are a v26.2 follow-up.

- **Node_id constructor**. `Node_id.of_located` is wired from `Partial_cst.zone_id` and the type is consumed by a new public `val zone_id` — giving the E3 theorem a concrete binding. Validators and incremental callers do NOT yet track zones by node_id across edits; that consumer arrives with the v26.2 lossless-CST substrate.

- **ExecutionClasses.v abstract model**. The theorem compartments (`Hot_path_state`, `Build_log_state`, `External_binary_state`, `Ml_confidence_state`) are a Coq-level abstraction. The runtime binding comes from the CI drift gate (step 3b in `check_rule_contracts.py`) verifying every runtime Class C rule has `execution_class: C` in the contract. A deeper binding — mapping Coq compartments to the real `Log_parser` / `File_context` / `Evidence_scoring` modules — is v26.2 work.

### Deferred to v26.2 / v27 (memo §16.3 release plan, not v26.1 regressions)

- Lossless CST stack (memo §7): `cst.ml`, `cst_builder.ml`, `rewrite_engine.ml`, `stable_spans.ml`, `CSTRoundTrip.v`, `RewritePreservesCST.v`. v26.2.
- Compile-guarantee theorem stack T0–T7 (memo §5) and `specs/v26/compilation_profiles.yaml`. v26.2 / v27.2.
- Three-plane hybrid invalidation with full semantic dep edges (memo §9). Current `dependency_graph.ml` / `invalidation.ml` / `semantic_edges.ml` ship as the v26 foundation; three-plane routing is v26.2.
- Full project/build model: `aux_state.ml`, `bibliography_state.ml`, `artifact_graph.ml`, `ProjectSemantics.v`, `ArtifactGraphSound.v` (memo §8). v26.2.
- Editorial policy layer (memo §13). v27.0.
- Collaboration platform (memo §14). v27.1.

### Documentation refresh

- `README.md`, `docs/index.md`, `docs/PROOF_CLASSES.md`, `docs/SUPPORT_MATRIX.md`, `docs/ARCH.md`, `docs/PROOFS.md`, `docs/PROOF_GUIDE.md`, `ARCHITECTURE.md`, `ml/ARCHITECTURE.md`, `ml/RESULTS.md`, `specs/README.md`, `specs/rules/README.md`, `docs/README.md`: v26.1.0 framing; refreshed counts (654 / 638 / 631 / 20 / 3 / 1,137); ML v2 no longer marked "blocked" (trained on A100, F1=0.9799, proved).
- `docs/L3_ROADMAP.md`: new. Honest acknowledgement of regex-derived L3 (memo §15.5) with migration plan to AST-derived extraction.
- `docs/ARCH.md` L3 section now leads with the regex-caveat.
- `docs/archive/`: moved obsolete v25-era docs (`PROJECT_STORY_GENERAL.md`, `RULES_IMPLEMENTATION_PLAN.md`, `WEEKLY_STATUS.md`).

### Fixed (memo §15)

- §15.2 governance drift: `governance/project_facts.yaml` regenerated and drift-gated end-to-end.
- §15.3 release-state coherence: CHANGELOG entry structure split across shipped / metadata / deferred.
- §15.4 DAG metadata hollowness: `default_meta` fallback removed for catalogued rules.
- §15.5 L3 over-source honesty: `docs/L3_ROADMAP.md` + `docs/ARCH.md` caveat.
- §15.1 EDF deadline bug: verified already fixed in v26.0 (field is `priority`, comment explicit).

### Verification

- `dune build` green (full tree including proofs)
- `dune runtest --force latex-parse/src` → 94+ suites PASS, 0 failures
- `proof-ci` zero admits, zero axioms across 144 Coq files
- `scripts/tools/check_repo_facts.py` → Project facts check passed
- `scripts/tools/check_rule_contracts.py` → PASS with Class C runtime-vs-contract binding check
- `scripts/validate_catalogue.py` → PASS (all layers)

## [v26.0.0] — 2026-04-18

### Added (PRs #223-#233)

**WS0: Truth-surface freeze**
- Canonical `governance/project_facts.yaml` with `generate_project_facts.py` and `check_repo_facts.py`
- Spec-drift CI gate (`.github/workflows/spec-drift.yml`)
- `docs/SUPPORT_MATRIX.md`, `docs/PROOF_CLASSES.md`, `docs/COMPILATION_GUARANTEE_STACK.md`

**WS1: Compile-log integration**
- Class C execution path: 14 log-dependent rules isolated from keystroke-critical `run_all`
- `build_profile.ml`: auto-detect `.log` sibling, engine detection, staleness check
- `execution_class.ml` / `execution_policy.ml`: A/B/C/D taxonomy
- CLI `--log` flag, auto-detect, `[build]` tagged output
- `docs/BUILD_LOG_CONTRACT.md`

**WS2: Bounded user macro registry**
- `user_macro_registry.ml`: parse `\newcommand`/`\renewcommand`/`\providecommand`, 29-primitive blocklist
- Def-use dependency edges, DFS cycle detection
- `merge_user_macros` in `macro_catalogue.ml`: user macros expand via existing pipeline
- CMD-015 (unsupported construct), CMD-016 (cycle), CMD-017 (shadowing)

**WS3: Project graph foundation**
- `include_resolver.ml`: parse `\input`/`\include`/`\includeonly`, no-brace form support
- `project_graph.ml`: directed inclusion graph, DFS cycle detection, `\includeonly` respect
- `project_state.ml`: per-file semantic analysis, cross-file label/ref projection
- PRJ-001 (cycle), PRJ-002 (unresolved), PRJ-003 (cross-file undef ref), PRJ-004 (dup label)
- CLI `--project` mode

**WS4: Hybrid invalidation**
- `semantic_edges.ml`: label-ref and macro def-use edges per chunk
- `dependency_graph.ml`: BFS transitive affected set propagation
- `invalidation.ml`: replaces whole-source fallback with semantic-aware invalidation
- Wired into `run_all_incremental` and `run_all_scheduled`

**WS5: Partial document semantics**
- `partial_cst.ml`: classify documents into trust zones (Complete/Partial/Broken)
- `error_recovery.ml`: recovery point detection, monotonic repair predicate
- PRT-001 (parse errors with confidence-based severity), PRT-002 (trust zone boundary)
- Wired into `run_all` via `Parser_l2.parse_located`

**WS6: Testing hardening**
- `test_mutation_baseline.ml`: 92.4% rule coverage (532/576)
- `test_fuzz_parser.ml`: grammar-aware parser fuzzing (5000 trials)
- `test_fuzz_binary.ml`: PNG/JPEG/font reader fuzzing (1000 trials/format)
- `test_long_stress.ml`: 10K iterations + GC tracking
- `.github/workflows/mutation.yml`, `.github/workflows/fuzz-nightly.yml`

**Coq proofs (6 new files, 22 QED, 0 admits)**
- `BuildLog.v`, `UserExpand.v`, `IncludeGraphSound.v`
- `InvalidationSound.v`, `PartialParseLocality.v`, `DamageContainment.v`

### Fixed
- EDF scheduler: renamed `deadline` to `priority` (was compared against wall-clock time)
- Removed dead `DeadlineMissed` event from event_bus
- TIKZ-002 moved from `rules_l3_file` to `rules_class_c` (Class C isolation)
- `expand_once` arity-0 argsafe fix (user macros with no args never expanded)
- REST handler: `User_macro_context` set/cleared per request

### Changed
- `project_facts.yaml`: `multi_file: planned` → `multi_file: alpha`
- 18 new OCaml modules, 15 new test files, ~3,846 new lines

## [v25.0.0] — 2026-04-14

### Added (PRs #200-#219)
- 19 L3 file-based validators: PNG/JPEG/PDF/font binary readers (PRs #214-#215)
- 12 expl3/draft rules: CHAR-004, MATH-006, L3-001..011 (PR #215)
- 19 MOD/EXP rules added to spec with VPD entries (PR #215)
- SIMD 6x benchmark: simd_vs_scalar_bench.ml, 12.67x measured (PR #214)
- ML v2 ByteClassifier trained on A100: F1=0.9799 (PR #215)
- SpanExtractorSound.v: v2_span_extractor_sound theorem QED (PR #215)
- Chunk store: paragraph-level splitting, xxh64 hashing, per-chunk caching (PR #216)
- EDF scheduler: deadline-ordered task execution, event bus integration (PR #216)
- ML confidence integration: pre-computed map suppresses zero-TP rules (PR #216)
- run_all_incremental: only re-validates dirty chunks (PR #216)
- run_all_scheduled: EDF-ordered incremental validation (PR #216)
- Proof maturity: multi_substring_all, substring_pair, terminated_command,
  paragraph_terminated_command_pair Coq families (PRs #218-#219)
- Integration test suite: 36 paranoid end-to-end assertions (PR #219)
- docs/ARCH.md: architecture handbook (PR #217)
- docs/PROOF_GUIDE.md: proof-writers guide (PR #217)
- .pre-commit-config.yaml: zero-admits, zero-axioms, no-Str, format hooks (PR #217)
- Re_compat module: thread-safe Str replacement via Re library (PR #217)
- Colab notebook: v2_byte_classifier_training.ipynb, disconnection-safe (PR #215)
- data/ml_confidence_map.json: per-rule ML precision weights (PR #216)
- Dockerfile: multi-stage OCaml service image
- scripts/release.sh: release automation
- .github/workflows/release.yml: GitHub Release + Cosign signing
- .github/workflows/docker-push.yml: Docker image to GHCR

### Changed (PRs #200-#219)
- Str→Re migration: 1,057 call sites across 16 files, zero Str references (PR #217)
- Proof count: 606 faithful (was 587), 20 conservative (was 37)
- Theorem count: 1,067 (was ~600)
- Severity mismatches: 10 fixed in VPD patterns (PR #219)
- validators_cli.ml: now uses run_all_scored with ML confidence (PR #217)
- ML confidence map: opt-in via LP_ML_CONFIDENCE_MAP env var (PR #217)
- Performance gates: aligned to spec (25ms full-doc, 1ms edit-window) (PR #217)
- v25_master_R1.md §9: 6→7 language packs (Arabic added) (PR #217)
- L_roadmap.md: W102-140 marked Done

### Fixed (PRs #200-#219)
- gen_coq_proofs.py: L3/L4 grouping bug (was defaulting to L0) (PR #214)
- build_candidate_dataset.py: yaml.safe_load→json.load for control chars (PR #215)
- train_byte_classifier.py: BCELoss outside autocast for AMP safety (PR #215)
- chunk_store: catcode vector in hash per spec I-3 (PR #216)
- chunk_store: diff_snapshots handles deletion (PR #216)
- edf_scheduler: removed dead Lockfree_queue field (PR #216)
- 25 weak test assertions eliminated across 5 files (PR #219)
- All font reader tests: match/expect-true→direct equality (PR #219)

## [Unreleased — Phases 9-12]

### Added (Phases 9-12, PRs #161-#179)
- Comprehensive project audit: docs, .mli, _CoqProject fixes (PR #172)
- Regex hoisting: 44 Str.regexp compilations moved out of run closures (PRs #172, #173)
- contains_substring: replaced Str.regexp_string with pure OCaml (PR #174)
- ML CPU baselines: logistic regression + gradient boosting pipeline (PR #175)
- External corpus infrastructure: corpora.lock + fetch_corpora.sh (PR #176)
- Risk register: governance/risk-register.md with 33 risks (PR #177)
- Parallel validators: run_all_parallel with OCaml 5.x domains (PR #178)
- Documentation site: mkdocs.yml + landing page (PR #179)

### Removed
- run_all_parallel: unsafe with Str global state, removed pending Re migration (PR #180)

### Added (PRs #161-#171)
- ML v2 parser-state diagnostic + architecture docs (PR #161)
- v2 candidate classification pipeline: extractor, dataset, byte classifier (PR #165)
- 429 soundness theorems via auto-generation + CI parallelism (PR #166)
- Language detection: babel/polyglossia/CJK heuristic, 65-lang mapping (PR #167)
- 84 new validators: 49 STYLE, 10 locale (CE/TH/IB/LANG), 25 L3-approx (PR #168)
- Post-merge audit fixes: regex bugs, severity mismatches, 55 test cases (PR #169)
- 93 golden corpus tests + 7 i18n QA documents across 12 YAML suites (PR #170)
- 607 soundness theorems (was 429), 26 test hardening cases, perf verified (PR #171)

### Changed (Phases 9-12)
- Rule count: 452 → 568 unique IDs (91.2% of 623 spec)
- Proof count: 429 → 607 per-rule soundness theorems (26 faithful, 581 conservative)
- Golden corpus: 236 → 329 cases across 12 suites
- Test suites: 53 → 57, ~7,320 test cases total
- gen_coq_proofs.py extended to L3/L4 layers

### Infrastructure (Phases 9-12)
- Project health cleanup: gitignore, CI consolidation, action bumps (PR #162)
- Docs/proofs audit: README sync, macro sync, Coq proof refactor (PR #163)
- Folder cleanup: archive stale docs, remove orphans (PR #164)

### Added (Phases 4-8, PRs #150-#159)
- Sub-split L0 and L1 validator modules (PR #150)
- Table-driven layer lookup (PR #151)
- CI workflow consolidation with setup-ocaml-env (PR #152)
- Test file consolidation by domain (PR #156)
- REST API decomposition into 3 modules (PR #157)
- Multi-arg macro support + 17 argsafe macros (PR #158)
- CI hardening: timeouts on all 30 workflows, Rust fmt+clippy (PR #159)

### Changed
- Macro catalogue expanded: 441 symbols + 79 argsafe = 520 total (was 383 + 28)
- CI consolidated from 35 to 30 workflows
- All CI jobs now have explicit timeout-minutes
- Rust proxy enforces cargo fmt --check + cargo clippy -D warnings
- Removed redundant opam constraint (dune >= 3.10 dedup)
- Deleted dead .github/actions/setup-ocaml/ composite action

### Fixed
- Dropbox-corrupted git refs (Phase 8: 21 conflict files in .git/)
- cargo fmt pre-existing formatting issue in rust proxy
- Stale remote branches cleaned (6 deleted)
- Stale local branches cleaned (16 deleted)
- Documentation audit: corrected inflated rule counts (482 → 452 spec-matched)


## [W25] - L3 Text-Scannable Approximations (PR #141)

### Added
- 22 new validators: BIB (12), PKG (2), FONT (1), LAY (3), REF (1), META (1), PDF (1), TIKZ (1)
- Helpers: `split_bib_entries`, `count_matches`
- 94 unit tests, 22 corpus files, 22 golden entries

## [W24] - expl3, TIKZ, LANG Rules (PR #140)

### Added
- 25 new validators: L3-expl3 (9), TIKZ (6), LANG (4), COL/LAY/META/RTL (6)
- 111 unit tests, 25 golden corpus files

## [W23] - L2 Batch 4: Final Text-Scannable (PR #139)

### Added
- 27 new validators: PKG (9), TAB (7), FIG (7), MATH (2), CMD (1), DOC (1)
- Helpers: `extract_usepackages_with_opts`, `extract_caption_content`
- 77 unit tests, 27 corpus files

## [W22] - Audit Remediation (PR #138)

### Fixed
- MATH-063 `String.split_on_char` bug
- CMD-005, PKG-007/023, TIKZ-007, FIG-010, DOC-001/002/003 logic fixes
- 43 regression tests

## [W21] - L2 Batch 3 (PR #137)

### Added
- 22 new validators: CMD, DOC, TAB, PKG, LANG, TIKZ, FIG rules
- 91 unit tests, 22 golden entries

## [W20] - L2 Batch 2 (PR #136)

### Added
- 11 new validators: FONT, MATH, REF cross-reference rules
- Helpers: `extract_labels_with_prefix`, `extract_refs_with_prefix`
- 85 unit tests

## [W19] - L2 Batch 1 (PR #135)

### Added
- 14 new validators: FIG, TAB, PKG, CJK structural scanning rules
- Helpers: `extract_env_blocks_with_opts`, `extract_preamble`, `extract_usepackages`
- 53 unit tests

## [W18] - Locale + Straggler Batch (PRs #133-134)

### Added
- 16 locale rules covering FR/PT/RU/PL/CS/EL/RO/AR/HE/ZH/JA/KO/HI
- 17 straggler rules (CY, DE, NL, PL, PT, RU, TR, ZH, VERB, MATH, L3, REF, TYPO)
- L0/L1 coverage: 100% of actionable rules (333/345; 12 Reserved)

## [W17] - L1 Batch Completion (PRs #120-132)

### Added
- DELIM (11), SCRIPT (22), MATH-A (14), MATH-B (23), MATH-C (34) L1 batches
- REF batch (8 rules), CHEM batch (9 rules), L3 batch (9 rules)
- ~1,300+ validator tests total
