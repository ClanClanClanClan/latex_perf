# Candidate Fixes (Bucket C) — `--list-candidate-fixes`

LaTeX-Perfectionist splits fixable rules into two channels:

| Channel | Field on `result` | Applied by | Bucket |
|---|---|---|---|
| **Auto-fix** | `fix : Cst_edit.t list option` | `--apply-fixes` / `--apply-fixes-for` | A (mechanical, deterministic, guard-gated) |
| **Candidate** | `candidate_fixes : candidate_fix list` | never auto-applied — surfaced for author review | C (context/intent-dependent) |

A **candidate fix** is a *suggested* edit whose correctness depends on author
intent, so it must never be applied without review. Example: inserting a space in
`main.Py` (identifier) vs `end.Sentence` (missing space) is lexically identical —
only the author knows which is meant. Such rules therefore emit candidates, not
auto-fixes.

**Invariant:** `--apply-fixes` and `--apply-fixes-for` read **only** the `fix`
field. Candidate rules keep `produces_fix: false`, so they are absent from the
producer-coverage gate and never mutate a document mechanically. Running
`--apply-fixes-for <candidate-rule> file.tex` is guaranteed byte-identical to the
input.

## Output format

```bash
dune exec latex-parse/src/validators_cli.exe -- --list-candidate-fixes paper.tex
```

Emits, per firing that carries candidates, tab-separated machine-readable lines an
editor frontend can offer as quick-fixes:

```
CANDIDATE<TAB><rule-id><TAB><human-readable label>
  EDIT<TAB><start-byte><TAB><end-byte><TAB><replacement>
  EDIT<TAB>...
```

- `EDIT` offsets are **byte** ranges `[start, end)` into the source; applying them
  (non-overlapping) yields the suggested rewrite.
- A **label-only** candidate (no `EDIT` lines) names a transformation whose span
  cannot be safely bounded (e.g. an unbraced `\eqalign`); the editor shows the
  label but leaves the edit to the author.
- Candidates are screened **twice**, by two different filters, and it is worth
  knowing which does what:
  1. `candidates_drop_exempt` (producer side) drops a candidate whose target
     lies inside a *typography-exempt* region — verbatim, comment, `\url`, and
     for text rules math. A commented-out or verbatim trigger yields no
     candidate at all.
  2. `Fix_guard.filter_candidate` (CLI side, v27.1.63) screens the surviving
     **byte offers** against the LOAD-BEARING regions: control symbols, TikZ and
     pgf picture bodies, filename and package-spec arguments, cross-reference
     keys, and tabular preambles. These are not regions the author wrote
     verbatim — they are bytes TeX reads as syntax rather than prose, so the
     first filter never looked at them.

  The second screen keeps the **CANDIDATE line and drops only the EDIT lines**.
  A fully-screened candidate therefore degrades to label-only: you still learn
  that the rule fired and where, and are simply not handed a rewrite the guard
  cannot vouch for. Measured over 523 corpus documents: 6,514 candidates
  unchanged, 174 of 7,523 byte offers withheld (2.3%).

  ⚠ Rules whose *contract* is to rewrite one of those regions are exempt from
  that region only — the `REF-00x` label renamers from cross-reference keys, the
  `PKG-0xx` package replacers from package specs, `TAB-005` from tabular
  preambles. The exemption lists are separate from the auto-fix channel's and
  are never shared.

Example:

```
CANDIDATE	REF-006	Use \pageref (page number) instead of \ref
  EDIT	9	14	\pageref{
CANDIDATE	PKG-022	Replace obsolete package subfigure with subcaption
  EDIT	37	46	subcaption
```

## The candidate rules (a sample — **124** are shipped)

The table below is a hand-picked selection, not the full set. The authoritative
count and per-rule list are generated into `specs/v27/CANDIDATE_BACKLOG.md`;
this heading previously read "(20)", which was a fair description of the table
and a badly misleading one about the tool.

| Rule | Suggests |
|---|---|
| REF-006 | `\ref` → `\pageref` (author confirms it's a page reference) |
| PKG-022 | obsolete package → modern (epsfig→graphicx, subfigure→subcaption, natbib→biblatex) |
| CMD-002 | `\def\name` → `\renewcommand{\name}` |
| CMD-011 | wrap `\def`/`\edef` (with `@`) in `\makeatletter` … `\makeatother` |
| MATH-012 | multi-letter function → `\operatorname{…}` |
| MATH-025 | one-column `align` → `equation` |
| MATH-032 | `[ smallmatrix ]` → `bsmallmatrix` |
| MATH-052 / MATH-101 | `\over` → `\frac{…}{…}` |
| MATH-064 | `\eqalign{…}` → `\begin{align}…\end{align}` |
| MATH-102 | `eqnarray` → `align` |
| VERB-006 | inline `\verb` (multiline) → verbatim environment (label-only) |
| VERB-010 | back-tick inline code → `\verb\|…\|` |
| BIB-011 | legacy `note={URL:…}` → `url` field |
| CHEM-001 | wrap chemical formula in `\ce{…}` (mhchem) |
| ZH-001 | western `.` → Chinese `。` (zh context) |
| FR-008 | French `œ/Œ` ligature |
| SPC-018 | insert a space after a sentence-ending period |
| DE-006 | Swiss German `ß` → `ss` (lossy: correct only under Swiss orthography) |
| ENC-006 | overlong UTF-8 → minimal re-encoding (may decode to a control byte) |

`MATH-012`/`MATH-025`/`MATH-032`/`MATH-052`/`MATH-064`/`MATH-101`/`MATH-102`,
`CHEM-001`, `ZH-001` and `SPC-018` gate on math; text rules use the full exempt
set. See `Validators_common.candidates_drop_exempt` / `candidates_drop_vcu_exempt`.

## Rationale

Auto-fixes (Bucket A) are **guard-gated, not proven**, and applied silently.
Candidates (Bucket C) require judgment, so they are surfaced only.

The distinction matters, because "proven" was the word here and nothing in
`proofs/` justifies it: `grep -rlniE 'fix_guard|apply_fixes' proofs/` returns
nothing. The `Cst_edit` theorems are about the edit APPLIER under a non-overlap
hypothesis — they say nothing about whether the bytes a producer chose to rewrite
were safe to rewrite. What actually constrains the fixer is empirical and lives in
two places: `Fix_guard` withholds edits landing in load-bearing byte ranges
(control symbols, TikZ paths, filename and package arguments, cross-reference
keys, tabular preambles), and `corpora/apply_fixes/manifest.json` records the
residual damage measured against real pdflatex. That manifest currently records
zero `breaks_compile` and zero `manufactured_false_ready` rows — a measurement
over that corpus, not a guarantee over your document.

⚠ The candidate channel is NOT guard-gated. `--list-candidate-fixes` prints its
byte offers unfiltered, so an offer may land inside a protected region; review
before applying. See `specs/v27/V27_FIX_PRODUCER_CADENCE.md` for the bucket
model.
