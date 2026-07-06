# Candidate Fixes (Bucket C) — `--list-candidate-fixes`

LaTeX-Perfectionist splits fixable rules into two channels:

| Channel | Field on `result` | Applied by | Bucket |
|---|---|---|---|
| **Auto-fix** | `fix : Cst_edit.t list option` | `--apply-fixes` / `--apply-fixes-for` | A (mechanical, deterministic, always safe) |
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
- Candidates whose target lies inside a protected region (verbatim / comment /
  `\url` / and, for text rules, math) are **dropped** — a commented-out or
  verbatim trigger yields no candidate.

Example:

```
CANDIDATE	REF-006	Use \pageref (page number) instead of \ref
  EDIT	9	14	\pageref{
CANDIDATE	PKG-022	Replace obsolete package subfigure with subcaption
  EDIT	37	46	subcaption
```

## The candidate rules (18)

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

`MATH-012`/`MATH-025`/`MATH-032`/`MATH-052`/`MATH-064`/`MATH-101`/`MATH-102`,
`CHEM-001`, `ZH-001` and `SPC-018` gate on math; text rules use the full exempt
set. See `Validators_common.candidates_drop_exempt` / `candidates_drop_vcu_exempt`.

## Rationale

Auto-fixes (Bucket A) are proven byte-safe and applied silently. Candidates
(Bucket C) require judgment, so they are surfaced only. This keeps `--apply-fixes`
corruption-free while still offering the full breadth of assisted edits through a
review surface. See `specs/v27/V27_FIX_PRODUCER_CADENCE.md` for the bucket model.
