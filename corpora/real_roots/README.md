# `corpora/real_roots` — the real-paper differential

The North-Star metric is *"proven-verdict coverage at zero false-READY on real
papers"*. Every number the project has ever quoted for it came from
`corpora/compile_check` — **66 hand-authored fixtures, 11,282 bytes total, mean
171 bytes**, flat single files. A differential over that corpus measures the
corpus's own design, not real LaTeX.

`scripts/tools/diff_real_roots.py` runs `--compile-check` and real pdflatex over
whole **arXiv source trees**: real preambles, real package sets, real `\input`
siblings, real `.bbl` files.

## The corpus is not in this repo

It is arXiv source — mixed licences, not redistributable, and ~12 GB. Point the
runner at it:

```
export LP_REAL_CORPUS=/path/to/corpus/papers
python3 scripts/tools/diff_real_roots.py --n 200 --record
```

Only `manifest.json` (per-paper hashes) and `results.json` (the matrix) are
committed, so a run is **reproducible by verification** even though the inputs
cannot be shipped: the runner recomputes `sha256_tree` for every selected paper
and exits 2 if any differs from the manifest.

## Frame and selection

- **Frame** — packages whose arXiv `00README.json` declares
  `process.compiler == "pdflatex"` and exactly one `usage == "toplevel"` `.tex`
  present on disk. Root detection uses that file, never a `\documentclass` scan:
  a substring scan counts commented-out declarations and is off by 66 files.
- **Selection** — sort by `sha256(arxiv_id)` ascending, take the first N.
  Deterministic, independent of filesystem order, and **stable under corpus
  growth**: extending 200 → 400 leaves the first 200 unchanged, so a later
  baseline stays comparable to an earlier one.

## Reading the result honestly

- Over-rejection is a rate over **graded** documents, never over N.
- `ungraded-infra` is a paper whose build needs `shell-escape` (arXiv ran
  `epstopdf`). Scoring those as FAILS would invent false-READYs out of
  infrastructure.
- **Any** timeout voids the whole run (exit 2). A timeout scores as FAILS
  against a READY verdict, which manufactures a false-READY out of thin air.
- arXiv built these under **TeX Live 2023** while the oracle is pinned to
  **TL2026**. A FAILS verdict can mean a genuine source defect *or* three years
  of package drift. ⚠ **This corpus cannot control for that drift**, and the
  instruction that used to sit here — "report the matrix restricted to
  `declared_texlive == 2026`" — asked for the empty set. Measured over all 2,821
  packages: `texlive_version` is present on 1,880 (66.6%) and **every declared
  value is 2023**; not one paper declares the oracle's TL2026. There is no
  same-engine stratum to compare against, so the drift confound is *universal*,
  not a subset to be split off.
  The only split this corpus supports is declared-2023 vs undeclared, and it
  shows **no signal**: false-READY runs **7/130 (5.4%)** among the papers
  declaring TL2023 and **4/69 (5.8%)** among those declaring nothing. Report
  both, and do not present either as a drift control — "undeclared" is unknown,
  very likely also older, not a TL2026 baseline.
- This is one snapshot of arXiv, pdflatex-only. It is the first honest reading
  of the metric; it is **not** a representative sample of research LaTeX.

## Exit codes

Identical in meaning to `diff_compile_check.sh`, deliberately:

| code | meaning |
|---|---|
| 0 | clean |
| 1 | a NEW false-READY — the cardinal bug |
| 2 | infrastructure: missing binary, sha mismatch, any timeout, >10% ungraded, or zero true-READY |
| 3 | engine skew (local pdflatex ≠ the pin) |
| 4 | over-rejection above the recorded baseline — the SAFE direction |

Never conflate 1 and 4. And never auto-populate an allowlist from a bulk run:
triage every false-READY by hand.

## First measured result (2026-08-21)

200 papers, frame 2,719, oracle `pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026)`.
Binary: `main` + the DELIM control-word boundary fix + fix-guard region 4.

| cell | n |
|---|---|
| true-READY | 107 |
| true-NOT-READY | 6 |
| **FALSE-READY** | **11** |
| false-NOT-READY | 75 |
| ungraded-infra | 1 |
| ungraded-timeout | 0 |

Correct verdicts **113/199 graded = 56.8%**. Over-rejection **75/199 = 37.7%**.

**Two classes account for all 11 false-READYs**, which is the useful half of the
result — the residual is large but not shapeless:

| n | class |
|---|---|
| 8 | `! LaTeX Error: Command \c@<env> already defined.` (lemma x3, proposition, definition, lem, assumption, `\theHalgorithm`) |
| 3 | `! Package natbib Error: Bibliography not compatible with author-year citations.` |

The first reproduces in seven lines, with no visible mistake in the document:

```latex
\documentclass{article}
\usepackage{thm-restate}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\begin{document}
\begin{lemma}A statement.\end{lemma}
\end{document}
```

pdflatex exits 1 with no PDF; `--compile-check` says READY. Remove
`thm-restate` and it compiles; `amsthm` alone compiles. Checked against TeX Live
drift first (arXiv built these under TL2023) — drift is **not** the cause.

Over-rejection drivers, by reason, over the 75 false-NOT-READY documents —
a document can carry several:

| reason | docs |
|---|---|
| T5 | 31 |
| T2 | 23 |
| T3 | 22 |
| T4 | 18 |
| T0 | 15 |
| PRT-001 | 13 |
| DELIM-007 | 11 |
| DELIM-001 | 8 |

⚠ **Do not read 56.8% as the North-Star metric.** The metric's own definition
requires ZERO false-READY, and this run has 11. The number is the first honest
*measurement*, not a score to celebrate.
