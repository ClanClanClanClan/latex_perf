# Round-7 Deep Code Audit — Findings & Fix Program (execution doc)

> **Status:** authoritative execution plan for the round-7 fix program. Companion to
> `docs/v27/ROADMAP.md` (v3.1), which sequences these items; THIS doc carries the finding-level
> detail. Scope frozen at audit HEAD = the post-#501 merge of `main` (v27.1.61 + glue train).
>
> **Method (keep for future audits — it worked):** two workflow phases, 8 adversarial
> finder-agents per phase, each REQUIRED to run the real binary (`--compile-check`) against the
> real oracle (pdfTeX, TeX Live 2026, dual protocol: `-halt-on-error` exit AND nonstopmode exit +
> PDF presence; *strong fatal* = nonstop nonzero AND no PDF), `kpsewhich` before any package-based
> claim, one independent verifier per finding re-building every repro FROM SCRATCH and trying to
> refute it, a known-list to suppress rediscovery, and a completeness critic per phase.
> **Score: 77 findings confirmed, 1 refuted** (a code-read-only conclusion — the exception that
> proves the run-the-binary rule).

---

## 1. Headline results

- **30 confirmed false-READY classes** (CLI exit 0, pdflatex deterministically fatal) +
  **47 confirmed other** (over-rejection / divergence / perf / doc-drift / quantification).
- **The verified core HELD everywhere it was engaged**: 477/477 fast==full parity, zero
  divergence, all four #501 fixes survived adversarial re-probing, MODEL-READY's Qed is genuine
  (0 Admitted / 0 Axiom across the 17-file dependency chain).
- **The #501 hard-gate's measured over-reject cost at corpus scale ≈ ZERO**: 7/477 model-only
  rejections; 6 are fontspec docs that genuinely fail pdflatex; 1 is the (mis-titled) dup-label
  fixture. The synthetic over-reject classes are real but rare in the committed corpus.
- **Highest-volume false-READY found:** raw CJK/Han body codepoints with no font-setup package —
  strong-fatal on **6 of 147 READY corpus docs (4.1%)**. No package catalogue can catch it; it
  needs a body-*codepoint* feature.
- **Most impactful real-world over-reject:** every scanner reads bytes AFTER `\end{document}`
  that TeX never reads — **37/38 roots of a real article project are auto-rejected** for parked
  dead content.
- **Destructive-fix class confirmed:** `--apply-fixes` breaks 2 of the project's own 29 compiling
  corpus docs and can rewrite `--` inside an `\input{fig--x}` filename into a strong fatal that
  the post-state `--compile-check` cannot see.

## 2. The three belts (every defect lives in one)

1. **INPUT-MODEL DIVERGENCE** — scanners read raw bytes; pdflatex reads TeX's *processed, live*
   input stream. CR-only EOLs blind the comment scanner; `^^7b` caret notation evades every brace
   counter; `\endinput` / `\iffalse` hide the missing `\end{document}`; dead regions after
   `\end{document}` are scanned. Supplies 4 strong-fatal false-READYs AND the dominant real-world
   over-reject. **One verified pre-pass fixes the whole belt (rank 2).**
2. **CLOSED-WORLD ASSUMPTIONS** — the 5-needle feature catalogue (no load-closure, no
   case/expansion tolerance, no codepoints); the include vocabulary + filesystem semantics
   (a *directory* satisfies `Sys.file_exists`; cycle detection is dead code); the artefact surface
   (`.bbl` never read; corrupt `.aux` ignored). Ranks 1, 4, 5, 6.
3. **GLUE POLARITY** — warning-grade oracle behaviours hard-block READY (dup-label,
   `\include`-missing, bare unclosed group), the corpus itself encodes one polarity inversion,
   and the fixer rewrites load-bearing syntax. Ranks 3, 7, 8, 10.

## 3. Confirmed false-READY inventory (fix-rank cross-referenced)

| ID | Repro essence | Rank |
|---|---|---|
| A-comment-blind (×4 variants) | `\usepackage{amsmath,%⏎fontspec}` / `\usepackage%⏎{fontspec}` — comment inside/before argument evades the verified scanner | 1, 2 |
| A-bracket-naive | `\usepackage[Ligatures={x]y}]{fontspec}` — option scan cuts at first `]`, LaTeX brace-protects it | 1 |
| A-csname-loader | `\csname usepackage\endcsname{fontspec}` (lp-extended, exit 0) | 1 |
| B2-02 | `\lowercase{\usepackage{FONTSPEC}}` | 1 |
| A2/ltjarticle | any engine-fatal package outside the 5 needles; `\documentclass{ltjarticle}` class-loader gap | 1 |
| B6-1 | raw CJK body codepoints, no font setup — 4.1% of corpus READY verdicts | 1(c) |
| B2-01 | CR-only EOLs: one `%` blinds every comment-aware detector for the rest of the file | 2 |
| B4-F1 | `^^7b` (catcode-1 `{`) decoded by TeX, by no scanner — brace runaway invisible | 2 |
| A3 / B7-1 / B7-2 / B7-6 | missing `\end{document}`; `\endinput` before it; the only `\end{document}` inside `\iffalse`; duplicate `\begin{document}` | 2 |
| A5 | `\verb\|x` broken by end-of-line | 2 |
| B1-F1 | `\input{sections}` where `sections/` (or `sections.tex/`) is a DIRECTORY | 4 |
| B1-F2 | include **2-cycle** (a→b→a) is READY (single-level scan never sees b's include of a). **Correction (fixture-verification):** the *direct self-include* B1-F2 also claimed is NOT a false-READY — the binary rejects it via `project_closed_b`; only the nested 2-cycle is live | 4 |
| B3-1 | fatal `.bbl` sibling — pdflatex reads it at `\bibliography`, no component ever does | 5 |
| B3-2 | corrupt/truncated `.aux` (interrupted-run artifact) fatals the next pdflatex run; `Aux_state` Error→`[]` | 5 |
| B8-5 | unwritable artefact dir / poisoned TEXINPUTS / unresolvable `article.cls` | 5 |
| A4 / B8-2 / B8-1 | NUL byte; >200 KB single line (buf_size); >255 grouping levels (parser's own guard sits at 500 — the WRONG side); 100k-label main-memory blowout | 6 |
| A6 | `\hyperref[l]{link text}` — link text IS typeset; double-script inside it missed | 7(a) |
| A7 | text-mode fatal class (`a^b` in text, …) — protocol-dependent (halt-on-error) | 7(a), S2 fixtures |
| b5-F1..F3 | fixer-manufactured fatals (`--` in `\input` filename; TikZ `--` path op; `` \` `` accent corruption) | 3 |

*(Full repro .tex + observed outputs for every entry: session task outputs `wj90flgff` /
`weqcuwnwu`; the fixture-export item R7-INFRA-1 commits them all under
`corpora/compile_check/false_ready/`.)*

## 4. The fix program (10 ranks, dependency-aware)

**Ranks 1–5 eliminate every confirmed critical false-READY.** `needs_coq` = touches the verified
spec (re-prove + re-extract via `regen_body_token_frontend_extract.sh`); everything else is pure
OCaml. Every rank lands with its fixtures flipped from `expected: false_ready` to
`expected: not_ready` in the R7-INFRA-1 manifest.

| # | Root cause | Fix (operative content) | Coq? | Effort |
|---|---|---|---|---|
| 1 | **T3 = 5-needle byte catalogue**; no load-closure, no case/expansion tolerance, no codepoint universe | (a) tokenizer-grade package/class extractor (comment-aware, case-normalizing, `\lowercase`/`\csname`-tolerant) in the Coq spec + OCaml mirror, extending the #501 pattern; (b) GENERATE `ProvidesCatalogue` from the pinned TeX Live tree (latexdef-style probing ~1 s/pkg) with **loads-edges** (polyglossia→fontspec) and **conflict-edges** (natbib+biblatex), keyed {package\|class}×option-set, one-directional per G1; (c) **body-CODEPOINT feature**: raw CJK/Han/Hebrew ⇒ requires-font-setup unless a capable package is detected (over-detect = safe) | YES | M |
| 2 | **Byte scanners don't model TeX's input processor / live region** | ONE verified pre-pass before every verdict-path scanner: (a) EOL normalization (CR, CRLF, LF all end lines/comments); (b) `^^`-notation decoding; (c) **LIVE-PREFIX computation** — truncate at the first *reached* `\end{document}`, honour `\endinput` line semantics + conservative `\iffalse` skip model, require the terminating `\end{document}` to be LIVE. Kills 4 false-READY classes AND the 37/38-roots over-reject AND the dead-byte perf tax, in one train. Specified in Coq (it changes what the verified model reads) | YES | L |
| 2 — **status (2 PRs)** | **PR-R7-2 SHIPPED the offset-preserving, add-NOT-READY-only slice** (no Coq — the verified model is untouched): CR/CRLF-aware line comments (`fr_cr_comment`) + a `no_live_end_document_fatal` detector for *no `\end{document}` at all* (`fr_missing_end`). Adversarially verified (18-agent workflow + 386 real papers): **0 new false-READY, 0 real over-rejection**. The `\endinput`-first arm was prototyped and **DROPPED** — the differential showed it over-rejects the common `\ifdefined\previewmode\endinput\fi` (arXiv) and `\ifdraft\endinput\fi` toggles, which compile. **DEFERRED to PR-R7-2b (the live-region train):** `^^`-decode (`fr_caret_brace`, offset-changing), `\endinput`+`\iffalse`/`\newif` liveness (`fr_endinput_before_end`, `fr_end_in_iffalse`), and the **truncation/dead-region over-reject fix** (the one part that could *introduce* a false-READY if the live-region model is wrong — needs its own adversarial pass). | — | — |
| 3 | **Fixer rewrites load-bearing regions, no post-fix guard** | (a) extend `find_exempt_ranges` to macro-argument contexts (`\input`/`\include`/`\includegraphics`/`\bibliography`/`\label`/`\ref` filename+key args) + tikzpicture bodies; (b) TYPO-013-class checks preceding-backslash (control-symbol) context; (c) belt-and-braces: after ANY rewrite, re-run `--compile-check`; REFUSE or roll back hunk-wise any fix set that flips READY→NOT-READY or adds Error findings. **Only class that silently destroys user files** | no | M |
| 4 | **T2 include layer** (dirs count as files; cycle check dead; comment-blind scanner; no kpathsea; wrong resolution base; duplicate-include collapse; wrong `\include` polarity) | Runtime half (each S): `Sys.is_regular_file`; comment-stripped source into the include scanner (reuse rank-2 pre-pass); `kpsewhich` fallback; documented resolution base + `--workdir` + divergence warning; `\include`-missing/`\includeonly` demoted to warning polarity; case-sensitivity portability lint; hashtable node lookup. Model half (Coq — the deferred Bug-4 train): real tex→tex edges with `exists:bool`, node dedup by resolved path, a GENUINE cycle check replacing constant-true `is_acyclic`; re-prove `project_closed_b` | YES (model half) | L |
| 5 | **Artefact surface unmodeled** (.bbl, corrupt .aux, environment) | (a) `\bibliography` present + `\jobname.bbl` exists ⇒ run structural/T5 scanners over the `.bbl` bytes (it is just TeX); (b) `Aux_state` parse warnings ⇒ conservative NOT-READY ("stale .aux — delete and retry"), not Error→`[]`; (c) cheap preflight: `.aux`/`.log`/`.pdf` writable, CWD writable, `article.cls` resolvable; (d) implement `Missing_bib_entries` or delete the dead constructor + fix comments | no | M |
| 6 | **pdflatex capacity limits absent; ENC coverage inconsistent** | Reject-only gates (safe direction): (a) group depth incl. `\begingroup` >250 ⇒ NOT-READY; (b) coarse main-memory heuristic (token/label mass, calibrated from the measured blowup) with explicit capacity reason; (c) extend ENC compile-blocking to 0x00 and 0x7F; (d) single-line > buf_size ⇒ reject | no | M |
| 7 | **Fatal-polarity errors + hash-collision over-reject** | (a) OCaml quick wins: `comment`/`filecontents*`/`Verbatim*` added to `parser_l2` verbatim_envs; accept `\end {env}` spacing; model `\[..$$` closure; demote text-mode bare-unclosed-group to warning; (b) Coq train (= deferred Bug 5): move dup-label to the G2 warning channel / drop the `nodup` premise, AND replace 30-bit FNV label ids with full-key comparison in the same re-prove; rename `fail_duplicate_label.tex` (it asserts the wrong polarity) | YES (b) | M |
| 8 | **lp-extended admits non-terminating macro recursion** | conservative detector: `\def` whose body references its own name with NO conditional + a use-site ⇒ NOT-READY/demote. MUST pass a differential sweep vs the real-paper corpus first (the CMD-016 over-rejection post-mortem applies) | no | M |
| 9 | **Superlinear hot spots** (the wedge inverts at scale) | (a) Coq: sort-based nodup replacing `nodup_nat_b` list-membership (43 s → <1 s @ 100k labels), re-extract; (b) OCaml: interval-tree / sorted-array search for `find_ref_alias_macros` / `find_moving_arg_ranges` / `in_ranges_b`; hashtable in `graph_of_build_graph`; (c) rank-2's live-prefix removes the dead-byte tax. Ship WITH the perf sentinel (R7-INFRA-6) | YES (a) | M |
| 10 | **Docs/corpus assertions overstate or invert measured behaviour** | qualify the structural-gate IFF claim as halt-on-error-scoped; fix/delete dead-code comments (`Missing_bib_entries`, cycle reason); re-tier the contradicted `tolerated_*` fixtures; document lint-mode's exit-code non-contract + opt-in `--error-exit`; fold the A10 honesty items into `COMPILATION_GUARANTEE.md` | no | S |

## 5. Regression infrastructure (the audit's structural payoff — R7-INFRA)

Nothing today prevents a NEW false-READY from shipping; these eight items make that class of
regression mechanically impossible to miss. **R7-INFRA-1 and -2 land FIRST, before rank 1.**

1. **`known_false_ready` fixture corpus + monotone CI gate** — ✅ **LANDED (PR-R7-0).** 21
   confirmed false-READY repros committed under `corpora/false_ready/` (a NEW sibling of
   `compile_check/`, so the flat differential matrix and the recursive front-end parity sweep are
   untouched) with `manifest.json` (per-fixture pdflatex ground truth + `expected_cli`).
   `scripts/tools/check_known_false_ready.py` runs in the CI `build` job (CLI-only, no TeX) and
   fails on either drift direction — a fixed fixture regressing to READY, or a live one silently
   fixed without a manifest update. Each fix PR flips its entries to `expected_cli: NOT-READY` and
   lowers the baseline. Baseline: 13 strong-fatal + 8 error-halt, fix ranks 1/2/4/5/6/7.
2. **pdflatex differential CI gate (S-CI-TEX realized)** — texlive-pinned image,
   `REQUIRE_PDFLATEX=1`, BOTH oracle protocols, full corpus + false_ready fixtures on every
   release train. (Every round-7 finding was discovered by RUNNING pdflatex; CI has zero pdflatex
   today.) **PR-R7-0 ships the LOCAL form** — `scripts/tools/false_ready_oracle.sh` re-runs the
   real oracle and drift-checks the manifest; the CI texlive-image is the remaining follow-up.
3. **Oracle-truth corpus snapshot** — per-doc {verdict, reason class, HALT/NOSTOP/PDF triple,
   timing} committed as golden TSVs; verdict flips require an explicit fixture-update commit.
   Simultaneously fix the polarity-inverted fixtures.
4. **apply-fixes round-trip gate** — for every corpus doc, both fixer modes must be (a) idempotent,
   (b) oracle-class-preserving (compiling docs still compile), (c) verdict-non-degrading.
5. **SEC-EXTRACT + mirror-fuzz** — CI byte-compares committed `*_extracted.ml` vs fresh
   extraction; a property fuzzer asserts OCaml-mirror == Coq-extract evidence on hostile byte
   streams (CR, NUL, `^^`, multi-byte UTF-8, `%` edges).
6. **Size-banded perf sentinel** — fixed synthetic set (380 KB flat / 1.1 MB flat / 5k-include /
   100k-label / 9 MB dead-region), budgets expressed as multiples of measured pdflatex time on
   the same file; CI fails on breach.
7. **Encoding/EOL/input-processor fixture matrix** — {CR, CRLF, LF, UTF-16LE/BE, BOM, NUL, DEL,
   0xE9, invalid-UTF-8, `^^`-hex} × {clean doc, known-fatal doc}, each with expected verdict +
   oracle grade.
8. **Real-project acceptance corpus** — the maintainer's article folders run read-only through
   `--compile-check` per release; over-reject rate tracked (this is what surfaced the 37/38 case).

## 6. Remaining unprobed surfaces (concrete mechanism hypotheses only)

1. **Local `.sty`/`.cls` content closure** — a project-sibling `mystyle.sty` containing
   `\RequirePackage{fontspec}` is loaded but never read → READY. (Rank-1(b) loads-edges must
   include project-local files.)
2. **Include vocabulary beyond `\input`/`\include`** — `\import`, `\subimport`, `\subfile`,
   `\@input` are invisible to `include_resolver.ml`.
3. **UTF-16/UTF-32 whole-file encodings** — a UTF-16 file is ~50% NUL bytes; every needle is
   byte-split, so NO detector fires; rank-6(c)'s NUL rejection also closes this carrier.
4. **Mirror-vs-extract differential under hostile bytes** — R7-INFRA-5 is the systematic answer.
5. **`\documentclass` option-driven engine selection** — distro classes whose `.cls` transitively
   loads engine-fatal packages (the ltjarticle mechanism, generalized).

## 7. Sequencing (mirror of ROADMAP v3.1 §5)

**PR-R7-0** = R7-INFRA-1 + -2 (fixtures + monotone gate + pdflatex CI). → **PR-R7-1** = rank 2
(the verified input-model pre-pass — biggest single belt). → **PR-R7-2** = rank 1 (catalogue +
codepoints). → **PR-R7-3** = ranks 4+5 (include/artefact surface). → **PR-R7-4** = rank 3 (fixer
guard). → then ranks 6–10 + remaining infra in S/M-sized trains. Version ceremony: the first
fix train ships as **v27.1.62**.

---

*Provenance: audit run 2026-07-24 on post-#501 `main`; phase A (extraction faithfulness) =
session task `wj90flgff` (47 agents), phase B (full sweep) = task `weqcuwnwu` (51 agents);
oracle pdfTeX 3.141592653-2.6-1.40.29 / TeX Live 2026; memory topic `audit_round7_deep_code`.*
