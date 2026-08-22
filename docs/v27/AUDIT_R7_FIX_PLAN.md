# Round-7 Deep Code Audit — Findings & Fix Program (execution doc)

> ⚠ **HISTORICAL EXECUTION RECORD.** Round 7 is complete as designed and
> superseded as strategy: it drove the false-READY *fixture* baseline from 21 to
> 7 while the published banner moved 35 → 34, because the fixture corpus and the
> differential corpus are disjoint. For current state and the live open ledger
> see **[PROJECT_STATE.md](PROJECT_STATE.md)**.

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
| 1 — **status (PR-R7-1a)** | **SHIPPED the polyglossia/mathspec catalogue additions** (loads-edges 1b, verified clean): `\usepackage{polyglossia}`/`{mathspec}` now require OpenType → `fr_polyglossia`. Re-extracted, capstone axiom-free, front-end parity holds. **⚠ COMMENT-BLANKING and BRACE-AWARE BRACKET were prototyped and REVERTED** — the 10-agent adversarial workflow found **4 new false-READYs**: blanking the *full* verbatim-range set erased live feature loads inside `alltt`/`listing` (which EXECUTE commands, not inert), and the brace-aware `drop_after_rbracket` was not escape-aware (`\{` in options evaded it). **DEFERRED to a dedicated feature-scanner-precision train:** comment-awareness must blank only truly-inert ranges (comments + `\verb` + url + true-verbatim, NOT `alltt`/`listing`/`tikzpicture`); the bracket scan needs escape-awareness; plus the CJK body-codepoint feature (1c) and `\lowercase`/`\csname` loaders. Fixtures deferred: `fr_comment_comma`, `fr_comment_beforearg`, `fr_bracket_naive`, `fr_lowercase_loader`, `fr_csname_loader`, `fr_raw_cjk`. | — | — |
| 1 — **status (PR-R7-1b)** | **SHIPPED the escape-aware brace-tracking option scan** — the one rank-1-precision sub-fix that survived adversarial verification. `drop_after_rbracket` (Coq + OCaml mirror) closes the `[..]` option group only at an UNESCAPED `]` at brace depth 0, so `\usepackage[Ligatures={x]y}]{fontspec}` and `\usepackage[a=\{]{fontspec}` are detected. Re-extracted, capstone axiom-free, parity 426, 0 over-reject on 400 real-paper samples. Flips `fr_bracket_naive`; baseline 13→12. **⚠ COMMENT-AWARENESS PROVED A MINEFIELD — dropped across TWO more adversarial rounds (6 false-READYs total):** blanking ANY scanner-identified region inherits that scanner's over-extension bugs as false-READYs — first the verbatim ENV set (`alltt`/`listing` execute; `\newenvironment{comment}` passthrough; undefined `comment`), then even `\verb`/`\lstinline` (the shared scanner mishandles `\lstinline[opt]` and doesn't stop `\verb` at EOL — the same bug as the pre-existing OR-1 over-reject). **Deferred (needs the shared `\verb`/`\lstinline`-optarg scanner FIXED first + a non-over-blanking design):** `fr_comment_comma`, `fr_comment_beforearg`; plus CJK codepoint (1c) + `\lowercase`/`\csname` (`fr_raw_cjk`, `fr_lowercase_loader`, `fr_csname_loader`). | — | — |
| 2 | **Byte scanners don't model TeX's input processor / live region** | ONE verified pre-pass before every verdict-path scanner: (a) EOL normalization (CR, CRLF, LF all end lines/comments); (b) `^^`-notation decoding; (c) **LIVE-PREFIX computation** — truncate at the first *reached* `\end{document}`, honour `\endinput` line semantics + conservative `\iffalse` skip model, require the terminating `\end{document}` to be LIVE. Kills 4 false-READY classes AND the 37/38-roots over-reject AND the dead-byte perf tax, in one train. Specified in Coq (it changes what the verified model reads) | YES | L |
| 2 — **status (2 PRs)** | **PR-R7-2 SHIPPED the offset-preserving, add-NOT-READY-only slice** (no Coq — the verified model is untouched): CR/CRLF-aware line comments (`fr_cr_comment`) + a `no_live_end_document_fatal` detector for *no `\end{document}` at all* (`fr_missing_end`). Adversarially verified (18-agent workflow + 386 real papers): **0 new false-READY, 0 real over-rejection**. The `\endinput`-first arm was prototyped and **DROPPED** — the differential showed it over-rejects the common `\ifdefined\previewmode\endinput\fi` (arXiv) and `\ifdraft\endinput\fi` toggles, which compile. **DEFERRED to PR-R7-2b (the live-region train):** `^^`-decode (`fr_caret_brace`, offset-changing), `\endinput`+`\iffalse`/`\newif` liveness (`fr_endinput_before_end`, `fr_end_in_iffalse`), and the **truncation/dead-region over-reject fix** (the one part that could *introduce* a false-READY if the live-region model is wrong — needs its own adversarial pass). | — | — |
| 3 | **Fixer rewrites load-bearing regions, no post-fix guard** | (a) extend `find_exempt_ranges` to macro-argument contexts (`\input`/`\include`/`\includegraphics`/`\bibliography`/`\label`/`\ref` filename+key args) + tikzpicture bodies; (b) TYPO-013-class checks preceding-backslash (control-symbol) context; (c) belt-and-braces: after ANY rewrite, re-run `--compile-check`; REFUSE or roll back hunk-wise any fix set that flips READY→NOT-READY or adds Error findings. **Only class that silently destroys user files** | no | M |
| 4 | **T2 include layer** (dirs count as files; cycle check dead; comment-blind scanner; no kpathsea; wrong resolution base; duplicate-include collapse; wrong `\include` polarity) | Runtime half (each S): `Sys.is_regular_file`; comment-stripped source into the include scanner (reuse rank-2 pre-pass); `kpsewhich` fallback; documented resolution base + `--workdir` + divergence warning; `\include`-missing/`\includeonly` demoted to warning polarity; case-sensitivity portability lint; hashtable node lookup. Model half (Coq — the deferred Bug-4 train): real tex→tex edges with `exists:bool`, node dedup by resolved path, a GENUINE cycle check replacing constant-true `is_acyclic`; re-prove `project_closed_b` | YES (model half) | L |
| 5 | **Artefact surface unmodeled** (.bbl, corrupt .aux, environment) | (a) `\bibliography` present + `\jobname.bbl` exists ⇒ run structural/T5 scanners over the `.bbl` bytes (it is just TeX); (b) `Aux_state` parse warnings ⇒ conservative NOT-READY ("stale .aux — delete and retry"), not Error→`[]`; (c) cheap preflight: `.aux`/`.log`/`.pdf` writable, CWD writable, `article.cls` resolvable; (d) implement `Missing_bib_entries` or delete the dead constructor + fix comments | no | M |
| 6 | **pdflatex capacity limits absent; ENC coverage inconsistent** | Reject-only gates (safe direction): (a) group depth incl. `\begingroup` >250 ⇒ NOT-READY; (b) coarse main-memory heuristic (token/label mass, calibrated from the measured blowup) with explicit capacity reason; (c) extend ENC compile-blocking to 0x00 and 0x7F; (d) single-line > buf_size ⇒ reject | no | M |
| 4/6 — **status (PR-R7-456)** | **SHIPPED the pure-source, add-NOT-READY-only slice** (no Coq, no file I/O): rank-4 dir-check (`t2_check` requires a non-directory — `fr_dir_target`); rank-6 NUL-byte detector (`fr_nul_byte`) + brace-grouping-levels>255 detector (`fr_grouping_255`, TeX cap verified on TeX Live 2026 at depths 300..20000). All three verified: 0 corpus over-rejection, real-paper differential clean. **DEFERRED:** rank-4 **model half** (real tex→tex edges + genuine cycle check → `fr_two_cycle`, needs recursion + `project_closed_b` re-proof); rank-5 artefact surface (`fr_fatal_bbl`, `fr_corrupt_aux` — needs sibling-file brace-balance + I/O wiring); rank-6 main-memory + buf_size (large generated fixtures). | — | — |
| 5 — **status (PR-R7-5)** | **SHIPPED** (OCaml, no Coq): `unbalanced_open_brace` (net-unclosed `{`, escape/comment-aware, clamps extra `}` to match TeX recovery) + `source_uses_bibliography` in `compile_gate_checks`; new `T_artefact_fatal` reason wired into `check_ready_to_compile` — checks the sibling `.aux` (read at `\begin{document}`) and `<jobname>.bbl` (read at `\bibliography{}`) for the "! File ended while scanning" fatal. Flips `fr_fatal_bbl` + `fr_corrupt_aux`. Verified: a doc with **valid balanced** `.aux`+`.bbl` stays READY; real-paper differential over papers-with-artefacts clean. **DEFERRED:** artefact writability/env preflight (5c) and `Missing_bib_entries` (5d). | — | — |
| 7 | **Fatal-polarity errors + hash-collision over-reject** | (a) OCaml quick wins: `comment`/`filecontents*`/`Verbatim*` added to `parser_l2` verbatim_envs; accept `\end {env}` spacing; model `\[..$$` closure; demote text-mode bare-unclosed-group to warning; (b) Coq train (= deferred Bug 5): move dup-label to the G2 warning channel / drop the `nodup` premise, AND replace 30-bit FNV label ids with full-key comparison in the same re-prove; rename `fail_duplicate_label.tex` (it asserts the wrong polarity) | YES (b) | M |
| 8 | **lp-extended admits non-terminating macro recursion** | conservative detector: `\def` whose body references its own name with NO conditional + a use-site ⇒ NOT-READY/demote. MUST pass a differential sweep vs the real-paper corpus first (the CMD-016 over-rejection post-mortem applies) | no | M |
| 9 | **Superlinear hot spots** (the wedge inverts at scale) | (a) Coq: sort-based nodup replacing `nodup_nat_b` list-membership (43 s → <1 s @ 100k labels), re-extract; (b) OCaml: interval-tree / sorted-array search for `find_ref_alias_macros` / `find_moving_arg_ranges` / `in_ranges_b`; hashtable in `graph_of_build_graph`; (c) rank-2's live-prefix removes the dead-byte tax. Ship WITH the perf sentinel (R7-INFRA-6) | YES (a) | M |
| 10 | **Docs/corpus assertions overstate or invert measured behaviour** | qualify the structural-gate IFF claim as halt-on-error-scoped; fix/delete dead-code comments (`Missing_bib_entries`, cycle reason); re-tier the contradicted `tolerated_*` fixtures; document lint-mode's exit-code non-contract + opt-in `--error-exit`; fold the A10 honesty items into `COMPILATION_GUARANTEE.md` | no | S |
| 2 — **status (PR-R7-inputmodel)** | **SHIPPED `verb_broken_eol_fatal`** (`fr_verb_eol`) — an add-NOT-READY-only structural detector: a real inline `\verb`/`\verb*` whose delimiter does not close before the line end → pdflatex "! `\verb` ended by end of line" (exit 1). Reuses the vcu scanner (a range starting at a real inline `\verb` that spans a newline is exactly the fatal; `\verb` inside comment/env never starts its own range). Adversarially verified (workflow, pdflatex oracle): 0 soundness issues, one exotic over-reject (unclosed `\verb` inside a `\begin{comment}` package env). Baseline **9→8**. Unit tests (compile_gate 69). **`raw_cjk_fatal` was BUILT + hardened over five adversarial rounds, then REVERTED and re-homed** — see **DWR-CJK**: CJK is a verified-feature-model fact (the model already owns `Japanese_cjk`), not a structural detector; it ships as a Coq model train that also fixes the pre-existing CJKutf8 T3 over-reject. | — | — |
| 2/4/7 — **status (PR-R7-struct-batch)** | **SHIPPED three add-NOT-READY-only / detector-precision fixes, each dual-oracled against real pdflatex + verified 0 over-reject on 384 real papers.** (rank-4 model half) `Project_model.has_include_cycle` — a recursive `\input`/`\include` DFS (grey path-stack for back-edges, black visited-set, absolute-path normalisation, fuel-bounded) wired into `t2_check`; the a→b→a cycle that single-level `of_root` + artefact-only `Build_graph.is_acyclic` missed now fires "T2 project not closed" (pdflatex "! TeX capacity exceeded [text input levels=15]") → `fr_two_cycle`. Sound by under-approximation: unresolvable/non-.tex children end a branch, abs-normalisation never over-collapses distinct files → can only MISS a cycle, never invent one. (rank-2) `duplicate_begin_document_fatal` — a 2nd real `\begin{document}` outside comment/verbatim → "Can be used only in preamble" → `fr_dup_begin_document`. (rank-7) dropped `\hyperref` from `moving_arg_commands` — its key is the `[label]` OPTIONAL arg, so listing it wrongly skipped the TYPESET `{link text}`, hiding a `$a^b^c$` double-superscript → `fr_hyperref_linktext`. Verified: hyperref-targeted sweep (30 real hyperref papers) = 0 double-script over-reject. Baseline **12→9** (strong_fatal 8→7, error_halt 4→2). Unit tests added (compile_gate 62, project-model 12). **NB the rank-2 truncation/live-region half and rank-4 kpathsea/resolution-base half remain deferred** (they can *introduce* a false-READY if wrong → dedicated adversarial train). | — | — |

## 4b. Deferred-Work Register (nothing is "dropped" — every item has a plan)

Everything below is **live-tracked**: each row's fixture is a `corpora/false_ready/` entry whose
`expected_cli` is still `READY` (so the monotone CI gate holds it), and each has a concrete unblock
design, its prerequisites, and its risk-polarity. "Dropped after N false-READYs" means *this approach
was falsified by adversarial verification* — it does **not** mean abandoned; the corrected design is
recorded here and the fixture stays in the ledger until it flips. **Risk-polarity is the key
discriminator:** for STRUCTURAL-fatal detectors, over-skip ⇒ under-fire ⇒ *sound* (add-NOT-READY); for
FEATURE detection (needs xelatex/opentype/CJK), UNDER-detect ⇒ **false-READY (cardinal)**, so those
trains must err toward *over*-detecting and be proven never to over-skip.

**DWR-1 — Shared `\verb`/`\lstinline` scanner fix (OR-1). PREREQUISITE for DWR-2.**
No fixture flip; fixes a pre-existing *over-reject* (`\lstinline[language=C]|..|` — the scanner in
`validators_common.compute_verbatim_comment_url_ranges` (~L560-575) takes the `[` as the verb
delimiter and over-runs; `\verb` also fails to stop at EOL). Design: (a) for `\lstinline`, consume the
optional `[...]` key-val arg *before* reading the delimiter; (b) bound the `\verb` scan at the line end
so its range is `[start, min(close_delim, EOL))`. **Coordinate with `verb_broken_eol_fatal`** (DWR
depends on the range spanning the newline today) — after this fix the detector keys off "range ended at
EOL with no close" instead. Risk: it *removes* NOT-READYs, so prove no case flips to a false-READY.
Sequence: FIRST (it unblocks DWR-2 and is independently useful).

**DWR-2 — Comment-awareness for FEATURE detection (`fr_comment_comma`, `fr_comment_beforearg`).**
Dropped after **6 false-READYs across 3 rounds** — the lesson: *blanking any scanner-identified region
inherits that scanner's over-extension as a false-READY*, and feature-detection polarity makes
over-skip the CARDINAL bug. Falsified approaches: blanking the full verbatim-env set (alltt/listing
*execute*), blanking `{verbatim,verbatim*,comment}` (`\newenvironment{comment}` passthrough executes),
blanking `\verb`/`\lstinline` (shared-scanner over-extension erases a live `\setmainfont`). **Corrected
design — LOCAL comment-skip, not global blanking:** make `uses_package_b` (VERIFIED
`BodyTokenFrontEnd.v`) parse `\usepackage[opts]{names}` the way TeX does — skip a `%…\n`
comment-continuation *within the construct only*, so a distant live feature can never be stripped. This
is bounded ⇒ cannot manufacture a false-READY by over-stripping. Re-prove capstone axiom-free +
re-extract + front-end parity. Prerequisite: DWR-1 (any residual global inert use). Risk: FEATURE
polarity (under-detect = false-READY) → conservative, heavy adversarial pass. Sequence: after DWR-1.

**DWR-3 — rank-2b live-region (`fr_endinput_before_end`, `fr_end_in_iffalse`, `fr_caret_brace`). HIGH
RISK — the one train that can INTRODUCE a false-READY.** `\endinput`-before-`\end{document}` naive
detection over-rejects the common `\ifdefined\previewmode\endinput\fi` / `\ifdraft\endinput\fi` (arXiv)
→ needs a *conditional-liveness* model (is the `\endinput` reachable/unguarded?). `\iffalse…\fi` makes
its enclosed `\end{document}` dead → needs an `\iffalse`/`\newif` region model. `fr_caret_brace`
(`^^7b`→`{`) needs `^^`-decode + brace-balance. **The dangerous part is TRUNCATION**: truncating the
scanned source at a *dead* `\end` (inside `\iffalse`) drops live content ⇒ false-READY if the model is
wrong. Design: a conservative live-prefix pass (model `\iffalse..\fi` dead, `\endinput` as EOF only
when provably unguarded), specified in Coq (it changes what the verified model reads). Risk: HIGHEST —
its own dedicated adversarial train with a full real-paper differential before any truncation ships.
Sequence: after DWR-2; do NOT bundle truncation with the cheap arms.

**DWR-4 — rank-1 tail loaders (`fr_lowercase_loader`, `fr_csname_loader`).** `\lowercase{\usepackage{FONTSPEC}}`
lowercases to `fontspec` at execution (case-sensitive needle misses it); `\csname…\endcsname`-built
loaders have no literal `\usepackage` token. Design: detect `\lowercase{…\usepackage…}` with a
case-fold, and `\csname`-assembled loads — both are macro-execution modeling. Low volume / hard-rare.
Risk: FEATURE polarity (under-detect = false-READY). Sequence: last of rank-1.

**DWR-CJK — Raw-CJK correctness, as a VERIFIED-MODEL train (NOT a structural detector).** Fixture
`fr_raw_cjk` (highest-volume, 4.1%). **A structural `raw_cjk_fatal` was built and adversarially
hardened over FIVE rounds, then DELIBERATELY REVERTED** — not for unsoundness (it is add-NOT-READY-only;
its over-reject side stayed clean) but because it is **architecturally misplaced**: the *verified* model
already owns the feature. `compile_evidence.ml:328` / `BodyTokenFrontEnd.v:483` detect `Japanese_cjk`
from `\usepackage{CJK}` / `\begin{CJK}` (but NOT from raw bytes — the `fr_raw_cjk` gap); `compile_contract.ml:40-41`
gates it (`Japanese_cjk, Ptex_uptex -> true; _, _ -> false`). That table is ALSO wrong — `\usepackage{CJKutf8}\begin{CJK}…\end{CJK}`
**compiles under pdflatex** (oracle exit 0) yet T3 rejects it: a pre-existing **false-NOT-READY**. So CJK
is one mis-modelled feature with **two-sided breakage** (raw-byte false-READY + CJKutf8 false-NOT-READY),
fixable only together, in the model. **Design:** (1) extend the verified `Japanese_cjk` detection to raw
3-byte CJK-block bytes; (2) fix T3 so `japanese_cjk` is admitted under pdflatex when a pdflatex-CJK
package (`CJKutf8`/`CJK`) is present; re-prove capstone axiom-free + re-extract + parity. **Reuse the
model's `uses_package_b`** (options-tolerant, `\usepackage{}`-anchored — the correct package detector)
rather than hand-rolled substring matching. **Reference implementation + the 6 falsified findings are
saved** (scratchpad `DWR-CJK-reference.ml`). The hard-won EXEMPTION SPEC to carry over (all
oracle-verified): body CJK is fatal even inside `\verb`/verbatim (inputenc decodes the bytes — exempt
ONLY comments + url); `\newunicodechar`/`\DeclareUnicodeCharacter` exempt PER-CODEPOINT and only when
(a) outside comment/verb/verbatim, (b) UPPERCASE hex for `\DeclareUnicodeCharacter`; **INVARIANT: every
source read for an exemption must be inert-aware AND token-anchored** — the 6th falsified round showed
loose global substring package-matching falsely exempts any prose mentioning "fontspec"/"CJK". Residual
coverage for the same train: widen block table (U+2E80–2EFF, U+2F00–2FDF, U+A000–A4CF, U+D7B0–D7FF) and
4-byte Ext-B (U+20000+) — both under-fire = safe. **LESSON: CJK-detection-as-structural-gate is the
wrong layer; a compile-compatibility fact about a Unicode feature belongs in the verified feature model,
where package detection is already correct.** Sequence: its own model train (Coq); the 5-round
hardening is the spec, not wasted.

*Implementation mechanics (de-risked by reading the proofs).* Add a `|| has_raw_cjk_b src` disjunct to
the `Japanese_cjk` block of `detect_body_features` — in BOTH `BodyTokenFrontEnd.v:480` (Coq) and
`compile_evidence.ml:327` (OCaml hand-mirror). **The capstone stays axiom-free for free:**
`body_required_features_of_source` (`BodyTokenFrontEnd.v:1307`) is proved GENERICALLY over
`detect_body_features` (it rewrites with the app/events/feats lemmas, never case-analysing the feature
internals), so a new well-formed boolean disjunct cannot break it; `compile_safe_of_source` only gets
STRICTER (more features ⇒ more T3 checks ⇒ fewer READYs), preserving READY⇒safe. **Part A alone closes
`fr_raw_cjk`** because the EXISTING T3 already rejects `Japanese_cjk` under pdflatex
(`compile_contract.ml:41`); the CKJutf8 T3 over-reject is the separable **Part B**. The binding
constraint is exact **OCaml↔Coq parity** (`test_body_token_frontend.ml check_parity`): `has_raw_cjk_b`
(terminating fuel-bounded `list byte` scan, style of `scan_from`) must byte-match the OCaml mirror
(adapt the hardened OCaml reference implementation preserved out-of-tree from the reverted structural
detector). Reuse the verified `uses_package_b` for the package check.
Re-extract via `scripts/tools/regen_body_token_frontend_extract.sh`; parity swept over the corpus; then
`Print Assumptions compile_safe_of_source` must still print "Closed under the global context". The exact
exemption polarity (which contexts flag vs compile — notably whether `CJKutf8`/`CJK` make raw bytes
compile only INSIDE their `\begin{CJK}` env, so raw bytes outside STILL flag) is pinned by a pdflatex
oracle-map before any Coq is written.

**`has_raw_cjk_b` SPEC (pinned by pdflatex oracle-map, four categories).** Fires iff there exists a
candidate CJK codepoint in a live, non-exempt region whose codepoint is not declared. Over-detect is
sound (over-reject); under-detect is the cardinal false-READY → lean to flag. (1) **Candidate byte:** a
well-formed UTF-8 sequence with codepoint ≥ U+3000 — 3-byte lead `0xE3..0xEF` OR 4-byte lead
`0xF0..0xF4` (covers Ext-B + emoji, both not-set-up). **EXCLUDE lead `0xE2`** (U+2000–2FFF: em/en-dash,
ellipsis compile fine — flagging them mass-over-rejects English prose) and all 2-byte (latin-1). (2)
**Exempt regions = comments + url-family ONLY** (`\url`/`\path`/`\nolinkurl`/`\href` first arg) — a
NARROWED vcu set that DROPS the verbatim/`\verb`/lstlisting members (raw CJK there STILL fails, exit 1).
(3) **CJK-env-interior exemption:** bytes strictly inside a live `\begin{CJK}…\end{CJK}` span, GATED on
`uses_package_b p_cjk || uses_package_b p_cjkutf8`. **⚠ THE ORACLE CORRECTION that condemns the
structural version: there is NO blanket package-skip** — with `CJKutf8` loaded, a raw 中 *outside* the
`\begin{CJK}` env STILL fails (exit 1), so the exemption is SCOPED to the env interior, never the whole
document (my reverted `has_pkg` skipped the whole doc = a real over-exemption). `xeCJK`/`luatexja`/
`fontspec`/`ctex` hard-fail under pdflatex regardless → never exempt. (4) **Per-codepoint declaration
exemption:** build set D from the PREAMBLE (before `\begin{document}`), LIVE (non-comment/verb/verbatim)
`\newunicodechar{<char>}` and `\DeclareUnicodeCharacter{<UPPERCASE-HEX>}` (lowercase hex is invalid →
ignored); a body codepoint is exempt iff its exact codepoint ∈ D. **Two colliding notions of "inert":**
the BODY scan exempts only comments+url (verb/verbatim FIRE); the DECLARATION scan treats
comment/verb/verbatim as dead (a declaration there does NOT exempt). Wiring: OR `has_raw_cjk_b` into the
`Japanese_cjk` disjunct only; existing package/env detection unchanged; existing T3 does the rest.

**DWR-CJK — status (PR-cjk-model, Part A v1 SHIPPED).** `has_raw_cjk_b` added to the VERIFIED front-end
(`BodyTokenFrontEnd.v`) + exact OCaml mirror (`compile_evidence.ml`), OR'd into the `Japanese_cjk`
disjunct; re-extracted, **front-end parity 426**, capstone **axiom-free** (`compile_safe_of_source`
"Closed under the global context" — the generic `body_required_features_of_source` theorem absorbed the
new disjunct with no re-proof). Flips `fr_raw_cjk` via the EXISTING T3 (`Japanese_cjk`→pdflatex `false`).
Baseline **8→7**. **⚠ THE DIFFERENTIAL CAUGHT A DESIGN ERROR before ship:** the first cut used a LOOSE
lead-byte test (any 3-byte ≥ U+3000) and over-rejected **four of the author's own English papers** on a
copy-pasted ﬁ ligature (U+FB01, which pdflatex COMPILES). Root lesson: *CJK-feature detection is not
"any unset Unicode char".* v1 therefore DECODES the codepoint and range-checks four definite-CJK blocks
only — U+3000–9FFF, U+AC00–D7A3, U+F900–FAFF, U+FF00–FFEF (= the oracle-validated structural `is_cjk`) —
excluding ﬁ AND the replacement char � (U+FFFD, a *non-CJK* fatal). A range-validation workflow
(pdflatex oracle) confirmed **0 in-range over-rejects** (every in-range codepoint fails pdflatex = correct
catch) and 0 real-paper over-rejects. **v1 has NO exemptions** (scans every byte ⇒ over-detect only ⇒
sound); the comment/url/env/declaration exemptions above and the CKJutf8 T3 fix (Part B) are the tracked
refinements. **Under-approximation = sound (add-detection-only, introduces zero false-READY).**

**DWR-CJK-2 — raw UNSET non-CJK / CJK-adjacent codepoints (the pre-existing gaps v1 does not close).**
These codepoints FAIL pdflatex "not set up" but fall OUTSIDE v1's four CJK blocks, so they remain the
pre-existing false-READYs they were before this change (v1 introduces none of them). Enumerated by the
range-validation workflow, by block: CJK Radicals Suppl (U+2E80–2EBF), Kangxi Radicals (U+2F00–2FD5),
Ideographic Description (U+2FF0), Yi Syllables/Radicals (U+A000–A4CF), Lisu (U+A4D0), Hangul Jamo
Extended-A/B (U+D7B0–D7FF), CJK Ext-B and beyond (4-byte, ≥ U+20000), Specials (U+FFFD replacement),
plus obscure unset symbols scattered in U+2000–2FFF (the 0xE2 range). Design: widen `is_cjk_cp` to the
CJK-adjacent blocks that are ENTIRELY unset (Yi, radicals, Hangul-Jamo-ext — each oracle-validated
before adding, since a set-up member would flip it to an over-reject) and add 4-byte decoding for Ext-B;
the non-CJK unset cases (U+FFFD, stray symbols) want a SEPARATE "raw unsupported codepoint" fatal, not
the `Japanese_cjk` feature (semantically wrong to label a corrupt byte "Japanese"). Risk: FEATURE
polarity (each widening must not over-reject a set-up member). Sequence: follow-up after Part A.

**DWR-6 — Multi-file structural gate (ARCHITECTURAL; shared by ALL structural detectors).** `structural_fatal_reasons`
sees only the ROOT source, so a CJK/`\verb`-EOL/double-script fatal living in an `\input` child is
invisible (a real READY-but-fails hole for every detector, not CJK-specific). Design: run the
structural gate over the resolved **include closure** (reuse `Project_model`'s resolver from
`has_include_cycle`), not just the root. Risk: over-reject if a resolved "child" isn't actually input
(bound it to the same resolver + comment-aware `scan_includes_live`). High value (fixes all detectors
at once). Sequence: its own PR; genuine CJK/foreign projects almost always load a package (which
correctly skips), so real-world exposure is low — schedule after the rank trains.

**DWR-7 — rank-4 kpathsea / resolution-base half.** `t2_check` include resolution: `kpsewhich`
fallback for system files, documented resolution base + `--workdir`, `\include` vs `\input` missing-file
polarity. Runtime-only (no Coq). Sequence: opportunistic.

Each DWR entry flips its fixture(s) and lowers `manifest.json`'s `baseline` when it lands; the gate
enforces monotonicity so none can silently regress. The rank rows in §4 remain the strategic map; this
register is the *execution* checklist with the falsified-approach history attached.

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
   today.) **PR-R7-0 shipped the LOCAL form**; ✅ **LANDED in full (#516)** —
   `.github/workflows/tex-oracle.yml` runs both scripts inside a digest-pinned TeX Live 2026 image
   with `REQUIRE_PDFLATEX=1`. Measured while building it: engine YEAR is NOT the fragile axis
   (TL2024 vs TL2026 = zero drift, byte-identical error text on all 21 fixtures); install
   COMPLETENESS is, and it fails BOTH ways — missing fonts flip all 8 error-halt fixtures to
   strong-fatal (cry wolf), while a missing `.sty` grades strong-fatal *identically to the intended
   fatal* (silent green). Hence the HARD/SOFT drift split and the install canary. The gate is
   ADVISORY on arrival: `branch-protection.yml` sets `enforce_admins: true`, so a red required
   check would be unbypassable even by the maintainer.
3. **Oracle-truth corpus snapshot** — per-doc {verdict, reason class, HALT/NOSTOP/PDF triple,
   timing} committed as golden TSVs; verdict flips require an explicit fixture-update commit.
   Simultaneously fix the polarity-inverted fixtures.
4. **apply-fixes round-trip gate** — for every corpus doc, both fixer modes must be (a) idempotent,
   (b) oracle-class-preserving (compiling docs still compile), (c) verdict-non-degrading.
5. **SEC-EXTRACT + mirror-fuzz** — ⚠️ **HALF LANDED (#513).** The SEC-EXTRACT half is done:
   `scripts/tools/check_extract_identity.py` re-runs each regen script in `proof-ci` (a REQUIRED
   context) and compares against the committed file. It compares the PARSED AST
   (`ocamlc -stop-after parsing -dsource`) rather than raw bytes, because `.ocamlformat` pins no
   version and a byte-compare would redden on every formatter upgrade — equally strict about
   meaning, immune to formatting. #513 also asserts `Print Assumptions` output for all four
   capstones, which was previously printed and never read. **The mirror-fuzz half is NOT done**: no
   property fuzzer asserts OCaml-mirror == Coq-extract on hostile byte streams. §6.4 names it the
   systematic answer to the mirror-vs-extract surface, so that surface remains open.
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
