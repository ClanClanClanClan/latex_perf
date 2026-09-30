> **Repository note (2026-09-30).** Historical design draft, committed verbatim below this note as the owner
> read it when deciding ADR-015. It was written in a session scratchpad (design-interp/ADR-014-draft.md, written by the ADR-014 design agent on 2026-09-29 (07:38 UTC)) and never
> committed there; the scratchpad was wiped, and this copy was rebuilt from the session transcripts: the
> agent's `Write` of the file plus its later in-place edits, replayed exactly (sha256 of the text below this note:
> `67b06f7ed434d67f8303adb8a4c4336b8e02f477ea93fde7ef35f2406721f417`). Scratch paths it cites (`design-*/`, `m/`, `src/`, probe scripts) were not kept.
> **Status: superseded by [ADR-015](../ADR-015-static-proven-tier-on-translated-engine.md)**, which records what was
> decided; where a measurement below was later corrected, ADR-015 and `docs/v27/spike/H1-report.md` say so.

# ADR-014 (DRAFT) — A verified TeX interpreter: decide a document by executing pdfTeX's own program

**Status:** DRAFT design for owner review, 2026-09-29. Nothing here is implemented or committed.
**Companion to:** ADR-013 (DRAFT, R-EFFECT). The owner asked for two architectures designed to the same depth before choosing. This is the second one.
**Extends / replaces:** ADR-012's decision 1 mechanism (the whitelist grammar `L_S` and the per-name contract), not its goals, verdict type, renderer, oracle, or exit codes.
**Read from:** `origin/main` = `35d93fe1`; branch `feat/v27165-strict-args` = `96a1695b` (C-92..C-98, OPEN-122); the ADR-013 draft.

**Evidence tags.**
- **[M]** measured for this draft on 2026-09-29, in a fresh `docker run --rm` of the pinned image `4984977ccf5a` (pdfTeX 3.141592653-2.6-1.40.29, TeX Live 2026) with `SOURCE_DATE_EPOCH=0 openin_any=p openout_any=p`, `-interaction=nonstopmode -halt-on-error`. These runs are **not** the oracle protocol (no `_oracle.py`, one pass unless stated); they are measurements for design, never grades. Inputs are in `design-interp/m/` next to this file.
- **[R]** read from source. `tex.web` (Knuth, CTAN, 25,011 lines, 1,380 sections; sha256 prefix `c62ab513ef167e93`); `pdftex.web` 1.40.29 from TeX Live **trunk** (40,334 lines, 1,868 sections, sha256 prefix `38537f10300d66d7`), `tex.ch`, `texmfmp.c`, `texmfmp.h`, `texmfmem.h`, `pdftexdir/am/pdftex.am`, `*.defines`; copies in `design-interp/src/`. The image contains **no** WEB sources (checked: no `tex.web`/`pdftex.web`/`*.ch` anywhere in it), so the sources used below are the trunk revision that carries the same version string, **not yet proven to be the pinned binary's revision** (spike step H.1).
- **[I]** inferred. **[U]** unknown; a measurement is named.

Section numbers `§n` are `tex.web` sections unless marked `pdftex.web §n`.

---

## 0. The proposal in nine sentences, and the honest verdict in one paragraph

1. **Do not write a semantics of TeX. Translate pdfTeX's own program into Coq.** TeX Live builds pdfTeX by merging `pdftex.web` with 16 change files (`tie`), tangling to Pascal, and translating the Pascal to C (web2c). This design runs the same merge and tangle, and translates the *same Pascal* mechanically into a Coq deep embedding, under a small, generic, human-reviewed operational semantics of the Pascal subset that TeX uses (`PS`).
2. **The state is tex.web's own globals, bit-exact**: `mem`, `eqtb`, `hash`, `str_pool`, `save_stack`, `input_stack`, `cond_ptr`, `nest`, the page builder's variables, `font_info`, the `\write` streams, `history`, `interaction`. Capacities (C-86, C-94, C-98) are then not *modelled*; they are the same arrays with the same sizes and the same allocator, so they overflow at the same step **by construction**.
3. **The format is data**: the shipped `pdflatex.fmt` is loaded by the translated `load_fmt_file` (§1303, plus TeX Live's `zlib-fmt.ch`). `latex.ltx`, `expl3`, the class and every package are executed from their real code, so composition (look-ahead, mode after use, page position, stored representations, hooks, sockets, patches) is correct by construction and nothing is ever admitted per name.
4. **The C boundary is the only hand-written model**: TeX Live's `input_line`, first-line parsing, kpathsea lookup over a content-hashed file-system snapshot, `texmf.cnf` sizes, date/time/random seed, the terminal, and the effects of pdfTeX's C libraries on TeX state (image dimensions, font-embedding success, `\pdfstrcmp`, `\pdfmdfivesum`, …). About 250 C entry points exist [R: `@define` lines: 104 common, 50 texmf, 103 pdfTeX]; most are generic runtime or PDF-byte output with no effect on TeX state.
5. **The decision is execution.** A fuelled interpreter returns `Compiles`, `Fatal(message, context, l.N)`, `Diverges` (exact state repetition with no output), or `Stuck(reason)`. PROVEN-READY / PROVEN-NOT-READY come only from the first three; `Stuck` is outside the tier. There is no membership predicate and no static screen.
6. **One named premise, fixed per engine pin, independent of every package**: `FaithfulEngine` — the pinned binary's observable outcome under the oracle protocol equals the model's. It decomposes, by a Coq simulation theorem, into per-unit premises (≈ 200–300 units: main-control cases, `expand` cases, `get_next`, `build_page`, `fire_up`, `line_break`, `hpack`, …) plus `F-PS` (web2c's C implements the Pascal semantics) and `F-C` (the boundary models).
7. **Attestation is lock-step co-simulation**, not only whole-document differential: an instrumented build of the pinned source dumps a state digest after every main-control iteration; the model must agree **at every step** on every corpus and generated document. A branch-coverage-directed generator drives every reachable branch of the translated program. The whole-document differential remains, as a check.
8. **Layout is exact** (TeX's layout is integer arithmetic in sp; the one `double`, `glue_ratio`, reaches TeX state only through `\pdfsavepos`). An abstract domain is still **mandatory**, for a different reason: the oracle runs on the real clock, so `\time`, `\day`, `\month`, `\year` are nondeterministic inputs [R+M], as are `\pdfrandomseed` and `\pdfelapsedtime` [R]. A verdict must hold for every value, so those inputs are abstract, branches on them fork, and identical states merge.
9. **The payoff is a step function.** Nothing is decided on a real paper until the whole engine, the format load, the C boundary and the TeX side of shipout are in place. Then, with no per-package work, every document whose execution does not reach a `Stuck` cause is decided. Estimated at 60–90 % of the unsealed frame [I, wide; measured only after stage G5], against ADR-013's measured census bound of ≤ 4 bodies at its S3.2–S3.5 and "low single digits" at S3.6.

**The honest verdict.** This architecture removes the four failure classes that stopped the per-name track:
- modelling errors (C-83, C-84, C-85);
- missing capacities (C-86, C-94, C-98);
- screens that under-read the code (C-92, C-96);
- composition holes (look-ahead, mode, page position, stored representations).

It removes them because nothing about TeX's behaviour is written by us. What it keeps is **the C boundary**. That is exactly where the project's *other* recent defects lived: C-89 (TeX Live's first-line parsing) and C-91 (environment and argv channels). The boundary therefore gets the most scrutiny here (§2.6, §6).

Its costs are real:
- It is all-or-nothing for real papers.
- It is 10–100× slower than pdfTeX [I; spike H measures it].
- Its Coq theorems have little mathematical depth. The weight sits on one fixed premise, attested as thoroughly as empirical attestation can be.

It also forces a question ADR-012 left implicit (§10.3, decision O-1). If the checker is, in effect, a re-execution of pdfTeX, why not run the pinned pdfTeX on the body? Decision 3 forbids that. This design complies with the letter of decision 3, and the owner should confirm it complies with the *reason* for it.

---

## 1. Facts this design rests on

| # | fact | tag |
|---|---|---|
| F1 | pdfTeX is built from `pdftex.web` + 16 change files merged by `tie`: `tex.ch0`, `tex.ch`, `tracingstacklevels.ch`, `partoken-102.ch`, `partoken.ch`, `locnull-optimize.ch`, `showstream.ch`, `zlib-fmt.ch`, three encTeX files, `unbalanced-braces.ch`, `pdftex.ch`, `char-warning-pdftex.ch`, `tex-binpool.ch` (plus the head of the list), then tangled and converted by web2c | [R] `pdftex.am` lines 51–86 |
| F2 | `pdftex.web` 1.40.29: 40,334 lines, 1,868 sections, 549 `primitive(` calls, 139 `print_err` sites, 92 `pdf_error` sites, 37 `overflow` sites, 46 `confusion` sites, 615 `goto`s. `tex.web`: ≈ 16.9k code lines, 482 `goto`s | [R] counted |
| F3 | the pinned format defines 554 primitives (551 multiletter + 3 control symbols), and 23,519 kernel names with a recorded `meanings_sha256` | [R] `corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json` |
| F4 | `glueratio` is C `double` in TeX Live (`GLUERATIO_TYPE` default) | [R] `texmfmp.h` 185–188 |
| F5 | `\pdfrandomseed` is initialised from the clock: `random_seed := (microseconds*1000)+(epochseconds mod 1000000)` | [R] `pdftex.web` line 33599 |
| F6 | the oracle sets `SOURCE_DATE_EPOCH=0` and **not** `FORCE_SOURCE_DATE`, so `\time`/`\day`/`\month`/`\year` (and so `\today`, expl3's `\c_sys_*`) follow the grader's real clock | [R] `_oracle.py` lines 166–224; the contract generator already treats six `c_sys_*` names as date-dependent (F3's file) |
| F7 | the shipped `pdflatex.fmt` (3,658,242 bytes) is **not** byte-reproducible: rebuilding it in the image with the recorded command (`pdftex -ini -jobname=pdflatex -progname=pdflatex -translate-file=cp227.tcx *pdflatex.ini`) gives 3,658,241 bytes, differing from byte 229,028 | [M] |
| F8 | building the format takes 14.8 s; a one-line `article` document 0.26 s; a synthetic 12-page `article`+`amsmath`+`amssymb`+`amsthm`+`graphicx`+`hyperref` paper (`m/p.tex`, 30 kB) 0.64–0.68 s per pass | [M] |
| F9 | the same paper, traced: ≈ 335k macro expansions, ≈ 210k assignment lines and ≈ 200k conditional lines over the whole run, of which ≈ 73k / 56k / 55k fall in the body. The preamble (with `hyperref`) is ≈ 3/4 of the interpretive work. It used 573,362 words of main memory, 39,021 multiletter control sequences, and 57 fonts | [M], counts from `\tracingmacros=2 \tracingassigns=1 \tracingifs=1` logs, approximate (line-wrapped logs) |
| F10 | the body of that paper executes `\scantokens`, `\pdfmdfivesum`, `\pdffilesize`, `\pdfstrcmp`, `\pdfescapestring`, `\halign`, `\mark`, `\vadjust`, `\shipout`, `\input`, `\jobname`, `\uppercase`, `\ignoreprimitiveerror`, among 181 distinct traced command names | [M] |
| F11 | `x \section{a}\par\unskip x` fails (`! You can't use \unskip in vertical mode.`, l.3). `x \par\unskip x` and `x\par\vskip 1pt\penalty0\unskip x` compile. The mechanism is `delete_last` (§1105): with an empty contribution list it refuses exactly when `last_glue ≠ max_halfword`, and `build_page` sets `last_glue` from the last item moved to the page (§996) | [M] + [R] |
| F12 | the unsealed frame: 1,117 of 1,119 roots stop at the front matter under the current kernel; median 16 packages; 782 load `hyperref` | [M, OPEN-122 / ADR-013] |

---

## 2. (A) The engine semantics: translate, don't transcribe

### 2.1 Why the task's (A) is refined

The task asks for "a Coq semantics of TeX's primitives transcribed from tex.web". A hand transcription of ≈ 17k lines of `tex.web` code, plus the ≈ 15k further code lines of pdfTeX and e-TeX, would be written by us. So it would inherit the failure mode of every Runs constructor so far (C-83: "a constructor is a claim about pdflatex until a probe agrees"), multiplied by about 1,000 sections. Every section transcribed by hand is a place where our reading can differ from the program.

**A mechanical translation has one failure surface, and it is generic**: the translator and the Pascal-subset semantics. A bug there is systematic. It shows up on the first documents that exercise the construct, and step-level co-simulation (§6.2) localises it to one statement. This is what web2c already does for C, and what `web2js` did for WebAssembly, so the approach is known to be feasible at this scale [R: web2c exists and builds TeX Live; `web2js` is public prior art].

"Transcribed from tex.web" therefore becomes: **the tangled `pdftex.p` of the pinned revision, translated statement by statement into a Coq AST.** Review against tex.web still happens, but it reviews the *translator's* rules once (≈ 40 constructs), not 1,868 sections.

### 2.2 The Pascal-subset semantics `PS` (the human-reviewed layer)

A deep embedding. The translator emits `prog : PS.program` (declarations, ≈ 1,400 procedures and functions after tangling [I], one AST per body). `PS` is:

- **Values.**
  - Integers are C `integer` (32-bit in web2c [U: confirm `INTEGER_TYPE` for the pinned build; H.1]). Every signed overflow is **`Stuck(ub_overflow)`**, never a wrap: C gives it undefined behaviour, and a document that reaches it is outside the tier. TeX guards its user-visible arithmetic itself (`\multiply` → "Arithmetic overflow", `\numexpr` checks), so this cannot mask a TeX error.
  - `div`/`mod` truncate toward zero, as in C99.
  - `real` is IEEE binary64 (`PrimFloat`). It occurs only in `glue_ratio`, and in the few `unfloat`/`float` conversions and `round` (web2c's `zround`).
- **Arrays** are Coq primitive persistent arrays (`PArray`, O(1) in linear use, extracted to OCaml arrays with version rerooting). An index outside the declared bounds is **`Stuck(ub_bounds)`**. C does not check bounds; a document that reaches such an access is outside the tier, and one that does not is unaffected.
- **`memory_word`** is 8 bytes, stored bit-exactly as two 32-bit halves, with accessors that reproduce `texmfmem.h`'s little-endian union layout: `hh.rh`, `hh.lh`, `hh.b0`, `hh.b1`, `qqqq`, `cint`, `sc`, and `gr` (the 8 bytes read as a `double`). This matters because TeX reads fields it did not write through the same accessor (type/subtype inside `lh`), and because the `.fmt` is a raw dump of these words. arm64 and amd64 are both little-endian, so one layout serves both images.
- **Control.**
  - `goto`s are compiled per procedure into a label-indexed loop, the way web2c and web2js do.
  - Non-local exits (`jump_out`, `goto final_end`, `goto end_of_TEX`) are exceptions of the monad.
  - `return` is an early exit.
- **Externals.** Every C function that the tangled program calls (listed from the `.defines` files) is a constructor `Ext name args`, interpreted by the C-boundary model (§2.6). An external with no model is **`Stuck(unmodelled_external name)`**.
- **Two interpreters of the same AST:**
  - `exec`: fuelled, big-step, over concrete values;
  - `exec#`: the same code over an abstract value domain (§5.2).

  Both are proved against the relational semantics `PS.Step`, which is the object a human reviews against the Pascal report and web2c's C output. For speed, a closure compiler `compile : stmt -> (store -> result)` is proved equal to `exec` (a standard staged-interpreter proof), and it is what is extracted (§7).

### 2.3 The state

`Store` = the values of every global of the tangled program. This is not an abstraction of TeX's state; it *is* TeX's state, including:
- the parts the owner's failure history turned on: `mem` (lists, token lists, the page and contribution lists), `eqtb` (catcodes, `\endlinechar`, registers, parameters), `save_stack`, `cur_level`, `cur_group`, `input_stack`, `line`, `buffer`, `cond_ptr`/`if_stack`, `nest` (mode, space factor, prev_depth), `page_contents`, `last_glue`/`last_penalty`/`last_kern`, `output_active`, `dead_cycles`, `write_open`/`write_file`, `interaction`, `history`, `error_count`, `str_pool`/`str_start`, `hash`/`hash_used`/`hash_extra`, `font_info` and the font arrays, the hyphenation `trie`;
- pdfTeX's additions (`pdf_mem`, object tables, link and destination state, the `\pdfsavepos` registers).

What is *not* in `Store` is what the C side holds: open `FILE*` buffers and the bytes already written to disk. These are held by the boundary model as a file-system state (§2.6).

**Why pointer-level and not algebraic.** An algebraic model (token lists as Coq lists, nodes as an inductive type) gives nicer proofs. It fails three of this project's hardest lessons:
- capacities would again be a *separate account* that can miss a multiplicative channel (C-98: memory = depth × tokens);
- the `.fmt` would need a decoder from raw words into the algebraic form, and that decoder is a second, hand-written model of the dump;
- "confusion()" and allocator behaviour would be approximations.

With a bit-exact store, all three are the program's own code.

### 2.4 The task's list, mapped to program parts (nothing is written per construct)

| task item | where it lives in the translated program | notes |
|---|---|---|
| input processor with dynamic catcodes, `\endlinechar`, `\input` | `get_next` §341–§357, `firm_up_the_line`, `begin_file_reading`/`start_input` §537, `input_ln` → boundary `input_line` | catcodes are `eqtb` reads, so dynamic by construction; `\endlinechar` is appended by the boundary's line model (the proven `Lexer.v` line model is reused, §8.3); `^^` reduction §352–§355 |
| expansion | `expand` §366–§380, `macro_call` §389–§399 (delimited parameters, `\par` in non-`\long`), `insert_relax`, `\expandafter` §368, `\noexpand` §369, `\csname` §372, conditionals §487–§510, `\the`, `\number`/`\romannumeral` §464–§470; e-TeX `\protected`, `\unexpanded`, `\detokenize`, `\scantokens`, `\numexpr` family; pdfTeX `\expanded`, `\pdfstrcmp` (boundary), `\ifincsname`, `\ifpdfprimitive` | the C-85 case (display `$` expands its follower) is §1197 (`get_x_token`), executed and not modelled |
| stomach (non-layout) | `main_control` §1030–§1045, `prefixed_command` §1211–§1280, `new_save_level`/`unsave` §274–§284, `\aftergroup`/`\afterassignment`, `handle_right_brace` §1085, math entry/exit `init_math` §1138 / `after_math` §1194, alignment §768–§812 | alignment is *not* optional: the synthetic paper's body runs `\halign` [M, F10] |
| layout | packaging §644–§679, line breaking §813–§890 with hyphenation §891–§965, page builder §980–§1028, math typesetting §699–§767 | exact, integer (§5.1) |
| error sites | every `print_err` (139), `pdf_error` (92, into the boundary), `overflow` (37), `confusion` (46), `fatal_error`, `succumb` | with `-halt-on-error`, `error` stops at the first error (`tex.ch`: `if (halt_on_error_p) then … history:=fatal_error_stop; jump_out`); the model reports the exact message string and `show_context` output |
| `\write`/`\openout` | §1340–§1378 (whatsits: out-of-line expansion at shipout, `write_out` §1370) | the delayed `\write` expands **at shipout** with the state of that moment. This is how `\label` in a moving context, and `\thepage`, behave; exact because shipout is exact |
| capacities | the same arrays with the sizes that `texmf.cnf` gives the binary: `main_memory`, `extra_mem_*`, `save_size`, `stack_size`, `buf_size`, `pool_size`, `hash_extra`, … | sizes are boundary data, read from the image's `texmf.cnf` by the modelled kpathsea, and attested by the capacity lines of every oracle log (F9 prints them) |
| halting protocol | `final_cleanup`, `close_files_and_terminate` (pdfTeX finishes the PDF), exit status from `history` (`tex.ch` `do_final_end`: `uexit(1)` unless `history` is `spotless` or `warning_issued` [R]) | the model's outcome includes rc, the page count and the "Output written" line |

### 2.5 What is still *our* modelling: the C boundary, enumerated

This is the part the owner should read hardest. Every row is hand-written Coq with its own relational spec and its own attestation (§6.3).

| id | C boundary | effect on TeX state or outcome | model | attestation |
|---|---|---|---|---|
| C1 | `input_line` (texmfmp.c) | line bytes, trailing-space trim, CR/LF/CRLF, buffer overflow "Unable to read an entire line" | **reuse** `Lexer.v`'s `Lines` model (already proved, C-89-hardened) | exhaustive byte-class tests, already 2,167 + 2,847 graded |
| C2 | first-line `%&` parsing, TCX, `-translate-file` (the TCX tables are dumped in the fmt) | format switch → outside; printable table for `\write` | reuse `Lexer.FirstLine`; TCX from the fmt (data) | existing `FL_*` families |
| C3 | kpathsea lookup (`kpse_find_file` per format: tex, tfm, fd via tex, enc, map, type1, pict), `openin_any=p` / `openout_any=p` paranoid rules, the `ls-R` databases, `mktextfm`/`mktexpk`/`mktextex` triggers | whether `\input`, `\openin`, `\font`, `\pdfximage` find a file, and which one | a function over the FS snapshot (project dir ∪ image texmf tree, content-hashed); **any lookup that would run a `mktex*` script is `Stuck(external_generator)`** | **exhaustive**: every name in the image's `ls-R` plus the project's names, and a generated set of paranoid-rule edge cases (dotfiles, `..`, absolute paths), compared with `kpsewhich` inside the image |
| C4 | `texmf.cnf` sizes and switches (`shell_escape=p`, `openout_any`) | capacity array sizes; `\pdfshellescape`; restricted `\write18` | data read from the image | the log's capacity lines; `\showthe\pdfshellescape` |
| C5 | clock: `get_date_and_time`, `seconds_and_micros`; `SOURCE_DATE_EPOCH`/`FORCE_SOURCE_DATE` | `\time` `\day` `\month` `\year`, `\pdfrandomseed` (F5), `\pdfelapsedtime`, `\pdfcreationdate` (fixed by `SOURCE_DATE_EPOCH=0`) | **abstract inputs** (§5.2): the verdict must hold for every date in a stated window and for every seed | direct |
| C6 | terminal I/O under the oracle (stdin, `interaction`) | `\read16`, `error` in `\errorstopmode` → "cannot `\read` from terminal" / "job aborted" | stdin = empty | probes per interaction command |
| C7 | output files (`open_out`, `\openout`, `\write`, `\closeout`, the log, the `.aux`), stdio buffering | the bytes a *later* `\input` or pass reads | FS state; **reading a file that is currently open for writing in the same run is `Stuck(buffered_io)`**, because what it sees depends on libc buffer sizes | probes |
| C8 | `\write18` (restricted shell escape) | runs `repstopdf`, `kpsewhich`, … and creates files (e.g. `graphicx`/`epstopdf-base` EPS conversion) | **`Stuck(shell)`** whenever a command would be executed | direct |
| C9 | pdfTeX utility C functions: `\pdfstrcmp`, `\pdfescapestring`/`name`/`hex`, `\pdfmdfivesum`, `\pdffilesize`, `\pdffilemoddate` (abstract: modification times are nondeterministic), `\pdffiledump`, `\pdfuniformdeviate`/`\pdfnormaldeviate` (depend on the seed, C5) | token lists and integers | Coq functions (MD5 included) | **exhaustive per function** on generated inputs, via a C test harness linked against the pinned library build (H.1) |
| C10 | images (`\pdfximage`: PNG, JPEG, JBIG2, PDF via the bundled xpdf/poppler) | width, height, depth, page count, box, errors ("reading image file failed", "page does not exist") | **per-file facts** keyed by (content hash, options), each obtained by a probe document run by the real engine; no fact → `Stuck(image)` | the probe is the fact |
| C11 | font embedding at shipout (map file, `.enc`, `.pfb`, subsetting), font expansion (`\pdfadjustspacing`, microtype) | fatal `pdf_error`s ("cannot open Type 1 font file") | **per-font facts** keyed by (tfm, size, expansion parameters, map line hash), obtained by a probe; no fact → `Stuck(font)` | the probe is the fact |
| C12 | PDF byte output (object writing, compression) | none on TeX state; the outcome needs only "pages > 0 and the file was finalised" | not modelled beyond success; the oracle's free-space floor makes disk-full an infrastructure error, not a grade | whole-document differential |

C10 and C11 are the only premises that **grow with input**. They grow per *file* (an image, a font), never per *package* or per *name*, they are keyed by content hash, and each is attested by the real engine on a probe that isolates that file. The design keeps that line on purpose.

---

## 3. (B) Executing the real format

### 3.1 Three options, compared

| option | what runs | trust | cost | verdict |
|---|---|---|---|---|
| **B1: decode the shipped `.fmt`** | the translated `load_fmt_file` (§1303–§1327 + `zlib-fmt.ch` + pdfTeX's extra dumps) over the decompressed bytes of `pdflatex.fmt` | the translation (same as everything else); decompression (zlib, outside Coq), checked by hashing the output of two independent inflaters | milliseconds to seconds, once per pin; the resulting `Store` is snapshotted and reloaded (§7.3) | **recommended** |
| **B2: preload through the model** | INITEX mode of the translated program on `pdflatex.ini` (`pdftexconfig.tex`, `latex.ltx`, the hyphenation patterns of `language.dat`, `expl3-code.tex` (40,266 lines)) | no dump decoding; but it needs the INITEX-only code (primitive installation, `new_patterns`/trie packing §942–§966, `store_fmt_file`) to be correct too, and the result must match a format pdfTeX built at a different time (F7: not byte-reproducible) | pdfTeX needs 14.8 s [M]; the model is 10–100× that, so minutes to half an hour, once per pin | **a one-time cross-check**, not the primary path |
| B3: an algebraic decoder | hand-written | a second model of the dump | — | rejected (§2.3) |

### 3.2 How B1 is attested

1. **Round trip.** `store_fmt_file` is also translated. `store (load bytes)` must reproduce the decompressed bytes exactly. This is the same translation run in reverse; a decoding defect breaks it.
2. **Meaning dump.** From the loaded `Store`, the model prints `\meaning` of every one of the 23,519 kernel names, plus every register, catcode, `\lccode`/`\uccode`/`\sfcode`/`\mathcode`/`\delcode`, and every font parameter. The existing contract generator already produces the same dump from pdfTeX (`meanings_sha256`, F3). The two must be byte-identical.
3. **B2 cross-check, once per pin.** The model's INITEX run of `pdflatex.ini` gives a `Store`. It must equal B1's `Store` modulo an enumerated set of differences, each explained (the dump date and time, `\fmtversion`-independent fields, string-pool order if F7's difference is there). F7 says the byte difference exists; spike H.3 locates it. If it is not *only* a timestamp, it is a finding about format determinism, recorded before anything is built on it.

### 3.3 Classes and packages as data

Every file TeX reads comes from the FS snapshot: the project's files, and the image's texmf tree, both content-hashed. `\documentclass{article}` executes `article.cls` from its bytes. `\usepackage{hyperref}` executes `hyperref.sty` and whatever it loads.

The configuration key, the per-configuration contract, per-name signatures, R-INERT, R-EFFECT's censuses, and the probe budget per configuration all **disappear**. ADR-012 decision 3 (run pdflatex on the preamble) is no longer needed for anything except the C10/C11 file facts.

---

## 4. (C) The decision by execution, and exactly what is proved

### 4.1 Outcomes

```
outcome ::= Compiles (pages : positive)              (* rc 0, "Output written", per the corrected oracle predicate *)
          | Fatal (msg : string) (ctx : context) (line : option nat) (rc : nat)
          | NoPages                                   (* rc 0, "No pages of output." = E0 *)
          | Diverges (why : cycle_witness)            (* exact Store repetition, no byte written in the cycle *)
          | Stuck (why : stuck_reason)
stuck_reason ::= unmodelled_external | ub_overflow | ub_bounds | fuel
               | nondeterministic_branch (input)       (* an abstract input decided a branch, and the paths disagree *)
               | fork_budget | external_generator | shell | buffered_io | image | font
```

- `msg` is the exact text `print_err` produced. A generated total map sends it to the project's E-codes.
- `line` is the `l.N` that `show_context` prints.
- `Diverges` becomes PROVEN-NOT-READY (reason "does not terminate: the oracle times out"), but **only** when the cycle writes nothing: no log line, no `\write`, no page. A loop that writes grows the log until the oracle's free-space floor turns it into an *infrastructure* error, which is not a grade. Such a loop is `Stuck(fuel)`.

### 4.2 The Coq statements

```coq
(* generated, from the pinned source *)
Definition prog : PS.program := (* translator output *).
(* the job: TeX Live start-up, fmt load, \everyjob, the main file, halting *)
Definition Job (E : env) (FS : fsnap) : PS.config := ... .
(* declarative: the reviewed small-step semantics, closed reflexive-transitively *)
Inductive Exec (E : env) : PS.config -> fsnap -> result -> Prop := ... .
(* the oracle protocol, exactly (run_to_fixpoint with the D-1 fix, ADR-013 §1.1) *)
Inductive Protocol (E : env) (FS : fsnap) : outcome -> Prop := ... .

Theorem exec_deterministic : forall E c fs r1 r2, Exec E c fs r1 -> Exec E c fs r2 -> r1 = r2.
Theorem run_sound    : forall E c fs n r, run n E c fs = Some r -> Exec E c fs r.
Theorem run_complete : forall E c fs r, Exec E c fs r -> exists n, run n E c fs = Some r.
Theorem compile_eq_exec : forall s st, compile s st = exec s st.            (* speed layer *)
Theorem abstract_sound :                                                     (* §5.2 *)
  forall E# c# fs n R, run# n E# c# fs = Decided R ->
  forall E, E ∈ γ E# -> forall c, c ∈ γ c# -> exists r, Exec E c fs r /\ r ∈ R.
Theorem diverges_sound : run n E c fs = DivergesW w -> ~ exists r, Exec E c fs r.
Theorem resume_exact :                                                       (* §7.2 checkpoints *)
  forall k edit, valid_checkpoint k edit -> run_from k (apply edit FS) = run (apply edit FS).
Theorem decide_exact : forall E# FS,
  (decide E# FS = ProvenReady            <-> forall E, E ∈ γ E# -> Protocol E FS Compiles) /\
  (decide E# FS = ProvenNotReady m ctx l <-> forall E, E ∈ γ E# -> Protocol E FS (Fatal m ctx l 1))
  (* and the NoPages / Diverges rows *).

(* the one premise about the world: a Definition, pinned like Faithful today (C-87, C-88) *)
Definition FaithfulEngine (oracle : env -> fsnap -> outcome -> Prop) : Prop :=
  forall E FS o, in_env_class E -> (oracle E FS o <-> Protocol E FS o).

Corollary proven_ready_iff_pdflatex : forall oracle E# FS,
  FaithfulEngine oracle ->
  (decide E# FS = ProvenReady <-> forall E, E ∈ γ E# -> oracle E FS Compiles).
Corollary proven_not_ready_pdflatex : ... (* with message and line: the reason and location are now
                                            covered by the premise, which OPEN-121 L-3 said they are not today *)
```

**Scope.** `in_env_class E` is the oracle's environment class: `IMAGE_ENV`, `ORACLE_TEX_VARS`, the protocol flags, the image digest, the architecture, and a date in the stated window. There is **no document restriction**. The tier is "`decide` did not return `Stuck`".

### 4.3 Can `FaithfulEngine` be split per primitive, so that the document-level bridge is a theorem?

**Formally, yes.** Take the real engine as an abstract transition system in Coq:

```coq
Record RealEngine := { RS : Type; rstep : RS -> RS + halt; robs : halt -> outcome }.
Definition FaithfulUnit (X : RealEngine) (R : X.(RS) -> PS.config -> Prop) (u : unit_id) :=
  forall rs c, R rs c -> unit_of c = u -> R_next (X.(rstep) rs) (step c).     (* one lock step *)
Theorem engine_from_units : forall X R,
  (forall u, FaithfulUnit X R u) -> FaithfulInit X R -> FaithfulC X R -> FaithfulPS ->
  FaithfulEngine (oracle_of X).
```

The proof is a routine simulation argument, by induction on the number of steps. The units are the arms of `main_control`'s `big_switch` (by `abs(mode)+cur_cmd`), the arms of `expand` (by `cur_cmd`), and the internal procedures that run between them (`get_next`, `build_page`, `fire_up`, `line_break`, `hpack`/`vpack`, `mlist_to_hlist`, `fin_align`, `ship_out`, `write_out`). That is ≈ 200–300 units.

**Honestly, the decomposition adds no trust on its own.** Its premises quantify over *every* state of an uninterpreted real machine, exactly like `FaithfulEngine`. It rests on two more modelling claims:
- the binary takes steps at the same boundaries (true of web2c's procedure-by-procedure translation, up to inlining that does not change the state at a boundary);
- the correspondence `R` is equality of the translated globals.

What it *buys* is diagnostic power:
- a disagreement is attributed to one unit at one step, not to a whole document;
- attestation can be organised and counted per unit: coverage of every branch of every unit (§6.2);
- `FaithfulEngine`'s attestation becomes a *sum* of per-unit attestations. This is the only honest sense in which "per primitive" works.

**The smallest honest premise is `FaithfulEngine` itself**, stated once per (engine revision, image digest, architecture). The per-unit theorem is offered as the *structure of its attestation*, not as a reduction of it.

**Compared with the existing kernel.**
- Today `Faithful` is about a hand-written relation `Runs`, so it can be false because *we* modelled TeX wrongly (C-83, C-85, C-94, C-98 were exactly that).
- `FaithfulEngine` can be false only for three reasons: the binary does not implement its own source; `PS` or the translator is wrong; or a C-boundary row is wrong.
- The first is testable at every step. The second is generic and small. The third is the enumerated table of §2.5.

### 4.4 What is proved, and what is not (no inflation)

**Proved in Coq, with content:**
- determinism;
- soundness and completeness of the fuelled run against `Exec`;
- the closure compiler;
- **soundness of the abstract interpreter**: the only substantial mathematics, proved once for `PS` and not for TeX;
- `diverges_sound`;
- checkpoint resumption;
- the multi-pass protocol;
- the E-code map is total.

**Proved but close to definitional:** `decide_exact`. The decider *is* the execution. Its content is that the optimisations (checkpoints, fork/merge, cycle detection, closure compilation) do not change the answer.

**Not proved, and never provable:** that the model is pdfTeX. That is `FaithfulEngine`.

**Not proved, and optional later:** invariants of the program itself: "`confusion` is unreachable from a well-formed `Store`", "no index leaves its bounds". These would turn `Stuck(ub_*)` into provably dead code. They are research, and nothing depends on them, because the runtime checks already make them sound.

An adversarial reader will say the theorem is thin, and should. The owner's "provably declare" then means: **proved relative to one fixed premise about one fixed program, attested at every step.** It no longer means "proved relative to a model we wrote", nor "relative to per-package premises that grow" (§10).

### 4.5 The protocol and passes, by construction

- The model threads the file-system state between passes exactly as `_oracle.run_to_fixpoint` does: up to 3 passes to the first success, then a confirming pass.
- It uses the D-1-corrected predicate: the PDF is deleted before each pass, or "Output written" is required in the last log. See ADR-013 §1.1. The oracle must be fixed first, whichever architecture is chosen.
- The `.aux`, `.toc`, `.out`, `.lof` bytes are written by the translated `write_out` under the fmt's TCX printable table, and re-read by the translated tokenizer.

So `\label` → `\ref` across passes, the 27th `enumii` label that `\ref` makes fatal on a later pass, and the oscillating Q1 of ADR-013 are all *executed*, not reasoned about. ADR-013's `aux_independent_fatal` is not needed as a lemma; the passes are simply run.

---

## 5. (D) Layout

### 5.1 Under translation, layout is exact, with one exception

All of TeX's layout is integer arithmetic in sp: packaging, badness, Knuth–Plass with fixed-point demerits, hyphenation, the page builder's `page_goal`/`page_total`/insert costs, and math typesetting from TFM parameters. The inputs are exact data:
- TFM files from the image (read by the translated `read_font_info`, §560–§575);
- the hyphenation trie in the fmt;
- the registers.

pdfTeX's font expansion and protrusion (microtype) use integer scaling [R: pdfTeX's expansion code; to be re-read in H].

**The exception is `glue_ratio`, a C `double` (F4).** It is computed in `hpack`/`vpack` and read back only at shipout (`hlist_out`/`vlist_out`: glue positions). It therefore reaches TeX state only through `\pdfsavepos` → `\pdflastxpos`/`\pdflastypos`. Using IEEE binary64 in `PS` makes it exact *if* the binary evaluates exactly as written.

Two risks, both recorded as [U] and measured in H:
- the compiler contracting `a*b+c` into a fused multiply-add on arm64 (GCC's default in GNU C mode);
- the pinned arm64 and amd64 binaries differing.

**Mitigation, independent of the answer:** `\pdflastxpos`/`\pdflastypos` return an abstract interval of ±k sp, where k is the number of glue items on the line. Positions are then abstract inputs (§5.2), exact where they do not decide a branch.

So in this architecture the layout abstraction the task asks for is **not needed for correctness**. It remains useful in two ways:
- the abstract domain is mandatory for nondeterministic inputs (§5.2);
- a layout abstraction is a *staging device* only if the owner rejects translation (§5.3).

### 5.2 The abstract domain (mandatory, for nondeterministic inputs)

F5 and F6 make these inputs genuinely nondeterministic under the oracle: `\time`, `\day`, `\month`, `\year` (real clock), `\pdfrandomseed` (clock), `\pdfelapsedtime`, `\pdffilemoddate`, positions (§5.1). Any `\maketitle` with no `\date` typesets `\today`. A verdict computed with today's date would be a verdict about today, not about the document, so the design **quantifies over them**.

**Domain.**
- Integers are `Exact z | Range lo hi | Top`.
- Characters are `Exact c | Set S` (a digit of an abstract number is `Set {0..9}` restricted by the range).
- Everything else is concrete.
- Arithmetic is interval arithmetic. Anything that could overflow is `Stuck(ub_overflow)`.

**Concretisation points.** The program needs a *concrete* value when it:
- indexes an array (a character code into `eqtb`, a `\csname` from abstract digits);
- branches (`if`, `case`, a `\ifnum` on `\day`);
- chooses a font glyph.

At such a point, the value is **forked** over its finitely many possibilities when the set is small (≤ `K`, default 64), else the run is `Stuck(nondeterministic_branch)`. A branch whose comparison is decided by the interval does not fork.

**Merge.** Paths are kept in a set keyed by a hash of the whole `Store` (plus the FS state and output so far). Two paths whose states are equal are merged.

In practice the `\today` fork (12 month names in `\ifcase\month`, abstract digits for the day) produces title boxes of different *widths* but equal heights and depths, because every month name starts with a capital and every date has a comma, so height and depth are equal [I]. The paths therefore make the same page break and become equal after page 1 ships out. The cost is ≤ 12× on page 1 only. When the paths do not reconverge within the fork budget `B` (default 256 live paths), the run is `Stuck(fork_budget)`.

**Decision rule** (the one the task states, made precise):
- PROVEN-READY iff every path ends in `Compiles`;
- PROVEN-NOT-READY(m, l) iff every path ends in `Fatal m _ l` with the same message and line. The simplest case is a failure *before* the first fork, which is common (preamble errors);
- if paths end differently, the document genuinely depends on the date or seed. The verdict is `Stuck(nondeterministic_branch)`, with the witness (for example "fails on days > 28"). That witness is useful to the author.

**Soundness.** `abstract_sound` (§4.2) is proved **once for `PS`**: each primitive operation on the domain over-approximates its concrete counterpart, forks cover every concretisation, and merging is by equality. It is a standard collecting-semantics proof for a small imperative language. It does not mention TeX.

`d1.tex` (`\ifnum\day>40 \zzundef\fi`) is decided READY because the range [1, 31] decides the comparison [M: compiles today; the design predicts it compiles on every day]. `\ifnum\day>28 \zzundef\fi` is `Stuck(nondeterministic_branch: day ∈ 29..31 → Undefined control sequence)`.

**Owner decision O-5 (§12).** Quantify over dates (recommended), or change the oracle to `FORCE_SOURCE_DATE=1` and make every claim "under the fixed date". The latter is simpler and exact, but it is a claim about a compile nobody runs.

### 5.3 If the owner rejects translation: the layout abstraction as a staging device, and why it decides almost nothing

Suppose the semantics is transcribed by hand, in stages, and the layout procedures (line breaking, math typesetting, the page builder) come last. Until they exist, their results are `Top`:
- paragraph heights;
- hence `page_total`;
- hence *whether `build_page` fires the output routine at each contribution*.

**Every contribution to the main vertical list then becomes a fork:** "break here or not". The number of paths is the number of ways to cut the document into pages, which is exponential. Merging does not help, because the output routine's state (`\c@page`, marks, the delayed `\write`s it executes, and `\@freelist`) differs between cuts.

A sound shortcut exists only when an **upper bound** on the total height proves that no break is possible. A body of n characters makes at most n lines, and each line has a bounded height, so the bound is n · (max line height + `\baselineskip` excess). If that stays under `\textheight`, the document fits on one page. That covers the short evidence documents of `L_S0`, and no real paper.

**Honest estimate under the abstraction alone** [I, but structural]:
- **PROVEN-READY: ≈ 0 real papers.** Every real paper is multi-page (F12: 12 pages is the synthetic median-ish case), and `\maketitle` alone runs the output routine.
- **PROVEN-NOT-READY: exactly the papers whose first error comes before the first page-break decision.** In practice that means preamble errors (missing `.sty` → "File … not found", option clashes, load-order fatals such as cleveref before hyperref) and errors in the first paragraphs. The fraction of the frame that fails in the preamble is not measured here [U]; the oracle grades of the frame give it in one query.

The staged path to exact layout under hand transcription runs as follows. Each stage is exact, integer, and read from tex.web:
1. TFM loading and the main loop's ligature/kern program (§1034–§1040). This is already needed for any character, because ligatures change the list.
2. `hpack`/`vpack`.
3. `line_break` + hyphenation. The hyphenation trie is data from the fmt.
4. `mlist_to_hlist`.
5. The page builder and `fire_up`.
6. Alignment, and pdfTeX's expansion and protrusion.

Only after stage 5 does the READY count leave zero. This is the strongest argument *for* translation: a staged hand transcription pays for almost all of tex.web before its first real paper anyway, and pays again in modelling risk.

---

## 6. (E) The trusted base, and how each part is attested

### 6.1 Enumeration

| id | trusted component | fixed or growing | attestation |
|---|---|---|---|
| TB-1 | Coq kernel, extraction to OCaml, OCaml runtime (including `PArray`, `PrimFloat`, `Int63`) | fixed | as today; `Print Assumptions` Closed |
| TB-2 | **the source pin**: the TeX Live source revision whose tangled `pdftex.p` is translated, the `tie` change-file list (F1), `tangle` | fixed per engine revision | the reference build from that source must reproduce the pinned binary's logs and PDFs byte-identically (modulo recorded timestamps) on the corpus (H.1) |
| TB-3 | **the translator** (Pascal subset → `PS` AST) | fixed, generic | review of ≈ 40 rules; translation validation: re-emit C from the AST and diff against web2c's C statement by statement (a second path through the same code); step-level co-simulation (6.2) |
| TB-4 | **`PS` semantics**: integer width, `div`/`mod`, `round` = `zround`, `double`, union layout, externals as boundary calls | fixed, generic | review against web2c's `convert` rules and the C headers (`texmfmem.h`); per-construct differential via a C harness |
| TB-5 | **C-boundary models** C1–C12 (§2.5) | fixed per engine revision, except C10/C11 | exhaustive or generated per function (6.3) |
| TB-6 | **file facts** C10 (images), C11 (fonts) | **grows per file**, keyed by content hash | one real-engine probe per fact |
| TB-7 | fmt decompression (zlib, outside Coq) and the FS snapshot hashing | fixed | two independent inflaters must agree; content hashes |
| TB-8 | **the nondeterminism inventory**: the list of inputs treated as abstract (C5, C9's `\pdffilemoddate`, positions) is complete | fixed per revision | a grep of every external in `.defines` that reads the clock, the environment or the file metadata, reviewed; a double run of the corpus under two clocks and two seeds must give identical traces except at the listed inputs |
| TB-9 | **P-time**: a run that `decide` completes within its step budget finishes within the oracle's 300 s per pass | fixed | measured steps per second of the pinned binary on the oracle hardware, with a margin ≥ 10×; runs beyond the budget are `Stuck(fuel)` |
| TB-10 | the oracle protocol and its predicate (D-1 fixed), the renderer, the verdict type | as today | as today |
| TB-11 | `FaithfulEngine` (the premise) | fixed per (revision, digest, arch) | everything above, plus the whole-document differential as a *check* |

**Removed from ADR-012's trusted base:**
- the contract generator's behavioural parts (signatures, the closed world as a proof input);
- the per-configuration contract store;
- R-INERT, and any static analyser.

**Kept:** the oracle, since it now attests C10/C11 and TB-2.

### 6.2 Attestation of the engine: co-simulation at every step, and branch-complete generation

1. **The reference build.** Build pdfTeX from the pinned source in a container. Show it equals the pinned binary on the corpus: logs, `.aux` bytes and page counts identical, the PDF identical modulo `/ID` and dates.
2. **The co-simulation build.** Add one change file to the reference build. After every `big_switch` iteration of `main_control` (and after every `expand`, if finer diagnosis is needed), it writes a digest of every translated global, with incremental hashing of `mem`/`eqtb` by dirty ranges.
   - The model computes the same digests. **The first differing step names the unit and the document.**
   - The instrumented build is itself checked against the reference build on outputs, so the probe cannot mask a divergence.
3. **Coverage-directed generation.** The model's closure compiler records which branch of every statement ran. The target is **every reachable branch of every unit covered by a co-simulated document**.
   - Uncovered branches are driven by generated documents. The model itself searches (symbolic execution over the *model* is allowed; it only proposes inputs, and the real engine grades them).
   - A branch shown unreachable gets a recorded reason, and later a Coq invariant.
   - This is the "exhaustive per primitive" generator the task asks for. It replaces "one probe per construct × failure mode" (today's `Runs` families) with "every branch of the real program, in lock-step".
4. **Corpora**, co-simulated in full, every step compared:
   - all existing graded evidence (L_S0 rule probes 510 + 680, differentials 4,000 + 3,000 + 3,500, byte probes 2,167 + 2,847, ADR-013's measured documents);
   - the unsealed frame (1,119 roots, every pass);
   - the owner's composition cases (§11).
5. **Whole-document differential.** It stays release-blocking, but it is a **check, never the argument**: a step-level agreement subsumes it.

### 6.3 Attestation of the C boundary

This is where C-89 and C-91 lived, so each row gets an exhaustive or generated test against the *real* C code, not against pdflatex runs alone:
- **C1/C2:** reuse the existing byte-level families, plus generated CR/LF/space/`%&` patterns.
- **C3:** every file name in the image's `ls-R`, for every kpathsea format the program uses, compared with `kpsewhich -format=…` inside the image; the paranoid-rule edge cases; the project directory's names. Exhaustive over the image.
- **C9:** a C harness links the pinned library build and calls `\pdfstrcmp`'s, MD5's and escape functions' C code directly on generated byte strings; the Coq functions must agree. Exhaustive over lengths 0–3, random beyond that.
- **C4/C6/C7/C8:** direct probes, one per switch and interaction command.
- **C10/C11:** the fact *is* a probe by the real engine.
- **C5:** the double-clock run of TB-8.

### 6.4 Honest comparison with R-EFFECT's P-1 to P-4

| R-EFFECT premise | what it becomes here |
|---|---|
| **P-1**: completeness of a static analyser of Turing-complete macro code (the one C-92 and C-96 broke) | **gone**: no analysis; the code runs |
| **P-2**: implicit engine reads reduce to a generated table of engine error sites; layout sites behind side conditions | **gone**: the engine's reads are the engine's code; layout is exact |
| **P-3**: determinism and no hidden state (tracer calibration) | **TB-8**: the nondeterminism inventory, stated over a finite list of externals, and checked by a double-clock run |
| **P-4**: one representative per cell, for arguments | **gone**: every argument is executed |
| `Faithful` over a hand-written `Runs` | `FaithfulEngine` over pdfTeX's own program |
| per-configuration contracts, per-name programs, footprint cache | **gone** |
| — | **new**: TB-2 (source pin), TB-3 (translator), TB-4 (`PS`), TB-5 (C boundary), TB-6 (file facts), TB-9 (time) |

**By code size**, the interpreter's trusted base is *larger*: a whole engine translation plus about 30 boundary functions, against R-EFFECT's analyser plus per-name programs.

**By structure**, it is smaller and closed:
- nothing grows with packages, names, configurations or LaTeX releases;
- the only growth is per image or font file, and each such fact is a real-engine measurement.

**By failure history**, every correction that stopped the per-name track (C-83..C-98) is in a class this design does not have. The class it keeps (the C boundary) produced C-89 and C-91, and the design treats it accordingly.

---

## 7. (F) Performance and real time

### 7.1 Estimate, and the measurement that settles it

- pdfTeX spends ≈ 0.4 s interpreting the 12-page synthetic paper per pass [M, F8 minus start-up]. That covers ≈ 335k expansions and ≈ 200k conditionals, plus typesetting and PDF writing (F9).
- The model is an interpreter (the extracted closure compiler) *of* an interpreter (pdfTeX's `main_control`):
  - persistent-array access in OCaml is ≈ 2–4× a C array access;
  - tagged `Int63` arithmetic is ≈ 1.5×;
  - closure dispatch per statement is ≈ 3–10×;
  - memory words stored as two halves add ≈ 1.5×.
- **Estimate: 10–60× pdfTeX** [I]. That is ≈ 4–25 s per pass for this paper, and 10–75 s for a full protocol run (2–4 passes), cold, without checkpoints. Nondeterministic forks add ≤ 12× on page 1 only.
- NTS (a 1990s Java reimplementation of TeX) is the cautionary precedent for "much slower". `web2js` (a mechanical translation) is the encouraging one [R: both public; the speeds are recalled, not measured here, so they are [U]].
- **Spike H.5 measures this.** The go/no-go line is ≤ 60× on the synthetic paper and on a 40-page corpus paper.

### 7.2 Checkpoints and incrementality

- **Format load.** The `Store` after B1 is marshalled once per pin. Start-up is an unmarshal (≈ 100–300 ms for ≈ 100 MB [I]). Only the pages of `mem` that are touched are materialised, thanks to persistence.
- **Preamble checkpoint.** A snapshot is taken just *before* `\begin{document}` reads the `.aux`, keyed by (preamble bytes, the files read so far, the env class). A body-only edit resumes from it, which saves ≈ 3/4 of the work (F9).
- **Page checkpoints.** A snapshot is taken after each `ship_out`, with `max_read_offset` per file: the last byte the tokenizer has read, which is the end of the current *line*, since `input_line` reads whole lines. The rule is `resume_exact` (§4.2): a checkpoint is valid for an edit iff every file byte at or after the edit offset is unread at the checkpoint, and no file written since then is read later in the same pass (C7).
- **Passes.** Pass 2 reuses the preamble checkpoint, since the `.aux` is read after it. The body is re-run.
- **Edit latency.** An edit on page k of N re-runs pages k..N plus any passes whose `.aux` changed. That is ≈ (N−k)/N of body time per pass, i.e. **seconds, not milliseconds**.

### 7.3 Real time, and where the Turing-free subset still matters

- The interpreter cannot promise a keystroke budget. TeX is Turing-complete, and even a terminating document can take long.
- **PROVEN verdicts are asynchronous.** The heuristic tier serves keystrokes, as the design's D.3 already says.
- **Fuel** bounds every run (TB-9), so a run always ends in a verdict or `Stuck(fuel)`.
- **The existing `L_S0` kernel keeps one job:** it is the only component with a *proven linear-time* bound (its decider is a fold). It remains the synchronous fast path for the documents it covers, and a regression oracle (§8.3). Its verdicts are cross-checked against the interpreter's on every covered document.

---

## 8. (G) Staging, payoff per stage, and what `proofs/Strict` becomes

### 8.1 Stages

Every stage is exact: nothing is decided that the stage cannot decide. Effort is in agent-weeks [I], for one focused track.

| stage | deliverable | exactness gate | payoff on the unsealed frame (1,119) |
|---|---|---|---|
| **G0** spike (§9) | go/no-go | H's criteria | 0 |
| **G1** source pin + reference build + translator + `PS` + closure compiler | the whole tangled pdfTeX as a Coq AST; extraction | translation validation (C re-emission diff), reference build = pinned binary on the corpus | 0 |
| **G2** C boundary C1–C9, C12 | boundary models with relational specs | §6.3 tests | 0 |
| **G3** B1 format load | `Store` of `pdflatex.fmt`, snapshot | round trip; 23,519-name meaning dump identical; B2 cross-check | 0 |
| **G4** end to end, TeX side of shipout; C10/C11 as `Stuck` | `decide` over the full protocol; co-simulation build | step-level agreement on all existing evidence (≈ 16k documents) and the frame; **0 disagreements** | **first real papers**. Decided = papers without images whose fonts are all attested, plus every paper whose first error comes before the first `Stuck` (preamble failures are decided NOT-READY). Estimate **20–40 %** [I] |
| **G5** C10/C11 file facts (probe service, cache by hash) | images and fonts | fact probes | **60–90 %** [I]. The remaining `Stuck`: restricted shell escape (EPS conversion), `mktex*` fonts, forks that do not merge, unmodelled externals |
| **G6** abstract inputs (§5.2) | date/seed/position quantification | `abstract_sound` proved; double-clock run | converts `Stuck(date)` into verdicts. Note: **without G6 every paper that typesets `\today` is `Stuck`**, so G6 moves into G4 unless the owner picks O-5(b) |
| **G7** checkpoints, incrementality, `L_S0` fast path wiring | CLI `--require-proof` | `resume_exact` | latency, not coverage |
| **G8** sample 3 | the North Star on the virgin sample | 0 `strict_wrong` | the published number |

**Honest reading.**
- G1–G3 are infrastructure with **zero** payoff. That matches ADR-013's S3.0–S3.5.
- The difference is what follows. G4–G5 do not *add names*, they *finish the engine*. If the engine is right, most of the frame is decided at once.
- If the engine is wrong somewhere, co-simulation finds the step before any verdict is published.

**Effort.**
- G1: 6–12 agent-weeks. The translator is the critical path, and its risk is the size of the Coq term, not the concept.
- G2: 4–8.
- G3: 2–4.
- G4: 6–10, dominated by triage of co-simulation divergences.
- G5: 3–6.
- G6: 3–6.
- G7: 3–5.
- **Total ≈ 27–51 agent-weeks** before sample 3 [I, wide].

Time to the first real paper is **≈ 18–34 agent-weeks** (end of G4, with G6's date handling pulled in). ADR-013 reaches its first real papers at S3.6 after five zero-payoff milestones. That is plausibly similar calendar time, for "low single digits" of papers.

### 8.2 What the first real paper needs (the task's checklist, answered)

Expansion, the stomach, the format load, the output routine, fonts and TFM, and every primitive the common packages use. **All of it comes with G1**, because the whole program is translated.

The remaining needs are the date (G6 or O-5(b)) and, for most papers, images (G5). There is no "common packages' primitives" item, because packages are data.

### 8.3 What the existing kernel becomes

- **`Lexer.v` (the line and first-line models)** becomes C1/C2 of the boundary, unchanged. It is the one part of the kernel that models the C side rather than TeX, and it is already proved and attested. A further proof is feasible and worth doing: under `L_S0`'s fixed catcodes, the translated `get_next` over `Lexer.v`'s lines yields `Lexer.v`'s tokens. That proof relates two Coq objects and needs no new premise.
- **`Syntax`/`Semantics`/`Decide`/`Bridge` (`Runs`)** become the synchronous fast path and a regression oracle. On every `L_S0` document, `decide_S0` must equal the interpreter's verdict. Any disagreement is a defect in one of them, and the interpreter co-simulates, so the fault can be located. Their `Faithful` premise could then be retired in favour of "`decide_S0` agrees with the interpreter on the fragment". That is testable, not proved: proving it means symbolic execution of `latex.ltx` code in Coq, which is out of scope.
- **Signature generators, R-INERT, slices B–D of step 2:** frozen. No further per-name admission work. OPEN-122 is closed as superseded if this ADR is adopted.
- **The evidence corpora (≈ 16k graded documents)** become the interpreter's first co-simulation suite. That is their best use.

---

## 9. (H) Feasibility spike (≈ 2 weeks of agent work; specified, not executed)

**Question.** Can the whole pinned pdfTeX be mechanically translated into Coq, load the real `pdflatex.fmt`, and agree step by step with the real engine on the existing evidence, at a usable speed?

| step | days | work | pass criterion | kills the approach if |
|---|---|---|---|---|
| H.1 | 1–2 | Fetch the TeX Live 2026 source at the revision of the image's binaries (match `pdftex --version`, the `pdftex.web` banner, and the release tag). Build pdfTeX in a Debian container with the TL build scripts. Confirm `INTEGER_TYPE`, `GLUERATIO_TYPE`, `-ffp-contract`. | the reference build's logs and `.aux` equal the pinned binary's on 200 corpus documents (PDF modulo `/ID`) | the revision cannot be identified, **and** no revision reproduces the logs. Fallback: pin the reference build as the new oracle (an ADR-012 decision-7 change) |
| H.2 | 3–6 | The translator for the Pascal subset (web2c's grammar as a guide) → a Coq AST; `PS` as a fuelled interpreter; closure compiler; extraction. Externals stubbed where not needed: C1 from `Lexer.v`, C3 as a precomputed `kpsewhich` map, C5 fixed date (spike only), C12 no-op | 100 % of procedures translated; Coq accepts the term; the extracted binary runs INITEX to the `*` prompt | the Coq term or its extraction is intractable (> 2 h compile or > 16 GB). Fallback: split the program into per-part modules, or emit a shallow embedding with a generated reflection lemma |
| H.3 | 7–8 | B1: decompress and load `pdflatex.fmt`; round-trip `store_fmt_file`; dump the meanings of the 23,519 kernel names; locate F7's byte difference | round trip byte-exact; meanings byte-identical to the contract generator's; F7 explained | the load cannot be made exact within the spike |
| H.4 | 9–11 | Run all L_S0 evidence (rule probes, the 4,000 + 3,000 differentials, the byte probes) and ADR-013's ≈ 50 measured documents, plus the owner's composition cases (§11 rows 1–6), through the model | verdict, message and `l.N` agree with the recorded oracle grades on 100 %, or every disagreement is traced to a stubbed external | disagreements traced to the *translated* code keep appearing after 3 fixes: the translator or `PS` is wrong in a way that is not converging |
| H.5 | 12 | Speed: the one-line document, the 12-page synthetic paper, a 40-page corpus paper; cold and from a preamble snapshot | ≤ 60× pdfTeX per pass | > 200× with no profile-guided fix in sight. Fallback: a verified-refinement fast interpreter becomes its own project |
| H.6 | 13–14 | Co-simulation prototype: a digest change file in the reference build; step-by-step comparison on 20 documents, including one that fails in the output routine | the first divergence (if any) is localised to a unit automatically | the digest cannot be made to match on a *correct* model (hidden C state not in the translated globals) |

**Deliverables.** The numbers of H.1–H.6, a list of every stubbed external a real paper would reach (from H.4's corpus run), and a revised effort estimate for G1–G7.

---

## 10. (I) Head to head, adversarially

### 10.1 Table

"A0" is the architecture neither draft proposes, and which the owner must weigh: **run the pinned pdflatex on the whole document** (the oracle itself), which ADR-012 decision 3 forbids.

| criterion | **A0: run the pinned pdflatex on the body** | **R-EFFECT (ADR-013)** | **Verified interpreter (this ADR)** |
|---|---|---|---|
| exactness / soundness | exact **by definition** for that run; one date, one seed | exact relative to `Faithful` + P-1..P-4; per-name holes found by four review rounds so far | exact relative to `FaithfulEngine` (one fixed premise); quantifies over dates and seeds |
| trusted base | the oracle | Coq + generic `Eff` machine + `Σ#` + analyser (P-1) + tracer calibration (P-3) + per-name programs + the contract store | Coq + translator + `PS` + ≈ 30 boundary functions + the source pin + file facts |
| grows per package? | no | **yes**: every package's names need programs, footprints and probes; hyperref "last" | **no**; only per image or font file, content-keyed, real-engine-attested |
| coverage trajectory | 100 % of documents (it is a compile) | ≤ 4 bodies before S3.6; "low single digits" at S3.6; ≤ 360 with every other package; ≤ 1,098 with every environment [census bounds] | 0 until G4; then 20–40 % (G4), 60–90 % (G5–G6) [I] |
| time to first real paper | now | S3.0–S3.6: five zero-payoff milestones | G1–G4 (+G6): ≈ 18–34 agent-weeks [I] |
| total effort to a stable tier | ~0 | open-ended: scales with packages × names × cells | ≈ 27–51 agent-weeks, then maintenance per engine release |
| durability | perfect | low: LaTeX releases twice a year, and package updates change footprints | high: `pdftex.web` changes rarely; format and packages are data |
| risk of a wrong PROVEN | none beyond the oracle's own (D-1) | many *independent* holes, each needing a new instrument (the history C-83..C-98) | **correlated**: one translator or boundary defect could affect many documents at once, but step-level co-simulation on every corpus document is designed to catch exactly that before publication |
| maintenance on a TeX Live update | none | re-attest everything that changed (kernel, packages) | re-translate and re-co-simulate if pdfTeX changed; nothing if only macros changed; file facts recomputed per new image |
| speed (cold / edit) | ≈ 1–3 s / 1–3 s | 10–45 min cold per new preamble; fast after | ≈ 10–75 s cold; seconds per edit [I; H.5] |
| per-document explanation | the log | the attested cell, the program | the exact trace, and for nondeterministic cases the witness ("fails for day > 28") |

### 10.2 Adversarial toward the interpreter

1. **The thin-theorem objection is correct.** Coq proves that the optimised execution equals the reference execution, and that the abstraction is sound. It cannot prove that the reference execution is pdfTeX. Everything that makes the verdict *true* is empirical: co-simulation and boundary tests. **Answer:** that was already true of `Faithful`. The change is *what* the empirical premise is about: our model of TeX before, TeX's own program now.
2. **All-or-nothing.** If G1 stalls (the translator, the Coq term size, extraction speed), there is **no partial payoff**: no subset of real papers is decided by 60 % of an engine. The spike exists to find this out in two weeks rather than in six months.
3. **Correlated failure.** A single wrong translation rule, such as `div` on negative numbers, or a union-field layout, could make *many* documents wrong at once. The mitigation (co-simulation of every step on every corpus document, plus branch-complete generation) is strong, but it is also the most complex attestation this project would have built. Its own adversarial pass comes first (C-30).
4. **Speed may be fatal for the product.** At 60× a 40-page paper takes minutes. If H.5 shows > 200×, the design needs a second, faster, *proved-equivalent* interpreter. That is a CompCert-sized proof effort, and at that point the plan is no longer credible within this project.
5. **Is layout ever Stuck forever?** Not under translation. Layout is exact integer code. The float caveat is bounded, and becomes abstract where it matters. Under hand transcription, yes: until the page builder is exact, no multi-page paper is PROVEN-READY (§5.3).
6. **Can the `.fmt` be soundly imported?** Yes, through the program's own `load_fmt_file`, with a byte-exact round trip and a 23,519-name meaning comparison. It is not byte-reproducible from sources (F7), and that must be explained (H.3) before anything rests on it.
7. **The C boundary is where this project has actually been burned** (C-89, C-91). It is small but not trivial. C3 (kpathsea) and C10/C11 (images, fonts) are the rows most likely to hide a defect.

### 10.3 Adversarial toward the question itself (decision O-1)

The interpreter's verdict is, epistemically, "a program proven to execute pdfTeX's code said so". A0's verdict is "pdfTeX said so". A0 is exact, available today, and ≈ 30× faster. The interpreter beats A0 on five things only:
1. it runs without a TeX engine: it still needs the image's *data files*;
2. its verdicts are universally quantified over dates and seeds, where A0 sees one run;
3. it resumes from checkpoints;
4. it gives explanations and witnesses;
5. it complies with ADR-012 decision 3.

If decision 3 exists to keep the checker's *answer* a proof and not a compile, the interpreter satisfies it only in form, because it does compile, inside Coq. If decision 3 exists for footprint, latency or sandboxing (no engine, no shell escape, no disk writes on the user's machine), the interpreter satisfies it in substance. **The owner should state which, before choosing between the two drafts** (O-1).

### 10.4 Adversarial toward R-EFFECT (as the other draft's own self-critique already partly does)

- P-1 (a complete static analyser of TeX macro code) is the premise the history keeps breaking. C-92 and C-96 were found only *after* publication, and ADR-013's D-2 and D-3 found two more defects while drafting.
- Its payoff is bounded by per-package work. Its own census gives ≤ 360 bodies *after* admitting every other package's names, which is itself unbounded work.
- Its per-configuration cost (10–45 min) is paid per paper.
- The owner stopped the per-name track after four review rounds found composition holes each time. R-EFFECT is that track made principled: static censuses plus a global R∩W closure. Whether principled means *closed* is exactly P-1.

**What R-EFFECT does better:**
- it yields a (small) number sooner, on the existing kernel;
- its proofs (`aux_independent_fatal`, the `Eff` interpreter) have more mathematical content;
- its worst case is "few papers", never "a systematic wrong verdict across the corpus".

---

## 11. Self-critique: counterexample attempts against this design

Each row tries to build a document on which the interpreter would give a wrong PROVEN verdict, or on which an abstraction is unsound. "Outcome" says whether the attack succeeds against the design as written, and what the design changed because of it.

| # | attack | source | outcome |
|---|---|---|---|
| 1 | `$$z $\empty $$$$$`: a display `$` whose follower expands to nothing | C-85 | **fails**: §1197's `get_x_token` is executed, not modelled |
| 2 | `\mbox{$` ×128 `x` `$}` ×128: 256 save levels under 128 braces | C-94 | **fails**: `new_save_level` §274 checks `cur_level = max_quarterword` in the translated code; the limit comes from the same constant |
| 3 | 197 `\mbox` levels around 6,427 `\frame{}`: main memory = depth × tokens | C-98 | **fails**: same `mem` array, same size from `texmf.cnf` (C4), same `get_node`/`get_avail` (§120, §125). **Residual:** the size must be read as the binary reads it. A wrong C4 would shift the overflow point. Attested by the capacity line of every oracle log (F9 prints `5000000`) |
| 4 | `x \section{a}\par\unskip x` | owner's case, F11 | **fails**: `delete_last` §1105 + `build_page` §996 (`last_glue`) execute; the model reproduces l.3 [the mechanism is confirmed by F11's two compiling controls] |
| 5 | `\label` inside the 27th `enumii`, `\ref` to it on a later pass | owner's case | **fails**: passes are executed with the real `.aux` bytes (TCX-printable `write_out`), the protocol exactly; the `\@alph` `\ifcase` runs in whichever pass reaches it |
| 6 | Q1: `\expandafter\ifx\csname r@a\endcsname\relax x\fi\label{a}` oscillates, and the oracle's stale PDF says READY | ADR-013 D-1 | **succeeds against the oracle, not the model**. The model mirrors *the predicate `Faithful` names*. If the oracle is not fixed, the model must mirror the stale-PDF quirk to be "faithful". **Design change:** D-1 is a prerequisite (O-6) |
| 7 | `%&latex` on the first line | C-89 | **fails** only because C2 reuses `Lexer.FirstLine`. **This is the kind of boundary item a fresh model would miss again:** rows C1–C12 exist for that reason |
| 8 | the host exports `openout_any=a`, or `-cnf-line=…` | C-91 | **fails**: the environment is an *input* of `in_env_class` (the oracle's allow-listed `IMAGE_ENV`), so a document is judged only under that class. **Residual:** a user who compiles under another environment is outside the claim, as today |
| 9 | `\ifnum\day>28 \zzundef\fi`: correct today, wrong on the 29th | F6 | **would succeed** if the date were taken from the grading run. **Design change:** abstract dates (§5.2) make it `Stuck(nondeterministic_branch)` with a witness; `\ifnum\day>40` is decided READY |
| 10 | `\pdfsavepos` then `\ifdim\pdflastxpos>…` on a line whose glue is stretched: FMA on arm64 differs from amd64 by 1 sp | F4, §5.1 | **possible** [U]. **Design change:** positions are abstract intervals ±k sp; an undecided branch forks or is `Stuck`. H.1 measures `-ffp-contract` and whether any cross-arch difference exists |
| 11 | `\immediate\openout\f=x.tex \immediate\write\f{…}` then `\input x` without `\closeout` | C7 | **would succeed** (libc buffering decides what `\input` sees). **Design change:** reading a file open for writing is `Stuck(buffered_io)` |
| 12 | `\def\a{\a}\a` | fuel | **fails**: exact state repetition with no output is `Diverges`, i.e. PROVEN-NOT-READY (the oracle times out). **Sub-attack:** `\loop\message{x}\repeat` writes the log, so the state never repeats and the disk fills → the oracle reports an infrastructure error, not a grade. The design returns `Stuck(fuel)` there, **not** NOT-READY. Correct |
| 13 | a document that compiles in 400 s (heavy TikZ) | TB-9 | **would succeed** if fuel were unbounded (the model says READY, the oracle times out). **Design change:** the step budget is calibrated to ≤ 30 s of the pinned binary with a ≥ 10× margin (TB-9). The premise is named |
| 14 | `graphicx` with `fig.eps`: `epstopdf-base` runs `repstopdf` via restricted `\write18` | C8 | **fails**: `Stuck(shell)`. A coverage cost, not a soundness hole. **Owner option:** run the oracle with `-no-shell-escape`, which turns it into an exact NOT-READY |
| 15 | a font missing its TFM, so kpathsea runs `mktextfm` in the oracle container | C3 | **fails**: any lookup that would trigger `mktex*` is `Stuck(external_generator)`. **Residual:** the list of such triggers is part of C3's exhaustive test |
| 16 | `\pdfuniformdeviate` in a package's load code, used in a branch (random placement) | F5 | **fails**: the seed is abstract. Arithmetic on it is `Top`, and a branch on it forks (small range) or is `Stuck` |
| 17 | `\input{../secret}` or `\openin` of a dotfile under `openin_any=p` | C3 | **fails** if C3's paranoid rules are right; they are in the exhaustive test set |
| 18 | a document whose aux write bytes contain 0xE9: with `cp227.tcx` it is printable, so it is written raw; `\pdfmdfivesum` of the `.aux` in `rerunfilecheck` then branches | F10 | **fails**: the TCX tables come from the fmt, and MD5 is a C9 function tested exhaustively on short inputs and randomly beyond |
| 19 | a `.fmt` whose rebuilt state differs from the shipped one in more than a timestamp | F7 | **not settled**. Under B1 it does not matter (the *shipped* fmt is loaded), but a difference beyond timestamps would mean the format build is nondeterministic, which is a fact the project should know. H.3 |
| 20 | a translation defect in a rarely used unit (`\vsplit` of an insertion with `\splittopskip`), not exercised by any corpus document | TB-3 | **could succeed on a future document**: co-simulation only checks executed steps. **Design change:** branch-complete generation (§6.2 item 3) is a release gate. Every reachable branch must be covered or proved unreachable. This is the residual risk of the whole design, stated plainly |
| 21 | the reference build differs from the pinned binary in a C-library version (libpng, zlib) → an image read differently | TB-2, C10 | **fails**: image facts come from the *pinned* binary's probe, not from the reference build |
| 22 | an interaction command (`\errorstopmode`) followed by an error: pdfTeX tries to read the terminal | C6 | **fails in the container backend, not settled in the native one**: `docker exec` without `-i` gives pdfTeX an empty stdin, but `_oracle.py`'s native backend calls `subprocess.run([engine, …])` with no `stdin=` argument, so it inherits the grader's stdin [R, `_oracle.py` line 924]. With `-halt-on-error` an *error* never reads the terminal, but `\errorstopmode\read16 to\x` does. **Design change:** C6 fixes stdin to empty, and the oracle should pass `stdin=DEVNULL` on every backend (a one-line oracle fix, recorded as a finding) |

**What changed because of the search:**
- attacks 9, 10, 11, 12, 13 and 20 produced §5.2, the position abstraction, `buffered_io`, the output-free divergence rule, TB-9, and the branch-complete release gate;
- attack 6 makes D-1 a prerequisite;
- attacks 1–5 and 17–18 confirm that the owner's composition cases are handled *by construction*: the code runs.

**Settled against the design:** none.
**Not settled:** 10 (floats across architectures, [U]), 19 (fmt determinism, [U]), 20 (untested branches: the permanent residual, mitigated and never eliminated), 22 (the native oracle backend inherits stdin: an oracle finding, independent of this ADR).

---

## 12. Open decisions for the owner

- **O-1. Why no body run?** What is ADR-012 decision 3 *for*: a proof-shaped answer, or no engine, latency and sandboxing on the user's side? The interpreter satisfies the letter; A0 (run the pinned pdflatex) dominates it on exactness, speed and effort if only the letter matters. This decides whether either draft should be built.
- **O-2. Translate, don't transcribe.** Adopt mechanical translation of the pinned tangled `pdftex.p` (recommended), or hand transcription in stages (§5.3: no READY on a real paper before the page builder exists)?
- **O-3. Bit-exact pointer-level state** (recommended: capacities and fmt by construction), or an algebraic model with separate capacity accounts (the C-94/C-98 pattern)?
- **O-4. Format:** B1 decode the shipped fmt, with a B2 cross-check once per pin (recommended), or B2 only?
- **O-5. Nondeterministic inputs.**
  - (a) Quantify over dates, seeds and positions (recommended; requires G6 before the first paper).
  - (b) Change the oracle to `FORCE_SOURCE_DATE=1` plus a fixed `\pdfsetrandomseed`-equivalent. This is an oracle-baseline change, and every claim becomes "under the fixed date".
- **O-6. Fix D-1 first** (the stale PDF across passes; ADR-013 §1.1). Required by both drafts.
- **O-7. Named premises:** accept `FaithfulEngine` (per revision, digest and architecture), TB-6 file facts, TB-8 (the nondeterminism inventory) and TB-9 (the time budget) as the trusted base, replacing `Faithful` + contracts (+ P-1..P-4 if R-EFFECT)?
- **O-8. Source pin:** if the exact revision of the image's binary cannot be identified (H.1), accept a reference build from source as the new oracle? That is a change to ADR-012 decision 7.
- **O-9. Shell escape:** keep the oracle's restricted `\write18` (EPS papers stay `Stuck(shell)`), or grade under `-no-shell-escape` (they become exact NOT-READY, but the claim changes)?
- **O-10. The existing kernel:** freeze per-name admission (OPEN-122 slices B–D) now, pending the spike? Keep `L_S0` as the synchronous fast path and regression oracle (recommended)?
- **O-11. Spend:** fund the two-week spike (§9) before choosing between ADR-013 and ADR-014? Its kill criteria are stated. It is the cheapest way to find out whether this architecture is fatally slow or fatally large.
