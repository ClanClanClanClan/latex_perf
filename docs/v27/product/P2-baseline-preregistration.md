# P2 diagnostics baseline: pre-registration

Product track P2 ("exactly why": the cause of a failure, at source level, before compiling). The owner ruled it part of the core vision on 2026-10-21. Ledger: OPEN-138 (this baseline) and OPEN-139 (the seal outside the P2 tools), in `docs/v27/PROJECT_STATE.md`.

**Status: PROPOSED. Nothing has been scored.** The success, kill and validity lines in §7 are proposals for the owner. The scorer (`p2_baseline.py score`) refuses to run until the owner sets the lines block to `"status": "FIXED"` in a commit. Definitions version: **p2-defs/4** (`_p2_diag.DEFINITIONS_VERSION`; `check_p2_diag.py` checks that this document and the code agree).

p2-defs/2 replaced p2-defs/1 (commit `758e0e18`, never scored) after an independent review found 7 HIGH and 6 MEDIUM defects; C-183 records them. p2-defs/3 adds the review's five LOW fixes (L1, L3–L6): file names with spaces and parentheses (§3), the `artefact` claim (§4.3), the printed order of predictions (§4.2), unverified locations counted by reason (§5.4), and numerically stable bounds. Neither version was scored, and each fix has a defeat test in `check_p2_diag.py`. p2-defs/4 applies the rulings below (R2–R4): it seals the P2 held-out set (§2.2), adds the claim tier and the soundness outcome (§4.5, §5.6, §7), adds the cause-line metric with two-labeller gold (§5.5), and plans the natural author-error set (§10).

**Rulings (provenance).** R2, R3 and R4 are **the assistant's recommendations of 2026-11-03, adopted by the owner** (`~/.cache/lp-tracks-2026-11-03/RULINGS-2026-11-03.md`). They are not the owner's own phrasing. The owner asked (2026-11-03, session e5675261): "What are the answers leading to the best product for the orginal vision? Ultrathink". The coordinating assistant answered with recommendations R1–R5. The owner replied: "Yes to run docker builder prune and listing the images. And I asked best recommendations for perfect project concerning your other two questions". The assistant read that reply as adopting R1–R5.

Code: `scripts/tools/_p2_diag.py` (record, prediction, matching, metrics), `scripts/tools/_sample_seal.py` (the sample-3 refusal), `scripts/tools/p2_baseline.py` (producer and scorer), `scripts/tools/check_p2_diag.py` (unit and defeat tests). Where this document and the code disagree, that is a defect. Fix both, then bump the definitions version.

## 1. What is measured, and what is not

The oracle tells us where pdfTeX **detected** the first error: its message, its `l.N` and the input file it was reading. The baseline measures how often the CLI's `--compile-check` answer names that cause and that place **before compiling**. The oracle is only the ground truth we score against. Running it is never the product (memory: engine-in-the-loop is not a product).

The following are not measured here:
- **The location of the cause.** TeX reports where it noticed the error, which can come after the cause. For example, a missing `.sty` on line 3 is reported at `l.4`, and a runaway argument at end of file has no line at all; both are in the fixtures. The log does not contain the cause's location, so this baseline cannot score it.
- **Columns.**
- **Fix suggestions.**
- **Any error after the first.** Under `-halt-on-error` there is none.

## 2. Samples, and the seal

### 2.1 Samples 1 and 2, and sample 3

- **The baseline uses samples 1 and 2 only.** Per **ruling R2**, P2 may NOT use sample 3 for anything: no baseline, no design, no scoring. Sample 3 stays sealed for the verdict tier's North-Star measurement (OPEN-119); it also has too few failing documents for P2's floors. (Until R2, this restriction was the assistant's default pending stock-take §8 #16.) Sample 1 is frame ranks 1–200 (offset 0); its grade of record is `corpora/real_roots/results.json`. Sample 2 is ranks 201–400 (offset 200); its grade of record is `corpora/real_roots/results_sample2.json`. The frame is the 2,719-paper frame ordered by `sha256(arxiv_id)`.
- **Sample 3 (ranks 721–920, offset 720) is SEALED (OPEN-119) and is never used.** Before this branch the seal was a convention, not a mechanism (C-180).
- **Neither sample is virgin.** Sample 1 has been tuned on and sample 2 has been seen during design. Reading their P2 records makes both design-seen for P2 as well. So a later P2 success measured on them is **in-sample**. Out-of-sample sets: the P2 held-out set (§2.2) and the natural author-error set (§10).
- **Size.** The scorer counts the oracle-failing rows; this document does not restate the count (one number, one artefact). The count is a few dozen across both samples, so every rate carries an exact one-sided 95% Clopper–Pearson bound. At this n a 0/n result still leaves an upper bound near 10%. Lines V1, V6 and V7, and the `min_n` of each line, set floors on n.

### 2.2 The P2 held-out set (ruling R3)

**The set.** Frame offsets **920–1999**: n = 1,080, the ranks after sample 3 in the same frame (2,719 papers, ordered by `sha256(arxiv_id)`). It is committed as `corpora/real_roots/manifest_p2_heldout.json`, which holds ids and verification counts only.

**How the manifest was built.** It was built by the frame's own rule (`diff_real_roots.build_frame` then the sha256 order) **without reading any document in the window**. Only arXiv's `00README.json` metadata, which defines frame membership, was read, plus a stat of each toplevel. The build reproduced the frame exactly:
- the frame has 2,719 papers;
- sample 1 equals ranks 0–199, sample 2 equals ranks 200–399, and sample 3 equals ranks 720–919;
- the window holds 1,080 valid, distinct ids, disjoint from samples 1–3.

**Ref check before sealing.** Before sealing, every branch and remote tip (526 refs) was searched for a frame window in 920–1999, on 2026-11-03. **None was found.** The nearest windows are sample 3 (offsets 720–919) and apply_fixes_real's windows at offsets 2000–2718. Earlier frame-wide corpus scans did touch these documents, in aggregate and never as a window; OPEN-138 lists them.

**The seal.** It uses the same mechanism as sample 3 (§2.3): the allow-list, the committed manifest, and refuse-everything if the manifest is unreadable. No P2 command may read, grade, design on, triage or list a held-out document. `record` and `score` refuse any window that meets it and any of its ids.

**How the held-out set may be used** (pre-registered here; no command does it yet):
- **Measurement only.** The set is never used for design, tuning or triage, and its documents and outputs are never read or listed one by one.
- **Aggregate output only.** A held-out run writes its per-document rows to its record (needed to verify it), but prints and publishes only counts and rates. No id, error text or per-document line goes to a terminal, a report or a ledger row.
- **One pre-registered run per milestone.** Each run is named in an amendment to this document **before** it happens: the milestone, the CLI commit, and the lines it is judged by. One run per milestone means no re-runs to improve a number. A run that is VOID or ungraded is reported as such, and is re-run only for an infrastructure cause recorded beforehand. A run that produces a SOUNDNESS DEFECT is final.
- **Enabling it.** A measuring command for the held-out set requires that amendment, with its own defeat tests. Until then, the P2 tools refuse the set.

**Caveat** (recorded with R3). arXiv failures under the pinned TL2026 are mostly **package drift** (arXiv built on TL2023). That is the publisher's situation, not the laptop author's; the author's situation is §10.

### 2.3 How `_sample_seal` enforces the seals

The same mechanism covers both sealed sets: sample 3 and the held-out set.

- **It works by allow-list and fails closed.** It does not try to recognise sealed inputs; it accepts only what it can prove belongs to samples 1–2:
  - **Document ids.** An id is accepted only if it is a string that fully matches the ASCII pattern `NNNN.NNNN(N)vN`. Nothing is normalised: any other string is refused, never mapped onto an id. Every id in samples 1, 2 and 3 matches this pattern (measured 2026-11-03). Papers are compared without the version suffix, so another version of a sealed paper is also sealed.
  - **Committed inputs only.** Every input is read from its committed blob at HEAD: the seal manifest, the grade of record, the pre-registration and the records. The working-tree file must equal that blob, and the blob ids are stamped into every output.
  - **Sample identity.** A sample is the number 1 or 2. Its ids must be exactly the 200 ids of its grade of record: valid, distinct and none sealed. A record is accepted only if its rows are exactly those documents, each appearing once. A record's own `sample` label is not trusted on its own.
  - **Tree checks.** A document's `toplevel` must be relative, must contain no `..`, and must resolve inside the document's package. A package containing any symlink is refused (C-182).
  - **Unreadable seal.** Every request is refused when a seal manifest cannot be read, when it does not hold exactly its n valid, distinct ids at its offset (200 at 720; 1,080 at 920), or when the two sealed sets overlap.

  There is no bypass. `check_p2_diag.py` §8 tries each known way round the seal and asserts it is refused. Tools outside P2 are still ungated (OPEN-139).

## 3. Ground truth: the oracle-side record (`_p2_diag.diag_record`)

**The run.** Each document is graded by the pinned oracle through `_oracle.get_oracle()`. The run uses the recorded protocol `diff_real_roots.run_to_fixpoint_full`: `-interaction=nonstopmode -halt-on-error`, pdflatex's default restricted shell-escape, up to 3 passes plus a confirming pass, and `PROTOCOL_CLOCK`. Each document runs in its own copy of its package. Before the copy, the package is checked: no symlink, no online-only file and no special file (checked with lstat, before any read), and then its `sha256_tree` must match the grade of record. The log read is the **last pass's** `<job>.log`.

**Compiles.** "Compiles" means rc 0 **and** a PDF, as in the grade of record. A row whose re-run rc or compiles value differs from the grade of record is excluded and counted (V2).

**Line model.** A raw log line of exactly 79 bytes continues on the next line; this is the oracle's own `_unwrap_log` rule.
- `!` lines, messages and the file stack are read **un-wrapped**.
- Context pairs are read **raw**. A context pair's second line is padded to 79 bytes and the help text follows it with no blank line (measured), so un-wrapping a context pair would glue it to the help text.

The record holds the following fields:

| Field | Definition |
|---|---|
| **first error** | The first un-wrapped line that begins with `!`, together with its block. pdfTeX's own final report line (`!  ==> Fatal error occurred, …`) does not count. The **message** is the block's first paragraph, in full and **not truncated**. The help text after the first blank line is kept in `message_lines` but is not part of the message. |
| **context_pairs** | TeX's two-line context pairs, read raw. |
| **l.N** | The first context line of the form `l.N …` at or after the first block. LaTeX's missing-file path prints a `\typeout` "! LaTeX Error: File … not found." followed by "! Emergency stop."; the `l.N` is in the second block. |
| **file stack** | The input files open when the first block starts, outermost first, from a parenthesis parse of the un-wrapped log. Every `(` pushes a file or a text marker. pdfTeX prints file names verbatim, spaces and parentheses included (measured: `(./my file.tex`, `(./fig(1).tex`). So the name is the **longest** text after the `(` that names a file in the tree, ending at a space, a parenthesis or the end of the line. Failing that, a name starting with `./`, `../` or `/`, ending at a space or parenthesis, is still a (TeX Live) file. Anything else is a text marker. Every `)` pops. Two kinds of line print document text with unbalanced parentheses and are skipped: box dumps after `Overfull`/`Underfull` warnings, up to their blank line, and `Missing character:` lines. |
| **stack certainty** | pdfTeX prints a file's `)` straight after that file's last output. A `)` that closes a file frame is therefore expected in one of three places: at the start of a line, after other closers or page markers, or on the same line as that file's own open. A `)` that closes a file frame after other printed text (for example `item a)`) may be the document's own text. It is counted as a **suspect pop**. Suspect pops and underflows are recorded. |
| **location** | `file` is `canon_path` of the top stack frame (§5.1), or none when it is a TeX Live file. `frame` is `document`, `system` or `none`. `author_file` is the innermost frame inside the tree. `line` is l.N. |
| **verified** | True only when all three hold: (i) line N of `file` contains the text pdfTeX printed around the error point (left-truncated `...`, right-truncated `...` and a trailing `^^M` are allowed; `^^xx` and `^^c` are decoded; trailing spaces and the end-of-line character are stripped, as pdfTeX does); (ii) the stack has no suspect pop and no underflow; (iii) no **other** tree file opened before the error carries the same context at line N (ambiguity check). A location that fails is **excluded**, not guessed (V4). |
| **consistent** | True only when the first block is the error pdfTeX stopped on. All three must hold: (i) pdfTeX's fatal-error report follows the last block, since `-halt-on-error` always prints it; (ii) no raw line beginning with `!` continues a 79-byte line, because that output is ambiguous; (iii) there is exactly one `!` block, or there are two and they form the missing-file prompt (`Enter file name:`) followed by `Emergency stop` with "cannot \read from terminal". Anything else is text that a document or package printed (the C-99 forgery) or an ambiguous log. Such a row is excluded from cause and location scoring (V5). |
| **cause** | `(class, object)` of the first message, from the ordered table `CAUSE_RULES`; the first match wins. Matching uses the **flat** message: its lines are joined, and LaTeX's `(pkg)   ` continuation prefixes are removed. See the rules after this table. |

**Cause rules.**
- **The classes:** `missing-file`, `engine-incompatible`, `undefined-cs`, `undefined-env`, `env-mismatch`, `missing-begin-document`, `command-already-defined`, `option-clash`, `encoding`, `brace-imbalance`, `left-right-imbalance`, `math-mode`, `alignment`, `tex-capacity`, `package-error`, `class-error`, `latex-error`, `emergency-stop` and `other`.
- **Package and class errors** are recognised in all three printed forms: plain, `Fatal` and `Critical`.
- **`engine-incompatible`** has two cases:
  - A package or class error whose text names an engine requirement (`XeTeX`, `LuaTeX`, `XeLaTeX`, `LuaLaTeX`, `Lua(HB)(La)TeX`, `pdftex` or `pdflatex`, or "unavailable in current mode"). The object is the package that raised it.
  - An undefined control sequence that is a primitive of another engine (for example `\luatexversion`). The object is the top stack frame's package.

  The pdfTeX output of every package named in `FEATURE_PACKAGES` was recorded with the same pdfTeX build as the pin and is in the fixtures. That is why the error is attributed to the package that **raised** it: polyglossia's error comes from fontspec, luatexja's from luatexja-core, and luatexbase's from ltluatex.
- **Objects are normalised** by `norm_object`:
  - a file: its basename, without one known extension (`.tex`, `.sty`, `.cls`, `.pdf`, `.png`, `.eps`, `.bib` and so on);
  - a package: lower-cased, with `-` and `_` removed;
  - for `undefined-cs`: the control sequence at the end of the first context line.

**This is a diagnostic, not evidence (C-99).** No grade is decided from it. The `consistent` and `verified` checks are how a forged, ambiguous or unparseable record gets excluded.

## 4. The prediction: the CLI side (`_p2_diag.cli_prediction`)

### 4.1 The run

The CLI runs in the copied package directory with the **relative** toplevel: `cd <copy> && validators_cli.exe --compile-check <toplevel>`. It runs with `L0_VALIDATORS=pilot`, which is the grade of record's setting. Both stdout and stderr are read.

**Provenance.** The CLI's binary sha256, its checkout's HEAD and its `latex-parse/src` tree are stamped into the record. The checkout's `latex-parse/src` must have no uncommitted or untracked change; otherwise the run is refused.

### 4.2 What counts as the prediction

Only the **frozen surface** counts: the lines before `TIER\t`, on stdout and then on stderr, the same scope as `diff_real_roots.scrape_reasons`. The `TIER` and `why not strict:` lines name constructs that block a proof, not causes of an error, so they are not predictions.

The predictions are the following lines, **in the order the CLI prints them**. The CLI prints `MODEL-CONNECTED` first, then `READY`/`NOT-READY` and its reasons.
1. The indented lines under `MODEL-CONNECTED`, **only when its state is `PREMISE-REJECTED`**. Under `PREMISE-CERTIFIED`, the certified premises predict no error.
2. The indented reasons under `NOT-READY`.

The non-blocking duplicate-label advisory and the `(model-connected checks …)` pointer line are not predictions. A `READY` answer predicts nothing.

**Top-1** is the first prediction in that printed order, within its claim tier (§4.5).

### 4.3 Class of a prediction

| Reason | Class, object |
|---|---|
| `T5 rule violations: [ids]` | One prediction per id. DELIM-001/002 → `brace-imbalance`. DELIM-003/004/009/011 → `left-right-imbalance`. ENC-001/002/004/005/006/009/012/014 → `encoding`. Every other id → no class (it can never be cause-correct). |
| `structural-fatal … [parts]` | Each part names the TeX message it predicts (`…: ! Double superscript`). That message is classified with the same `CAUSE_RULES`. |
| `T2 … missing file P` | `missing-file`, object `P`. |
| `T3 … feature F …` (contract or model line) | `engine-incompatible`, object set = the packages that **raise** F's error (`FEATURE_PACKAGES`). |
| `artefact-fatal (F): …` | **No class**: the gold taxonomy has none for it, because TeX reports an error inside an artefact as whatever it is. It would otherwise be unscorable by construction. The file F is a file-level claim. |
| `T0 …`, `T1 …`, `T2 cycle`, `T4 …`, `input too large`, other model lines | No class: the reason says NOT-READY without naming a cause that TeX would report. |

### 4.4 Location claims

A prediction claims a location when its text names a file and a line: `F:N`, or `in F` together with `(line N)`. Every claimed file goes through `canon_path` (§5.1), using the directory the CLI ran in as its root; the printed text is kept in `file_raw`. As of v27.1.64 only LP-Foreign `T0` reasons claim a location, and they name a construct, not an error.

### 4.5 The claim tier (ruling R4)

Every prediction carries a claim tier, **CERTIFIED** or **HEURISTIC**, and the two are scored separately.
- **Certified.** A prediction is certified only when the CLI's `TIER` line is a `proven` `PROVEN-NOT-READY` verdict. That verdict is decided by the strict tier's proof (`Verdict.render`). Its `file:line:col` and its message form the certified claim: the message is classified with `CAUSE_RULES`, and the location is checked against TeX's stopping line `l.N`. A certified claim whose `TIER` line cannot be parsed counts as **wrong** (fail closed).
- **Heuristic.** Every frozen-surface reason is heuristic.
- **Today.** As of v27.1.64 the strict tier's membership predicate is a stub (M0), so the certified channel is empty, by measurement.
- **A row's claim** for recall is its certified claim if it has one, and otherwise its first heuristic one. Recall is therefore measured on certified ∪ heuristic.

## 5. Matching and metrics (`_p2_diag.cause_correct`, `location_correct`, `score_rows`)

### 5.1 Matching rules

- **One path normalisation, `canon_path`.** It is used for the gold file, the claimed file and every stack entry:
  - A path is made relative to the document root.
  - An absolute path under one of the run's roots is made relative. The roots are the host work directory, its resolved form, and the container's `/lp/run`.
  - The path is then `normpath`ed.
  - An absolute path outside the run, or any path that escapes with `..`, becomes **None**, and None never matches anything.
- **Correct cause:** the classes are equal. When both sides name an object, the normalised objects must also be equal. For a T3 object set, the gold package must be in the set.
- **Correct location, line level:** the canonical files are equal and not None, **and** the predicted line equals l.N **exactly**. No tolerance is pre-registered; an offset is wrong.
- **Correct location, file level:** the canonical files are equal.

### 5.2 Metric sets

- **R_fail:** graded, agreeing rows where the oracle fails.
- **R_cause:** the rows of R_fail with a consistent record and a classified cause.
- **R_loc:** the rows of R_cause whose gold location has a line, lies in the document tree (not a system frame) and is **verified**.

### 5.3 Metrics

Each metric is reported as k, n, and the exact one-sided 95% Clopper–Pearson lower and upper bounds. These are computed in log space, so they stay stable at any n; they are tested at n = 5000.

| Metric | k / n |
|---|---|
| `cause_recall_top1` | R_cause rows where the CLI says NOT-READY and the row's claim (§4.5) is cause-correct / \|R_cause\| |
| `cause_precision_top1_{certified,heuristic}` | Per tier: correct / every row whose first prediction of that tier names a class. A class named on a **compiling** document counts as wrong. R_fail rows that are not in R_cause are left out. |
| `location_precision_line_{certified,heuristic}` | Per tier: correct against l.N / every row whose first prediction of that tier claims a (file, line). A claim on a compiling document counts as wrong. R_fail rows that are not in R_loc are left out. |
| `location_precision_cause_heuristic` | Heuristic located claims that are correct against the **cause-line** gold (§5.5) / every heuristic located claim on a labelled row or a compiling row |
| `location_recall_line` | R_loc rows where top-1 is line-correct / \|R_loc\| |
| `location_recall_file` | R_loc rows where top-1 is file-correct / \|R_loc\| (secondary) |

Recall counts a READY answer on a failing document as a miss. That answer is a FALSE-READY, which is graded elsewhere; here it simply gives no cause.

p2-defs/1 had a fifth metric, `cause_recall_any` (any prediction, not just top-1, names the cause). It is **dropped**: a predictor that lists every class scores 100% on it (review M3(d)).

### 5.4 Exclusions

Every exclusion is counted **by reason** in the score output. Record-time exclusions are counted under `excluded_at_record_by_reason`, and their total is floored by V0. The reasons are:
- **at record time:**
  - missing from the corpus;
  - a symlink, an online-only file or a special file in the package;
  - an unsafe toplevel;
  - no tree hash, or a tree hash that differs from the grade of record;
- **ungraded:** a timeout on either side. Under load this means a rerun, not a verdict;
- **disagrees** with the grade of record;
- **for cause scoring:** no error block, an inconsistent record, or an unclassified record;
- **for location scoring:** no l.N, a system top frame, or an unverified location. Unverified locations are also counted **by reason** (`location_unverified_by_reason`): a file the tree does not have (for example a mis-parsed name), an uncertain stack, an ambiguous match, a line outside the file, or context not on the line.

### 5.5 The cause line: two-labeller gold (ruling R4)

TeX's stopping line `l.N` is the gold for **certified** location claims. The **cause** line is a different thing: the line an author edits to fix the error, for example the `\usepackage` on line 3 when TeX reports `l.4`. It is scored as a **heuristic** claim, against gold made by two independent labellers.

**The protocol.**
1. **Who and what.** Two labellers, A and B, label each document independently. A labeller is a person, or an agent session with no shared context. Each receives the document's source tree and the oracle's first-error record (message, `l.N`, file stack). Neither sees the CLI's output, any prediction, the other labeller's labels or any score. Labels are written before any cause-line prediction is scored, and are committed as `corpora/p2_baseline/cause_labels.json` (schema `p2-cause-labels/1`).
2. **The label.** Each labeller records the (file, line) of the smallest edit that fixes the first error, or `{"none": reason}` when no single line is the cause.
3. **Agreement.** When A and B give the same canonical (file, line), that is the gold.
4. **Disagreement.** A third person, the adjudicator, resolves it. The adjudicator is distinct from both labellers and equally blind to the CLI, and picks one of the two labels or `"unresolvable"`. An unresolvable document has no gold and is counted.
5. **Both "none".** When both labellers say `none`, the document has no cause line and is counted.
6. **Reporting.** The agreement statistics (entries, agreed, adjudicated, unresolved, no cause line) are part of the score output.
7. **Never on sealed sets.** No document of a sealed set is labelled: labelling is per-document reading. The cause-line metric is computed on samples 1–2 and on the natural author-error set (§10) only.

The scorer reads the label file from HEAD. If no label file is committed, the metric has n = 0 and is not evaluable.

### 5.6 Soundness (ruling R4)

Certified precision must be **exactly 1.0**. A single wrong certified claim is a **SOUNDNESS DEFECT**, treated like a wrong PROVEN verdict: the certified channel stops and the class is fixed. It is **not** a statistical kill.

**When a certified claim is wrong.** It is wrong when any of these holds:
- it is on a document that compiles;
- it names a class that is not the gold cause;
- its location is not `l.N`;
- its `TIER` line is malformed.

A certified claim on a row whose gold is excluded is counted as **unscorable**, not as correct.

**Reporting.** The scorer reports the outcome `SOUNDNESS-DEFECT` with exit **5**, and the defect takes precedence over VOID. The soundness block (claims, wrong, unscorable, malformed, wrong rows) is in every score output, void or not.

## 6. Procedure (stage 2; not run on this branch)

Stage 2 starts only after Track B writes `~/.cache/lp-track-B/LANES_DONE` and the owner fixes the lines in §7. Track B holds the oracle containers first; at most 2 run at once across the machine.

```
python3 scripts/tools/p2_baseline.py record --sample 1 --corpus-root "$LP_REAL_CORPUS" --out corpora/p2_baseline/diag_sample1.json
python3 scripts/tools/p2_baseline.py record --sample 2 --corpus-root "$LP_REAL_CORPUS" --out corpora/p2_baseline/diag_sample2.json
git add corpora/p2_baseline/diag_sample{1,2}.json && git commit ...   # score reads committed records only
python3 scripts/tools/p2_baseline.py score --records corpora/p2_baseline/diag_sample1.json corpora/p2_baseline/diag_sample2.json --out corpora/p2_baseline/score.json
```

- **`score` inputs.** `score` takes exactly the two records, one for sample 1 and one for sample 2. It reads the pre-registration from HEAD at its canonical path; there is no option that names another file.
- **`score` output.** The output records HEAD, the pre-registration's blob, the seal manifest's blob, and each record's blob and sha256.
- **VOID runs.** If a validity line fails, the run is **VOID**: exit 4, the output holds only the validity lines, the counts and the soundness block, and no metric is presented as a result.
- **Soundness defects.** A wrong certified claim gives **exit 5** (§5.6), whatever else holds.
- **Provenance.** Each `record` stamps a `RunStamp` before its first engine run. The stamp covers the oracle core plus `p2_baseline.py`, `_p2_diag.py`, `_sample_seal.py` and `diff_real_roots.py`. The command also stamps the grade-of-record and seal blobs, and re-checks all of them before writing.
- **Grading blobs.** `_oracle.py` and `diff_real_roots.py` are not modified, so every recorded grade's `grading_code` (blobs 6b4ce94e and 9859cccf) still names this tree's code. `check_p2_diag.py` §9 asserts this for samples 1–2.
- **Artefact registration.** `check_oracle_pin.py` registers `corpora/p2_baseline/diag_sample{1,2}.json` as GRADED, with these graders. Until stage 2 writes them, the gate reports them missing.

## 7. Lines (PROPOSED: for the owner to fix)

The lines come in four kinds:
- **Validity:** if one does not hold, the run is **VOID**. It is reported as a failed run (exit 4); no metric is presented.
- **Prediction:** pre-registered expectations about the baseline. They are reported, not pass/fail.
- **Success:** the target for the P2 deliverable. It is measured later under the same definitions; **the baseline itself is not judged against it.**
- **Kill:** retires the P2 design route measured at that milestone, never the goal. A KILL line "holds" when it fires.

**`min_n` (not evaluable).** A line with `min_n` is not evaluable when its metric's n is below that floor:
- A success line that is not evaluable is **not met**.
- A kill line that is not evaluable **does not fire**.

So a predictor that never claims a location or names a cause cannot pass: its success lines are not evaluable. Nor can it be killed: its kill lines do not fire. Its milestone is reported as "not evaluable: no claims", which is a failure to deliver, not a pass.

**Floors (ruling R4).**
- **Success.** Every success line has `min_n` **29**: zero errors in 29 claims gives a one-sided 95% lower bound of 0.90, while 10 claims give only 0.74. The **next floor is 59** (lower bound 0.95), to be adopted once the sets can supply it.
- **Kill.** Kill lines keep `min_n` 10, unchanged from p2-defs/2. R4 sets no kill floor, and a kill that never becomes evaluable would never retire a failing route.
- **Certified.** The certified channel has no kill line: it has the soundness outcome instead (§5.6).

All values below are proposals.

| id | kind | metric | test | proposal and rationale |
|---|---|---|---|---|
| V0 | validity | excluded.at_record | = 0 | Every document of both samples is graded. Online-only files must be made available offline first. A changed tree means the corpus is not the one that was graded. |
| V1 | validity | inputs.fails | ≥ 20 | Below 20 failing rows the bounds say nothing. |
| V2 | validity | excluded.disagrees_with_record | = 0 | Same oracle, same clock, same tree: any disagreement means the instrument is not the grade of record. |
| V3 | validity | excluded.ungraded | = 0 | A timeout is a rerun (COMMON rules), not a datum. |
| V4 | validity | excluded.location_unverified | ≤ 3 | Above roughly 10% of R_fail, the log parser, not the CLI, is what is being measured. |
| V5 | validity | excluded.cause_inconsistent | ≤ 2 | More would mean forged, ambiguous or multi-error logs are common enough to need their own design. |
| V6 | validity | inputs.cause_scored | ≥ 20 | Floor on \|R_cause\|. |
| V7 | validity | inputs.location_scored | ≥ 15 | Floor on \|R_loc\|. |
| P1 | prediction | location_recall_line (point) | ≤ 0.10 | The v27.1.64 CLI prints no error lines (§4.4), so the baseline sits at the zero point. |
| SC1 | success | location_precision_line_certified (point), min_n 29 | = 1.0 | Exactly 1.0. A miss is a soundness defect (§5.6), not merely a failed line. |
| SC3 | success | cause_precision_top1_certified (point), min_n 29 | = 1.0 | The same, for certified causes. |
| SH1 | success | location_precision_line_heuristic (point), min_n 29 | ≥ 0.95 | Heuristic, against l.N. |
| SH3 | success | cause_precision_top1_heuristic (point), min_n 29 | ≥ 0.95 | |
| SH5 | success | location_precision_cause_heuristic (point), min_n 29 | ≥ 0.95 | Against the cause-line gold (§5.5). |
| S2 | success | location_recall_line (point), min_n 29 | ≥ 0.50 | On certified ∪ heuristic. |
| S4 | success | cause_recall_top1 (point), min_n 29 | ≥ 0.80 | On certified ∪ heuristic. |
| KH1 | kill | location_precision_line_heuristic (point), min_n 10 | < 0.90 | Fires: that heuristic route is retired. |
| KH3 | kill | cause_precision_top1_heuristic (point), min_n 10 | < 0.90 | Fires: that heuristic route is retired. |
| KH5 | kill | location_precision_cause_heuristic (point), min_n 10 | < 0.90 | Fires: that heuristic route is retired. |

The block below is machine-readable. The scorer reads it **from HEAD**, and it is the authority if it ever differs from the table. The owner fixes the lines by changing `"status"` to `"FIXED"` (with any value changes) in a commit of their own.

<!-- P2-LINES:BEGIN -->
```json
{
 "status": "PROPOSED",
 "definitions": "p2-defs/4",
 "lines": [
  {"id": "V0", "kind": "validity", "metric": "excluded.at_record", "stat": "n", "op": "==", "value": 0},
  {"id": "V1", "kind": "validity", "metric": "inputs.fails", "stat": "n", "op": ">=", "value": 20},
  {"id": "V2", "kind": "validity", "metric": "excluded.disagrees_with_record", "stat": "n", "op": "==", "value": 0},
  {"id": "V3", "kind": "validity", "metric": "excluded.ungraded", "stat": "n", "op": "==", "value": 0},
  {"id": "V4", "kind": "validity", "metric": "excluded.location_unverified", "stat": "n", "op": "<=", "value": 3},
  {"id": "V5", "kind": "validity", "metric": "excluded.cause_inconsistent", "stat": "n", "op": "<=", "value": 2},
  {"id": "V6", "kind": "validity", "metric": "inputs.cause_scored", "stat": "n", "op": ">=", "value": 20},
  {"id": "V7", "kind": "validity", "metric": "inputs.location_scored", "stat": "n", "op": ">=", "value": 15},
  {"id": "P1", "kind": "prediction", "metric": "location_recall_line", "stat": "point", "op": "<=", "value": 0.1},
  {"id": "SC1", "kind": "success", "metric": "location_precision_line_certified", "stat": "point", "op": "==", "value": 1.0, "min_n": 29},
  {"id": "SC3", "kind": "success", "metric": "cause_precision_top1_certified", "stat": "point", "op": "==", "value": 1.0, "min_n": 29},
  {"id": "SH1", "kind": "success", "metric": "location_precision_line_heuristic", "stat": "point", "op": ">=", "value": 0.95, "min_n": 29},
  {"id": "SH3", "kind": "success", "metric": "cause_precision_top1_heuristic", "stat": "point", "op": ">=", "value": 0.95, "min_n": 29},
  {"id": "SH5", "kind": "success", "metric": "location_precision_cause_heuristic", "stat": "point", "op": ">=", "value": 0.95, "min_n": 29},
  {"id": "S2", "kind": "success", "metric": "location_recall_line", "stat": "point", "op": ">=", "value": 0.5, "min_n": 29},
  {"id": "S4", "kind": "success", "metric": "cause_recall_top1", "stat": "point", "op": ">=", "value": 0.8, "min_n": 29},
  {"id": "KH1", "kind": "kill", "metric": "location_precision_line_heuristic", "stat": "point", "op": "<", "value": 0.9, "min_n": 10},
  {"id": "KH3", "kind": "kill", "metric": "cause_precision_top1_heuristic", "stat": "point", "op": "<", "value": 0.9, "min_n": 10},
  {"id": "KH5", "kind": "kill", "metric": "location_precision_cause_heuristic", "stat": "point", "op": "<", "value": 0.9, "min_n": 10}
 ]
}
```
<!-- P2-LINES:END -->

## 8. Threats to validity

- **Forged log text (C-99).** Mitigated by the `consistent` and `verified` checks (§3). One residual remains, and it is accepted and stated here: a single genuine-looking block whose forged `l.N` reproduces a real line of the same file (review exp3 "E") is indistinguishable from TeX's own output. It can be produced only by a document that prints text copied from its own source.
- **Parser bias.** The parenthesis parse and the context reader are heuristics over pdfTeX's output, tested on the shapes in the fixtures. Fixtures were produced on the laptop TeX Live (the same pdfTeX build as the pin), not on the oracle. The stack-certainty and ambiguity checks exclude, rather than guess, when the parse can be wrong. The first stage-2 run's V4/V5 counts should be read before any score.
- **79-byte ambiguity.** A raw `!` line after a 79-byte line makes the record inconsistent (§3).
- **Detection location versus cause location** (§1). The baseline scores TeX's detection point, by definition.
- **Small n, and in-sample reuse** (§2).

## 9. Amendments

Once the lines are FIXED, any change to a definition in §3–§5 or to a line needs three things: a new definitions version, the owner's sign-off, and the earlier version's results kept beside the new ones. Results are never re-scored silently under new definitions.

## 10. The natural author-error set: feasibility plan (ruling R3; no mining yet)

**Goal.** A second out-of-sample set of **natural** broken states: documents an author actually broke and later fixed, which is the laptop author's situation rather than the publisher's package drift (§2.2 caveat). Injected or synthetic errors are allowed for development and regression tests only, **never for a headline number**.

**Candidate source.** Public LaTeX git repositories, where a commit breaks the build and a later commit fixes it. The broken commit is the document; the fixing commit's diff is a label candidate for §5.5.

**The feasibility check** is about one day, and it mines nothing yet. It answers six questions; each answer becomes an amendment before any mining.
1. **Source and licence.** Which hosts and searches yield LaTeX repositories with history, under which licences? The set's sources must be storable as hashes, with a manifest, as for the arXiv frame.
2. **Selection rule.** A deterministic rule, fixed before looking at outcomes, for example sha256 order over (repository, commit) pairs that pass a mechanical filter. The filter is: a pdflatex single-toplevel build, the parent commit compiles under the pinned oracle, the commit fails, and a later commit compiles again.
3. **Yield.** An estimate of how many candidate pairs per 1,000 repositories survive the filter, so we know whether P2's floors (n ≥ 29 claims per tier; 59 later) are reachable. The estimate comes from repository metadata and commit counts, not from opening documents.
4. **Oracle cost.** Compilations per candidate (parent, broken and fixed) under the measurement clock, against the 2-container limit.
5. **Contamination.** Repositories whose history is mostly machine-generated, or that vendor arXiv sources, are excluded by rule.
6. **Sealing.** Like §2.2, the set is drawn once, sealed, measurement only, aggregate output.

**Ledger.** Outcome and dates go in OPEN-138 (5). The id range for new OPEN items is exhausted on this track; the coordinator assigns one if the check needs its own row.
