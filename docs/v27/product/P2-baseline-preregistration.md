# P2 diagnostics baseline: pre-registration

Product track P2 ("exactly why": the cause of a failure, at source level, before compiling). The owner ruled it part of the core vision on 2026-10-21. Ledger: OPEN-138 (this baseline) and OPEN-139 (the seal outside the P2 tools), in `docs/v27/PROJECT_STATE.md`.

**Status: PROPOSED. Nothing has been scored.** The success, kill and validity lines in §7 are proposals for the owner. The scorer (`p2_baseline.py score`) refuses to run until the owner sets the lines block to `"status": "FIXED"` in a commit. Definitions version: **p2-defs/3** (`_p2_diag.DEFINITIONS_VERSION`; `check_p2_diag.py` checks that this document and the code agree).

p2-defs/2 replaced p2-defs/1 (commit `758e0e18`, never scored) after an independent review found 7 HIGH and 6 MEDIUM defects; C-183 records them. p2-defs/3 adds the review's five LOW fixes (L1, L3–L6): file names with spaces and parentheses (§3), the `artefact` claim (§4.3), the printed order of predictions (§4.2), unverified locations counted by reason (§5.4), and numerically stable bounds. Neither version was scored, and each fix has a defeat test in `check_p2_diag.py`.

Code: `scripts/tools/_p2_diag.py` (record, prediction, matching, metrics), `scripts/tools/_sample_seal.py` (the sample-3 refusal), `scripts/tools/p2_baseline.py` (producer and scorer), `scripts/tools/check_p2_diag.py` (unit and defeat tests). Where this document and the code disagree, that is a defect. Fix both, then bump the definitions version.

## 1. What is measured, and what is not

The oracle tells us where pdfTeX **detected** the first error: its message, its `l.N` and the input file it was reading. The baseline measures how often the CLI's `--compile-check` answer names that cause and that place **before compiling**. The oracle is only the ground truth we score against. Running it is never the product (memory: engine-in-the-loop is not a product).

The following are not measured here:
- **The location of the cause.** TeX reports where it noticed the error, which can come after the cause. For example, a missing `.sty` on line 3 is reported at `l.4`, and a runaway argument at end of file has no line at all; both are in the fixtures. The log does not contain the cause's location, so this baseline cannot score it.
- **Columns.**
- **Fix suggestions.**
- **Any error after the first.** Under `-halt-on-error` there is none.

## 2. Samples, and the seal

- **Samples 1 and 2 only** (owner ruling 2026-10-21). Sample 1 is frame ranks 1–200 (offset 0); its grade of record is `corpora/real_roots/results.json`. Sample 2 is ranks 201–400 (offset 200); its grade of record is `corpora/real_roots/results_sample2.json`. The frame is the 2,719-paper frame ordered by `sha256(arxiv_id)`.
- **Sample 3 (ranks 721–920, offset 720) is SEALED (OPEN-119) and is never used.** Before this branch the seal was a convention, not a mechanism (C-180).
- **How `_sample_seal` enforces it.** It works by **allow-list and fails closed**. It does not try to recognise sample-3 inputs; it accepts only what it can prove belongs to samples 1–2:
  - **Document ids.** An id is accepted only if it is a string that fully matches the ASCII pattern `NNNN.NNNN(N)vN`. Nothing is normalised: any other string is refused, never mapped onto an id. Every id in samples 1, 2 and 3 matches this pattern (measured 2026-11-03). Papers are compared without the version suffix, so another version of a sealed paper is also sealed.
  - **Committed inputs only.** Every input is read from its committed blob at HEAD: the seal manifest, the grade of record, the pre-registration and the records. The working-tree file must equal that blob, and the blob ids are stamped into every output.
  - **Sample identity.** A sample is the number 1 or 2. Its ids must be exactly the 200 ids of its grade of record: valid, distinct and none sealed. A record is accepted only if its rows are exactly those documents, each appearing once. A record's own `sample` label is not trusted on its own.
  - **Tree checks.** A document's `toplevel` must be relative, must contain no `..`, and must resolve inside the document's package. A package containing any symlink is refused (C-182).
  - **Unreadable seal.** If the seal cannot be read, or does not hold exactly 200 valid ids at offset 720, every request is refused.

  There is no bypass. `check_p2_diag.py` §8 tries each known way round the seal and asserts it is refused. Tools outside P2 are still ungated (OPEN-139).
- **Neither sample is virgin.** Sample 1 has been tuned on and sample 2 has been seen during design. Reading their P2 records makes both design-seen for P2 as well. So a later P2 success measured on them is **in-sample**. Claiming it generalises needs an out-of-sample set that the owner designates (OPEN-138 (3)).
- **Size.** The scorer counts the oracle-failing rows; this document does not restate the count (one number, one artefact). The count is a few dozen across both samples, so every rate carries an exact one-sided 95% Clopper–Pearson bound. At this n a 0/n result still leaves an upper bound near 10%. Lines V1, V6 and V7, and the `min_n` of each line, set floors on n.

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

**Top-1** is the first prediction in that printed order.

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
| `cause_recall_top1` | R_cause rows where the CLI says NOT-READY and top-1 is cause-correct / \|R_cause\| |
| `cause_precision_top1` | correct / every row whose top-1 names a class. A class named on a **compiling** document counts as wrong. R_fail rows that are not in R_cause are left out. |
| `location_precision_line` | line-correct / every row whose top-1 claims a (file, line). A claim on a compiling document counts as wrong. R_fail rows that are not in R_loc are left out. |
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
- **VOID runs.** If a validity line fails, the run is **VOID**: exit 4, the output holds only the validity lines and the counts, and no metric is presented as a result.
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

So a predictor that never claims a location or names a cause cannot pass: S1 and S3 are not evaluable. Nor can it be killed: K1 and K2 do not fire. Its milestone is reported as "not evaluable: no claims", which is a failure to deliver, not a pass.

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
| S1 | success | location_precision_line (point), min_n 10 | = 1.0 | Zero wrong located claims, over at least 10 claims. A wrong line is the diagnostics analogue of a FALSE-READY (perfection over speed). |
| S2 | success | location_recall_line (point) | ≥ 0.50 | |
| S3 | success | cause_precision_top1 (point), min_n 10 | = 1.0 | Zero wrong named causes, over at least 10. The owner may prefer ≥ 0.95. |
| S4 | success | cause_recall_top1 (point) | ≥ 0.80 | |
| K1 | kill | location_precision_line (point), min_n 10 | < 0.90 | Fires: the route that produced the claims is retired. |
| K2 | kill | cause_precision_top1 (point), min_n 10 | < 0.90 | Fires: the route is retired. |

The block below is machine-readable. The scorer reads it **from HEAD**, and it is the authority if it ever differs from the table. The owner fixes the lines by changing `"status"` to `"FIXED"` (with any value changes) in a commit of their own.

<!-- P2-LINES:BEGIN -->
```json
{
 "status": "PROPOSED",
 "definitions": "p2-defs/3",
 "lines": [
  {"id": "V0", "kind": "validity", "metric": "excluded.at_record", "stat": "n", "op": "==", "value": 0},
  {"id": "V1", "kind": "validity", "metric": "inputs.fails", "stat": "n", "op": ">=", "value": 20},
  {"id": "V2", "kind": "validity", "metric": "excluded.disagrees_with_record", "stat": "n", "op": "==", "value": 0},
  {"id": "V3", "kind": "validity", "metric": "excluded.ungraded", "stat": "n", "op": "==", "value": 0},
  {"id": "V4", "kind": "validity", "metric": "excluded.location_unverified", "stat": "n", "op": "<=", "value": 3},
  {"id": "V5", "kind": "validity", "metric": "excluded.cause_inconsistent", "stat": "n", "op": "<=", "value": 2},
  {"id": "V6", "kind": "validity", "metric": "inputs.cause_scored", "stat": "n", "op": ">=", "value": 20},
  {"id": "V7", "kind": "validity", "metric": "inputs.location_scored", "stat": "n", "op": ">=", "value": 15},
  {"id": "P1", "kind": "prediction", "metric": "location_recall_line", "stat": "point", "op": "<=", "value": 0.10},
  {"id": "S1", "kind": "success", "metric": "location_precision_line", "stat": "point", "op": "==", "value": 1.0, "min_n": 10},
  {"id": "S2", "kind": "success", "metric": "location_recall_line", "stat": "point", "op": ">=", "value": 0.50},
  {"id": "S3", "kind": "success", "metric": "cause_precision_top1", "stat": "point", "op": "==", "value": 1.0, "min_n": 10},
  {"id": "S4", "kind": "success", "metric": "cause_recall_top1", "stat": "point", "op": ">=", "value": 0.80},
  {"id": "K1", "kind": "kill", "metric": "location_precision_line", "stat": "point", "op": "<", "value": 0.90, "min_n": 10},
  {"id": "K2", "kind": "kill", "metric": "cause_precision_top1", "stat": "point", "op": "<", "value": 0.90, "min_n": 10}
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
