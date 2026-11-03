# P2 diagnostics baseline: pre-registration

Product track P2 ("exactly why": the cause of a failure, at source level, before compiling). The owner ruled it part of the core vision on 2026-10-21. Ledger: OPEN-138 (this baseline) and OPEN-139 (the seal outside the P2 tools), in `docs/v27/PROJECT_STATE.md`.

**Status: PROPOSED. Nothing has been scored.** The success, kill and validity lines in §7 are proposals for the owner. The scorer (`p2_baseline.py score`) refuses to run until the owner sets the lines block to `"status": "FIXED"`. Definitions version: **p2-defs/1** (`_p2_diag.DEFINITIONS_VERSION`; `check_p2_diag.py` checks that this document and the code agree).

Code: `scripts/tools/_p2_diag.py` (record, prediction, matching, metrics), `scripts/tools/_sample_seal.py` (the sample-3 refusal), `scripts/tools/p2_baseline.py` (producer and scorer), `scripts/tools/check_p2_diag.py` (unit tests). Where this document and the code disagree, that is a defect. Fix both, then bump the definitions version.

## 1. What is measured, and what is not

The oracle tells us where pdfTeX **detected** the first error: its message, its `l.N` and the input file it was reading. The baseline measures how often the CLI's `--compile-check` answer names that cause and that place **before compiling**. The oracle is only the ground truth we score against. Running it is never the product (memory: engine-in-the-loop is not a product).

The following are not measured here:
- **The location of the cause.** TeX reports where it noticed the error, which can come after the cause. For example, a missing `.sty` on line 3 is reported at `l.4`, and a runaway argument at end of file has no line at all; both are in the fixtures. The log does not contain the cause's location, so this baseline cannot score it.
- **Columns.**
- **Fix suggestions.**
- **Any error after the first.** Under `-halt-on-error` there is none.

## 2. Samples

- **Samples 1 and 2 only** (owner ruling 2026-10-21). Sample 1 is frame ranks 1–200 (offset 0); its grade of record is `corpora/real_roots/results.json`. Sample 2 is ranks 201–400 (offset 200); its grade of record is `corpora/real_roots/results_sample2.json`. The frame is the 2,719-paper frame ordered by `sha256(arxiv_id)`.
- **Sample 3 (ranks 721–920, offset 720) is SEALED (OPEN-119) and is never used.** Before this branch the seal was a convention, not a mechanism (C-180). Now `_sample_seal` refuses, and every P2 command calls it before opening the corpus, building an oracle or reading an artefact. It refuses:
  - the sample number 3, in any spelling;
  - any frame window that touches ranks 720–919;
  - any sealed document id, compared after normalising basename, case and version suffix;
  - any artefact whose name, symlink target, recorded frame or contained ids point at sample 3.

  If the seal set cannot be read, or does not hold exactly 200 ids, every request is refused. There is no bypass. `check_p2_diag.py` §8 tries to defeat each of these refusals. Tools outside P2 are still ungated (OPEN-139).
- **Neither sample is virgin.** Sample 1 has been tuned on and sample 2 has been seen during design. Reading their P2 records makes both design-seen for P2 as well. So a later P2 success measured on them is **in-sample**. Claiming it generalises needs an out-of-sample set that the owner designates (OPEN-138 (c)).
- **Size.** The scorer counts the oracle-failing rows; this document does not restate the count (one number, one artefact). The count is a few dozen across both samples, so every rate carries an exact one-sided 95% Clopper–Pearson bound. At this n a 0/n result still leaves an upper bound near 10%. V1 floors the input.

## 3. Ground truth: the oracle-side record (`_p2_diag.diag_record`)

**The run.** Each document is graded by the pinned oracle through `_oracle.get_oracle()`. The run uses the recorded protocol `diff_real_roots.run_to_fixpoint_full`: `-interaction=nonstopmode -halt-on-error`, pdflatex's default restricted shell-escape, up to 3 passes plus a confirming pass, and `PROTOCOL_CLOCK`. Each document runs in its own copy of the package tree, which is first checked against the grade of record's `sha256_tree`. The log read is the **last pass's** `<job>.log`.

**Compiles.** "Compiles" means rc 0 **and** a PDF, as in the grade of record. A row whose re-run rc or compiles value differs from the grade of record is excluded and counted (V2).

The record holds the following fields:

| Field | Definition |
|---|---|
| **first error** | The first block of the log that begins with `!`. pdfTeX's own final report line (`!  ==> Fatal error occurred, …`) does not count. The **message** is the block's first paragraph, in full. It is **not truncated**: the old `first_error` field stops at 160 characters. Message lines are un-wrapped at TeX's 79-byte hard wrap, using the oracle's own `_unwrap_log`. The help text after the first blank line is kept in `message_lines` but is not part of the message. |
| **context_pairs** | TeX's two-line context pairs, read from the **raw** lines. A pair's second line is padded to `error_line = 79`, and the help text follows it with no blank line in between (measured in the `long_line` fixture). Un-wrapping the whole log would therefore glue context to help text. |
| **l.N** | The first context line of the form `l.N …` at or after the first block. LaTeX's missing-file path prints a `\typeout` "! LaTeX Error: File … not found." followed by "! Emergency stop."; the `l.N` is in the second block. |
| **file stack** | The input files open when the first block starts, outermost first. It is built by a parenthesis parse of the un-wrapped log. Every `(` pushes: a file when the following name starts with `./`, `../` or `/` (or names a file in the tree), and a text marker otherwise. Every `)` pops. Two kinds of line print document text with unbalanced parentheses and are skipped: box dumps after `Overfull`/`Underfull` warnings, up to their blank line, and `Missing character:` lines. The skipped lines and any underflows are recorded. |
| **location** | `file` is the top stack frame as a path relative to the package root, or none when it is a TeX Live file. `frame` is `document`, `system` or `none`. `author_file` is the innermost frame that lies inside the tree. `line` is l.N. |
| **verified** | True when line N of `file` contains the text pdfTeX printed around the error point: before it (left-truncated `...` allowed) and after it (right-truncated `...` and a trailing `^^M` allowed). `^^xx` and `^^c` are decoded, and trailing spaces and the end-of-line character are stripped, as pdfTeX does. A location that fails this check is **excluded**, not guessed (V4). |
| **consistent** | True when the first block is the error pdfTeX stopped on. That holds in two cases: there is exactly one `!` block, or there are two and they form the missing-file prompt followed by `Emergency stop` with "cannot \read from terminal". Any other extra block is text that a document or package printed. That is the C-99 forgery: a `\message{! …}` is measured in the `forged_message` fixture. An inconsistent row is excluded from cause and location scoring (V5). |
| **cause** | `(class, object)` of the first message, from the ordered table `CAUSE_RULES`, where the first match wins. The classes are listed after this table. The object is a file, environment, package, class or control sequence. Objects are normalised by `norm_object`: a file by basename, with `.tex`, `.sty` and `.cls` dropped; a package lower-cased, with `-` and `_` removed. For `undefined-cs`, the object is the control sequence at the end of the first context line. |

The cause classes are: `missing-file`, `undefined-cs`, `undefined-env`, `env-mismatch`, `missing-begin-document`, `command-already-defined`, `option-clash`, `encoding`, `engine-incompatible`, `brace-imbalance`, `left-right-imbalance`, `math-mode`, `alignment`, `tex-capacity`, `package-error`, `class-error`, `latex-error`, `emergency-stop` and `other`.

**This is a diagnostic, not evidence (C-99).** No grade is decided from it. The `consistent` and `verified` checks are how a forged or unparseable record gets excluded.

## 4. The prediction: the CLI side (`_p2_diag.cli_prediction`)

### 4.1 The run

The CLI is built from the commit under test, and its build provenance is stamped in the artefact. It runs `validators_cli.exe --compile-check <toplevel>` with `L0_VALIDATORS=pilot`, which is the grade of record's setting. Both stdout and stderr are read; the file-not-found branch prints its reasons on stderr.

### 4.2 What counts as the prediction

Only the **frozen surface** counts: the lines before `TIER\t`, the same scope as `diff_real_roots.scrape_reasons`. The `TIER` and `why not strict:` lines name constructs that block a proof, not causes of an error, so they are not predictions.

The predictions are read in the order a user reads them:
1. the indented reasons under `NOT-READY`;
2. when the model rejects, the indented lines under `MODEL-CONNECTED`. In that case the `NOT-READY` line only points to them; the pointer line and the non-blocking duplicate-label advisory are not predictions.

**Top-1** is the first prediction.

### 4.3 Class of a prediction

| Reason | Class, object |
|---|---|
| `T5 rule violations: [ids]` | One prediction per id. DELIM-001/002 → `brace-imbalance`. DELIM-003/004/009/011 → `left-right-imbalance`. ENC-001/002/004/005/006/009/012/014 → `encoding`. Every other id → no class (it can never be cause-correct). |
| `structural-fatal … [parts]` | Each part names the TeX message it predicts (`…: ! Double superscript`). That message is classified with the same `CAUSE_RULES`. |
| `T2 … missing file P` | `missing-file`, object `P`. |
| `T3 … feature F …` (contract or model line) | `engine-incompatible`, object set = the packages for F (`FEATURE_PACKAGES`, e.g. `opentype_fonts` → `fontspec`). |
| `artefact-fatal (F): …` | `artefact`, file F. |
| `T0 …`, `T1 …`, `T2 cycle`, `T4 …`, `input too large`, other model lines | No class: the reason says NOT-READY without naming a cause that TeX would report. |

### 4.4 Location claims

A prediction claims a location when its text names a file and a line: `F:N`, or `in F` together with `(line N)`. As of v27.1.64 only LP-Foreign `T0` reasons do this, and they name a construct, not an error. A prediction that names only a file claims a file-level location.

## 5. Matching and metrics (`_p2_diag.cause_correct`, `location_correct`, `score_rows`)

### 5.1 Matching rules

- **Correct cause:** the classes are equal. When both sides name an object, the normalised objects must also be equal. For a T3 object set, the gold package must be in the set.
- **Correct location, line level:** the predicted file equals the gold top frame's tree path, after `normpath` and stripping a leading `./`, **and** the predicted line equals l.N **exactly**. No tolerance is pre-registered; an offset is wrong.
- **Correct location, file level:** the files are equal.

### 5.2 Metric sets

- **R_fail:** graded, agreeing rows where the oracle fails.
- **R_cause:** the rows of R_fail with a consistent record and a classified cause.
- **R_loc:** the rows of R_cause whose gold location has a line, lies in the document tree (not a system frame) and is **verified**.

### 5.3 Metrics

Each metric is reported as k, n, and the one-sided 95% lower and upper bounds.

| Metric | k / n |
|---|---|
| `cause_recall_top1` | R_cause rows where the CLI says NOT-READY and top-1 is cause-correct / \|R_cause\| |
| `cause_recall_any` | the same with any prediction instead of top-1 (secondary) |
| `cause_precision_top1` | correct / every row whose top-1 names a class. A class named on a **compiling** document counts as wrong. R_fail rows that are not in R_cause are left out. |
| `location_precision_line` | line-correct / every row whose top-1 claims a (file, line). A claim on a compiling document counts as wrong. R_fail rows that are not in R_loc are left out. |
| `location_recall_line` | R_loc rows where top-1 is line-correct / \|R_loc\| |
| `location_recall_file` | R_loc rows where top-1 is file-correct / \|R_loc\| (secondary) |

Recall counts a READY answer on a failing document as a miss. That answer is a FALSE-READY, which is graded elsewhere; here it simply gives no cause.

### 5.4 Exclusions

Every exclusion is counted and printed beside the results:
- ungraded rows (a timeout on either side; under load this means a rerun, not a verdict);
- rows that disagree with the grade of record;
- rows missing from the corpus, whose tree differs, or that contain online-only (Dropbox dataless) files. These are checked **before** any read, since a read triggers a download;
- for cause scoring: no error block, an inconsistent record, an unclassified record;
- for location scoring: no l.N, a system top frame, an unverified location.

## 6. Procedure (stage 2; not run on this branch)

Stage 2 starts only after Track B writes `~/.cache/lp-track-B/LANES_DONE` and the owner fixes the lines in §7. Track B holds the oracle containers first; at most 2 run at once across the machine.

```
python3 scripts/tools/p2_baseline.py record --sample 1 --corpus-root "$LP_REAL_CORPUS" --out corpora/p2_baseline/diag_sample1.json
python3 scripts/tools/p2_baseline.py record --sample 2 --corpus-root "$LP_REAL_CORPUS" --out corpora/p2_baseline/diag_sample2.json
python3 scripts/tools/p2_baseline.py score --records corpora/p2_baseline/diag_sample1.json corpora/p2_baseline/diag_sample2.json --out corpora/p2_baseline/score.json
```

- **Provenance.** Each `record` stamps a `RunStamp` before its first engine run. The stamp covers the oracle core plus `p2_baseline.py`, `_p2_diag.py`, `_sample_seal.py` and `diff_real_roots.py`. The command refuses to write if that grading code changed during the run.
- **Grading blobs.** `_oracle.py` and `diff_real_roots.py` are not modified, so every recorded grade's `grading_code` (blobs 6b4ce94e and 9859cccf) still names this tree's code. `check_p2_diag.py` §9 asserts this for samples 1–2. `check_oracle_platforms.py` (blob 3c666fe3) is not touched either.

## 7. Lines (PROPOSED: for the owner to fix)

The lines come in four kinds:
- **Validity:** if one fails, the run is void and is reported as a failed run, not a score.
- **Prediction:** pre-registered expectations about the baseline. They are reported, not pass/fail.
- **Success:** the target for the P2 deliverable. It is measured later under the same definitions; **the baseline itself is not judged against it.**
- **Kill:** retires the P2 design route measured at that milestone, never the goal. A KILL line "holds" when it fires.

All values below are proposals.

| id | kind | metric | test | proposal and rationale |
|---|---|---|---|---|
| V1 | validity | inputs.fails | ≥ 20 | Below 20 failing rows the bounds say nothing; report counts only. |
| V2 | validity | excluded.disagrees_with_record | = 0 | Same oracle, same clock, same tree: any disagreement means the instrument is not the grade of record. |
| V3 | validity | excluded.ungraded | = 0 | A timeout is a rerun (COMMON rules), not a datum. |
| V4 | validity | excluded.location_unverified | ≤ 3 | Above roughly 10% of R_fail, the log parser, not the CLI, is what is being measured. |
| V5 | validity | excluded.cause_inconsistent | ≤ 2 | More would mean forged or multi-error logs are common enough to need their own design. |
| P1 | prediction | location_recall_line (point) | ≤ 0.10 | The v27.1.64 CLI prints no error lines (§4.4), so the baseline sits at the zero point. |
| S1 | success | location_precision_line (point) | = 1.0 | Zero wrong located claims. A wrong line is the diagnostics analogue of a FALSE-READY (perfection over speed). |
| S1n | success | location_precision_line (n) | ≥ 10 | S1 must rest on claims that were actually made. |
| S2 | success | location_recall_line (point) | ≥ 0.50 | |
| S3 | success | cause_precision_top1 (point) | = 1.0 | Zero wrong named causes. The owner may prefer ≥ 0.95. |
| S4 | success | cause_recall_top1 (point) | ≥ 0.80 | |
| K1 | kill | location_precision_line (point) | < 0.90 | Fires: the route that produced the claims is retired. |
| K2 | kill | cause_precision_top1 (point) | < 0.90 | Fires: the route is retired. |

The block below is machine-readable. The scorer reads it, and it is the authority if it ever differs from the table. The owner fixes the lines by changing `"status"` to `"FIXED"` (with any value changes) in a commit of their own.

<!-- P2-LINES:BEGIN -->
```json
{
 "status": "PROPOSED",
 "definitions": "p2-defs/1",
 "lines": [
  {"id": "V1", "kind": "validity", "metric": "inputs.fails", "stat": "n", "op": ">=", "value": 20},
  {"id": "V2", "kind": "validity", "metric": "excluded.disagrees_with_record", "stat": "n", "op": "==", "value": 0},
  {"id": "V3", "kind": "validity", "metric": "excluded.ungraded", "stat": "n", "op": "==", "value": 0},
  {"id": "V4", "kind": "validity", "metric": "excluded.location_unverified", "stat": "n", "op": "<=", "value": 3},
  {"id": "V5", "kind": "validity", "metric": "excluded.cause_inconsistent", "stat": "n", "op": "<=", "value": 2},
  {"id": "P1", "kind": "prediction", "metric": "location_recall_line", "stat": "point", "op": "<=", "value": 0.10},
  {"id": "S1", "kind": "success", "metric": "location_precision_line", "stat": "point", "op": "==", "value": 1.0},
  {"id": "S1n", "kind": "success", "metric": "location_precision_line", "stat": "n", "op": ">=", "value": 10},
  {"id": "S2", "kind": "success", "metric": "location_recall_line", "stat": "point", "op": ">=", "value": 0.50},
  {"id": "S3", "kind": "success", "metric": "cause_precision_top1", "stat": "point", "op": "==", "value": 1.0},
  {"id": "S4", "kind": "success", "metric": "cause_recall_top1", "stat": "point", "op": ">=", "value": 0.80},
  {"id": "K1", "kind": "kill", "metric": "location_precision_line", "stat": "point", "op": "<", "value": 0.90},
  {"id": "K2", "kind": "kill", "metric": "cause_precision_top1", "stat": "point", "op": "<", "value": 0.90}
 ]
}
```
<!-- P2-LINES:END -->

## 8. Threats to validity

- **Forged log text (C-99).** Mitigated by excluding records that fail the `consistent` and `verified` checks. A forgery that passes both checks would also have to reproduce the source line, which is possible only for text the document itself contains.
- **Parser bias.** The parenthesis parse and the context reader are heuristics over pdfTeX's output, and they are tested only on the shapes in the fixtures. Fixtures were produced on the laptop TeX Live (the same pdfTeX build as the pin), not on the oracle. The first stage-2 run should be read for V4/V5 counts before any score is read.
- **79-byte ambiguity.** A line of exactly 79 bytes can be a wrap or a full line. Context is read raw (§3). Messages and the stack accept the oracle's convention.
- **Detection location versus cause location** (§1). The baseline scores TeX's detection point, by definition.
- **Small n, and in-sample reuse** (§2).

## 9. Amendments

Once the lines are FIXED, any change to a definition in §3–§5 or to a line needs three things: a new definitions version, the owner's sign-off, and the earlier version's results kept beside the new ones. Results are never re-scored silently under new definitions.
