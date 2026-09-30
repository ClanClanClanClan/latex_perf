# Spike H.1: committed evidence

This directory backs every number in [`../H1-report.md`](../H1-report.md), so that each can be
re-checked from the repository (review round 1 of the spike found that none could: all of it was
in `~/.cache/lp-spike-h1/`). Run the check with:

```
python3 docs/v27/spike/h1/verify_h1.py        # pure: no TeX, no docker; exit 1 on any mismatch
```

`verify_h1.py` recomputes the report's verdict counts from `diffs/r1/`. It also requires every
aarch64 FMA site outside xpdf in `fma/fma_sites_aarch64.tsv` to be named in the report's §5.1
classification, with its count. On the round-0 report it fails, with 27 failures; on this one it
passes.

| path | what it is |
|---|---|
| `diffs/r1/diff_*.json` | every comparison, re-run 2026-09-30 by `tools/h1diff.py` with the narrowed PDF mask (§4.1). These are the report's numbers |
| `diffs/r0/diff_*.json` | the round-0 comparison files, as the report first quoted them (the older names lack the second set). 13 of the 14 agree with their `r1` counterpart count for count (documents, verdicts, masks, rcs). The 14th is the superseded partial run below, which has no `r1` counterpart |
| `tools/h1diff.py` | the comparator (reads raw runs from `~/.cache/lp-spike-h1/runs/`; runs no engine) |
| `tools/h1diff_selftest.py` | kill-tests for the PDF canonical mask: 2 of 5 pass on the round-0 comparator; 6 of 12 on the round-1 one (review round 2 added 7: no Ghostscript intermediate, xref entry types, bytes after a zlib end, a predictor-encoded xref stream); 12 of 12 on this one (`python3 h1diff_selftest.py [path/to/h1diff.py]`) |
| `tools/window_2000_2199.json`, `tools/*_ids.json` | the 200 real papers (frame ranks 2000–2199), and the id lists of the 20-, 7- and 13-document subsets |
| `fma/fma_sites_aarch64.tsv` | all 524 FMA instructions of the aarch64 `pdftex`, as function, source line and instruction, from `objdump -d -l` of the unstripped build, whose stripped form is the pinned binary |
| `fma/fma_by_function.txt` | the same, counted per function |
| `fma/jbig2_exhaustive.py`, `fma/pdfversion_exhaustive.py` | exhaustive checks of the two TeX-state FMA sites with finite input ranges; outputs in `*.out` |
| `fma/lexsim.py`, `fma/lexmid.py` | xpdf's real-number parser, fused and unfused: a random sample and a targeted search. The channel stays open |
| `fma/matrix_search.py` | rounding flips at `do_matrixtransform`, the channel review round 1 reproduced |
| `adversarial/rot2.tex` | review round 1's document: its arm64 and amd64 PDFs differ in one byte (§5.3) |
| `amd64_crash_sites.txt` | the 16 emulator crash sites of the three failed amd64 builds, grepped from the build logs |
| `diffs/r2/diff_*.json` | every comparison re-run by the round-2 comparator (review round 2: the canonical PDF form engages only with a Ghostscript intermediate, decodes the xref stream row by row and keeps bytes after a zlib end). Counts identical to `r1`, which `verify_h1.py` checks |
| `fma/pdfversion_full.c`, `.out` | the PDF-version FMA site over pdfTeX's whole input range (major 1..2^31−1, minor 0..9), with a self-check against the Python transcription |
| `archsem/` | review round 2: every integer-division and float-to-int site of both binaries with a verdict, the `-fsigned-char` and `-fwrapv` function censuses, and the adversarial documents that make the architectures give different exit codes (report §5.4; [`archsem/README.md`](archsem/README.md)) |
| `recipes.md` | verbatim copies, with sha256, of the build recipe, the pdftex-only amd64 build, the INITEX format experiments, the FMA mapping and the run harness `h1cmp.py`. They are documentation, not executable files: several start TeX outside `_oracle.py`, which `check_oracle_pin.py` forbids for tracked code |

## Runs that are not counted in the report, all disclosed

The report's §5.2 lists each of these:

- `diffs/r0/diff_real-fixclock__arm64-pinned__vs__amd64-pinned.json` (01:26 UTC): a partial first
  cross-architecture comparison of 25 real papers, with 1 `DIFF_STDOUT_ONLY` (2507.07609v1). That
  one difference is the container mutation of report §6.1. It was superseded by the full
  200-document run, `diff_real-fixclock__amd64-pinned__vs__arm64-pinned.json` (02:58).
- `diffs/r1/diff_real-fixclock__amd64.after-mutation-pinned__…`: the 48 grades made in the mutated
  container. All were discarded and re-graded.
- `diffs/r1/diff_strict-fixclock__…`: an aborted full-evidence amd64 run, 53 documents. For time,
  it was replaced by every 8th document (`strict8`).
- `diffs/r1/diff_real13-fixclock-regrade__…`: the first re-grade of the 13 pre-guard documents. It
  ran in a work root of a different length and failed closed on 2 documents. It was repeated as
  `regrade2`.
- `~/.cache/lp-spike-h1/runs/real/amd64.protocolclock.aborted`: 4 documents, never compared.

## What stays only in the cache

The raw runs take 62 GB; the whole cache is 72 GB. No quoted number depends on them. They are
needed only to re-run the comparator on raw outputs, or for H.4 and H.6 to diff against these
grades. Also only in the cache:
- the source tarball (sha256 `0aa8c538…`, re-creatable with `git archive dc8efcd4`);
- the build trees;
- the full build logs.
