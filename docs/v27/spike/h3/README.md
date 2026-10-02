# Spike H.3: the format load, its evidence and its tools

Report: [`../H3-report.md`](../H3-report.md).

| path | what it is |
|---|---|
| `model.patch` | the model's changes since H.2 (`docs/v27/spike/h2/` at `0ab6005e`), as built and measured in H.3 (the format-file externals, the evaluation-order refinement, the memory fixes, the driver's `PS_MEMDIAG` and `PS_COMPACT` diagnostics); merged into `h2/` at the next checkpoint with a re-measurement of H.2's evidence |
| `tools/capped.sh` | runs a command under a physical-footprint cap and a wall-clock time-out, recording the footprint every poll |
| `tools/meandigest.py` | the contract generator's `meanings_sha256`, recomputed from the log of one meaning dump with the generator's own `parse_dump` |
| `tools/fmtdiff.py` | compares two decompressed format streams up to the string pool, then byte by byte |
| `evidence/roundtrip/` | the round trip's run identity (template), the model's and the binary's terminal output and `texput.log`, and the shipped-vs-round-trip comparison |
| `evidence/memory/` | `curve.tsv` (prefixes of the meaning dump, per build: verdict, live words at exit, peak major heap, load) and the largest heap blocks of two runs |

**Binary-side recipes** (they start the engine outside `_oracle.py`, so they are documentation;
WORK holds `stdin` and, for the meanings, `stdin-meanings`; SHIM the clock shim of `h2/diff/`;
CLOCK is the spec's clock readings as `SEC.USEC,...`):

```zsh
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
# the round trip: pdftex -ini, first line "&pdflatex \dump"
docker run --rm -i --platform linux/arm64 --network none -v WORK/b1/w:/w -w /w -v SHIM:/shim:ro \
  -e LD_PRELOAD=/shim/clockshim-arm64.so -e LP_CLOCK=CLOCK -e LP_CLOCK_LOG=/w/clock.log \
  -e SOURCE_DATE_EPOCH=1788076260 -e FORCE_SOURCE_DATE=1 $IMG pdftex -ini < WORK/stdin > WORK/b1/out 2> WORK/b1/err
# the meaning dump: "&pdflatex", the generator's dump_block, \csname @@end\endcsname
docker run --rm -i --platform linux/arm64 --network none -v WORK/b2/w:/w -w /w -v SHIM:/shim:ro \
  -e LD_PRELOAD=/shim/clockshim-arm64.so -e LP_CLOCK=CLOCK -e LP_CLOCK_LOG=/w/clock.log \
  -e SOURCE_DATE_EPOCH=0 -e FORCE_SOURCE_DATE=1 -e max_print_line=1000000 -e error_line=254 \
  -e half_error_line=238 -e openin_any=p -e openout_any=p $IMG pdftex -ini < WORK/stdin-meanings > WORK/b2/out 2> WORK/b2/err
# the format, and kpathsea's answer for it
docker run --rm --platform linux/arm64 --network none -v WORK/w:/w $IMG sh -c \
  'cp $(kpsewhich -engine=pdftex -progname=pdftex -format=fmt pdflatex.fmt) /w/shipped.fmt'
```
