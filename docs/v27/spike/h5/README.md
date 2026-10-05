# Spike H.5, stage 1: the heap-design profile, its tools and its evidence

Report: [`../H5-heap-design.md`](../H5-heap-design.md). The profiling variants are never model
builds: they exist to measure. Heavy data lives in `~/.cache/lp-spike-h1/h5/`: `in/` holds the
inputs, `runs/` the runs, `sample/` the raw profiles.

| path | what it is |
|---|---|
| `tools/mkvariant.py` | `mkvariant.py ML_DIR OUT_DIR {prof\|t1\|t2}`: a profiling variant of an extracted tree (H.3 checkpoint 2: `~/.cache/lp-spike-h1/h3/cp2/build/ml`, tree `72b2ea79…`); every replacement is asserted |
| `tools/parrayc.ml` | coq-core 8.18.0's `Parray` with counters; `PS_PARRAY=linear` is the in-place, fail-closed mode (candidate A, measured) |
| `tools/prof.ml` | the GC probe at the C boundary (`PS_PROBE`, `PS_PROBE_DEEP`) |
| `tools/zr.ml` | the O(1) conversion realizers T1 and T2, as measured, with the `PS_T1CHECK` comparison hooks |
| `tools/build.sh` | compiles a variant tree in dependency order, as `../h2/pipeline.sh` does |
| `tools/run.sh` | one model run of a meaning-dump prefix under `../h3/tools/capped.sh` |
| `tools/cmp.sh` | `../h3/tools/meancompare.py` on a model run and the binary's run of the same prefix |
| `tools/selfprof.py`, `tools/callers.py` | macOS `sample` output grouped by cost class, and by nearest caller |
| `tools/summarize.py` | `evidence/runs.tsv` from the runs' last probe lines |
| `tools/t1test.ml` | the T1 realizers against the extracted Coq definitions, on boundary and random values (`evidence/t1test.txt`); built against a compiled `t1` tree: `ocamlfind ocamlopt -package zarith,coq-core.kernel -linkpkg -I $T $T/zr.cmx <the .cmx of Uint0, Sint0 and their dependencies, in ocamldep -sort order> t1test.ml` |
| `tools/abtable.py` | `evidence/abtest.tsv`: the interleaved timing rounds of `evidence/commands/abtest.sh`, median CPU per variant |
| `evidence/abtest.tsv`, `evidence/t1test.txt` | the timing medians of §3.2; the realizer test's result |
| `evidence/commands/` | the exact command lines of every run, and the queue logs |
| `evidence/runs.tsv` | every run: verdict, CPU, GC counters, array counters, comparison class |
| `evidence/probes/` | per run: the `PROBE` lines, the GC's exit statistics, the verdict and the footprint trace |
| `evidence/compare/` | `meancompare` JSON per compared run |
| `evidence/profile/` | the `sample` call trees (gzipped), their class summaries, the `-dcmm`/`-dlambda` excerpts |
| `evidence/binary-times.txt` | the pinned binary's CPU times (five runs per prefix) |
| `evidence/exe-sha256.txt` | the hashes of the model build and the three variants measured |

**Inputs:** `python3 docs/v27/spike/h3/tools/meanblock.py REPO ~/.cache/lp-spike-h1/h5/in/pN N`
(N = 0, 50, 250, 1000; all names without N, into `in/pall`). Each input directory also gets the
run identity of `~/.cache/lp-spike-h1/h3/cp2/mt50/spec`, which is
`h3/evidence/meanings/model.spec.template` with the format stream's local path filled in.

**Building a variant:**

```zsh
H5=~/.cache/lp-spike-h1/h5
python3 docs/v27/spike/h5/tools/mkvariant.py ~/.cache/lp-spike-h1/h3/cp2/build/ml $H5/prof-t2/ml t2
zsh docs/v27/spike/h5/tools/build.sh $H5/prof-t2/ml $H5/prof-t2/ps-t2.exe
```

The `tools/` scripts expect the run harness's files under `$H5/tools/` (`run.sh` calls
`../h3/tools/capped.sh` from the repository).

**Binary-side recipes.** They start the engine outside `_oracle.py`, so, as in H.1–H.3, they are
documentation, not committed scripts. P is a prefix directory under `$H5/in`. CLOCK is the spec's
clock readings, written `SEC.USEC,...`. SHIM is `~/.cache/lp-spike-h1/h2/diff/shim` (the clock
shim of `h2/diff/`).

```zsh
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
# CPU timing (evidence/binary-times.txt): five runs in one container, colima's native arm64 VM.
# The clock shim fakes the wall clock, so bash's `time` is read for user + sys only.
docker run --rm --platform linux/arm64 --network none -v $O/w:/w -w /w -v SHIM:/shim:ro \
  -e LD_PRELOAD=/shim/clockshim-arm64.so -e LP_CLOCK=CLOCK -e LP_CLOCK_LOG=/w/clock.log \
  -e SOURCE_DATE_EPOCH=0 -e FORCE_SOURCE_DATE=1 -e max_print_line=1000000 -e error_line=254 \
  -e half_error_line=238 -e openin_any=p -e openout_any=p $IMG \
  bash -c 'TIMEFORMAT="BINTIME real %R user %U sys %S"; for i in 1 2 3 4 5; do rm -f texput.*;
           time (pdftex -ini < /w/stdin > /w/out.$i 2>&1); done'      # /w/stdin = P/stdin-meanings
# the run meancompare.py reads (out, err, rc, w/): the h3/README.md meaning-dump recipe
docker run --rm -i --platform linux/arm64 --network none -v $O/w:/w -w /w -v SHIM:/shim:ro \
  -e LD_PRELOAD=/shim/clockshim-arm64.so -e LP_CLOCK=CLOCK -e LP_CLOCK_LOG=/w/clock.log \
  -e SOURCE_DATE_EPOCH=0 -e FORCE_SOURCE_DATE=1 -e max_print_line=1000000 -e error_line=254 \
  -e half_error_line=238 -e openin_any=p -e openout_any=p $IMG pdftex -ini < P/stdin-meanings > $O/out 2> $O/err
echo $? > $O/rc
```
