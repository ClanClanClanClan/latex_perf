# Spike H.1, review round 4 (MEDIUM-2): does each DIVERGES probe reach its site?

Round 3's DIVERGES verdicts tied a probe to a site by hand: `classify.py` copied the probe name
from the `argued` column, and `verify_h1.py` checked only that the probe's recorded outcomes
differ between the architectures. Moving `snapy0` to another site left `verify_h1.py` OK
(reproduced: mutation M1 below, on the HEAD version). This directory replaces the hand link with
a measurement: every probe document runs under gdb on both architectures, with a breakpoint on
every DIV/F2I instruction of every candidate site.

## What is measured [M]

- **Candidate sites**: the 18 rows of `../classification.tsv` whose `argued` column is DIVERGES.
  The candidates come from the argued column, not from the verdict, because the verdict is now
  computed from this trace.
- **Breakpoints**: `site_addrs.py` repeats `census.py`'s scan of the two `objdump -d -l`
  listings (`~/.cache/lp-spike-h1/archsem/{arm64,amd64}.dis`, sha256 `878f2fa9…`, `87995834…`)
  and keeps each instruction's address. It asserts that the rows are exactly
  `census_insns.tsv.gz`'s rows for those sites. Result: `site_addrs.tsv`, 20 aarch64 and 19
  x86_64 instructions. Six sites have instructions on one architecture only, because the two
  compilers attribute the same C operation to different lines: `pdftex0.c:1363`, `1371`
  (x86_64), `1365`, `1370` (aarch64), and `utils.c:405` (x86_64), `406` (aarch64). gdb's own
  line table names `utils.c:405` for both aarch64 instructions that objdump puts on line 406.
  This is why breakpoints are set on addresses, not on lines.
- **Per hit** (`trace_gdb.py`): the instruction runs, and the script reads its operands. An
  **edge** operand is one at which the two ISAs answer differently. For DIV: a divisor of 0 or
  −1, or an INT_MIN dividend or divisor. For F2I: a NaN source, or one outside
  (−2147483649, 2147483648). For each conversion, the source is cross-checked against the
  result read at the next instruction. A hit whose source does not explain its result fails
  `build_trace.py`, and there are 0 such hits.
- **Documents**: all 32 committed probe documents (`../probes/*.tex`, `../probes/lead/*.tex`),
  controls included. They run exactly as `../../recipes.md` runs them: `-halt-on-error
  -interaction=nonstopmode` (the `nh-*` documents without `-halt-on-error`), `SOURCE_DATE_EPOCH=1788076260
  FORCE_SOURCE_DATE=1`, stdin `/dev/null`, every `*.jpg`/`*.pdf` beside the document. The
  engine is the unstripped reference build, mounted at `/usr/local/texlive/2026/bin/ref/pdftex`
  in the pinned image:
  - aarch64: `~/.cache/lp-spike-h1/b-arm64/…/pdftex`, sha256 `b23c26d6…`, which strips to the
    pinned `cee621bf…`;
  - x86_64: `b-amd64/…/pdftex`, sha256 `78c49dad…`.
- **rc**: for every document on both architectures, the rc under the trace equals the rc
  recorded in `../probes/out/` (`build_trace.py` checks it). Every x86_64 SIGFPE was taken AT the
  site's own `idiv` (the `fault` column). On aarch64 the rc is gdb's exit code. On x86_64 it is
  the shell's `$?` for the traced engine (`raw/amd64/shellrc.tsv`), because gdb learns no exit
  signal through qemu-user's gdbstub. Wherever gdb did learn an exit code, it equals the
  shell's.

## Result

`reach_trace.tsv` has 960 rows, one per (document, candidate site, architecture with
instructions). The verdicts in `../classification.tsv` follow from these rows (`classify.py`).
Each cell gives hits and edge hits as hits/edge:

| site | probe | aarch64 | x86_64 | verdict |
|---|---|---|---|---|
| pdftex0.c:1363 | nh-intmin | (no instruction) | 6/6, dividend INT_MIN | DIVERGES |
| pdftex0.c:1365 | nh-intmin | **0/0** | (no instruction) | **PS-STUCK**: never executed |
| pdftex0.c:1370 | nh-intmin | 6/6, dividend INT_MIN | (no instruction) | DIVERGES |
| pdftex0.c:1371 | nh-intmin | (no instruction) | 6/6 | DIVERGES |
| pdftex0.c:18140, 18511, 24311, 24739 | lead-{hdvi,vdvi,hpdf,vpdf}-x | 1/1, divisor 0 | 1/1, divisor 0, SIGFPE at the site | DIVERGES |
| pdftex0.c:23709 | snapy0 | 1/1, divisor 0 | 1/1, divisor 0, SIGFPE at the site | DIVERGES |
| writejpg.c:218 | jpgdiv | 1/1, INT_MIN / −1 | 1/1, INT_MIN / −1, SIGFPE at the site | DIVERGES |
| writejpg.c:222 | jpgdiv | **0/0** | **0/0** | **OPEN**: never executed |
| writejpg.c:236 | jpgconv | 1/1, source 5.08e9 | 1/1, source 5.08e9 | DIVERGES |
| writejpg.c:237 | jpgconv | 1/**0** | 1/**0** | **OPEN**: in-range source only |
| mapfile.c:487 | slanthuge | 1815/1, source ≈1e33 | 1815/1 | DIVERGES |
| utils.c:1496 | matnan | 8/8, NaN and 3.3e305 | 8/8 | DIVERGES |
| utils.c:1497 | matnan | 8/4, NaN | 8/4, NaN | DIVERGES |
| utils.c:405 | imgwide | (no instruction) | 4/1, source 2.63e9 | DIVERGES |
| utils.c:406 | imgwide | 2/1, source 2.63e9 | (no instruction) | DIVERGES |

The controls make shared sites visible as shared:
- `lead-*-xctl` executes its x site once on both architectures, with no edge operand.
- `snapy1` executes `23709` once, with no edge operand.
- Six documents execute `mapfile.c:487`, 1,814 or 1,815 times each on both architectures:
  `nh-intmin`, `slantctl`, `slanthuge`, `slantnan`, `snapy0` and `snapy1`. Only `slanthuge`
  and `slantnan` (NaN) give it an edge operand.
- `jpgctrl` and `jpgbig` execute `writejpg.c:218`, `236` and `237`, with no edge operand.
- `jpgconvneg` gives `236` an edge operand on both architectures, and its rc is 1 on both.
- `lead-*-a` and `lead-*-c` execute none of the four x sites.

So reaching a site is not evidence on its own. The verdict needs the edge operand.

**What this does and does not show.** For the six SIGFPE probes, the trace links probe, site
and outcome directly: x86_64 dies at the site's own instruction, with the edge operand in its
registers. For the value divergences (`nh-intmin`, `jpgconv`, `slanthuge`, `matnan`,
`imgwide`), the trace shows that the probe drives the site with an edge operand, and the
recorded outputs differ. That the edge value at this site *causes* the recorded difference is
still [I]: for example, `matnan`'s `/Rect` comes from `do_matrixtransform`'s result. A site
with instructions on only one architecture is confirmed on that architecture only.

## How it was run (reference copies, not run from the repo)

These scripts start a TeX engine outside `scripts/tools/_oracle.py`, so, as in `../../recipes.md`,
they are kept as documentation only. Their sources are in `~/.cache/lp-spike-h1/reach-gdb/`.
`trace_gdb.py`, `site_addrs.py` and `build_trace.py` in this directory start nothing.

### img/Dockerfile (sha256 `150975d89cdc69543e0f554aa8b60460bcf9abe54c2ade54b743f017704193f1`)

Built as `lp-spike-gdb:multiarch` for `linux/arm64`: image id `sha256:3bade143…`, with Debian
`gdb` and `gdb-multiarch` 17.2-1+b1.

```
FROM texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
RUN apt-get update >/dev/null 2>&1 && apt-get install -y --no-install-recommends gdb-multiarch gdb binutils >/dev/null 2>&1 && gdb-multiarch --version | head -1
```

### run-arm64.sh (sha256 `204633c8192bf48199c1f2a37e4da07965d7268d9612ab078ca0fc15ed2ef155`)

```sh
# runs inside lp-spike-gdb:multiarch (linux/arm64); /d = probe documents (ro),
# /t = reach_trace (ro), /w = work; reference build at /usr/local/texlive/2026/bin/ref/pdftex
set -u
cd /w; mkdir -p res
uname -m; sha256sum /usr/local/texlive/2026/bin/ref/pdftex
for t in /d/*.tex /d/lead/*.tex; do b=$(basename $t); f=${b%.tex}
  H=-halt-on-error; case $f in nh-*) H=;; esac
  rm -rf o-$f; mkdir o-$f; cp $t o-$f/; cp /d/*.jpg /d/*.pdf o-$f/ 2>/dev/null
  (cd o-$f && SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 timeout 600 gdb -batch -nx \
     -x /t/trace_gdb.py -ex 'set pagination off' \
     -ex "starti $H -interaction=nonstopmode $b </dev/null >term.txt 2>&1" \
     -ex "python install('/t/site_addrs.tsv', 'arm64')" \
     -ex continue -ex 'python stopped()' -ex continue \
     -ex "python dump('/w/res/$f.json')" \
     --args /usr/local/texlive/2026/bin/ref/pdftex > /w/res/$f.gdb.log 2>&1; echo "$f gdbrc=$?")
  grep -ohE '^!.*|\[[a-zA-Z0-9=-]+=[^]]*\]|too (large|small)[^.]*|number too big|invalid[^.]*' o-$f/term.txt | tr '\n' ' ' | cut -c1-300 | sed 's/^/   /'; echo
done
```

Invocation (in `~/.cache/lp-spike-h1/reach-gdb/`, `T` = this repository's `docs/v27/spike/h1/archsem`):

```sh
docker run --rm --name lp-reach-arm64 --platform linux/arm64 --cap-add SYS_PTRACE -v $PWD/w-arm64:/w -v $T/probes:/d:ro -v $T/reach_trace:/t:ro -v ~/.cache/lp-spike-h1/b-arm64/repo/Work/texk/web2c/pdftex:/usr/local/texlive/2026/bin/ref/pdftex:ro -v $PWD/run-arm64.sh:/run.sh:ro lp-spike-gdb:multiarch sh /run.sh > run-arm64.out 2>&1
```

### run-amd64.sh (sha256 `facd0c920128063e3ea57c1b36bf9b931bd7e2685757b508ca9239297082cb79`)

ptrace-based gdb does not work under qemu-user, so x86_64 uses qemu-user's gdbstub instead.
The colima VM's `/usr/bin/qemu-x86_64` (7.0.0) is registered through binfmt_misc with flags
`POCF`. With `QEMU_GDB=1234` in the environment of the exec, qemu waits for a debugger before
the first guest instruction. `gdb-multiarch` attaches from an arm64 container that shares the
amd64 container's network namespace.

```sh
#!/bin/sh
# host-side driver (macOS, colima). A = amd64 container of the pinned image (qemu-user via binfmt),
# reference build mounted at bin/ref; B = arm64 lp-spike-gdb:multiarch in A's network namespace.
# Each document: A runs the engine with QEMU_GDB=1234 (qemu-user waits for a debugger before the
# first instruction; QEMU_UNSET_ENV keeps both variables out of the guest environment), B attaches
# gdb-multiarch, runs trace_gdb.py, and the engine runs to its end.
set -u
R=$HOME/.cache/lp-spike-h1/reach-gdb; T=$1; W=$R/w-amd64
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
REF=$HOME/.cache/lp-spike-h1/b-amd64/repo/Work/texk/web2c/pdftex
rm -rf $W; mkdir -p $W/res
docker run -d --name lp-reach-amd64 --platform linux/amd64 -v $W:/w -v $T/probes:/d:ro -v $REF:/usr/local/texlive/2026/bin/ref/pdftex:ro $IMG sleep 86400 >/dev/null
docker run -d --name lp-reach-gdbx --platform linux/arm64 --network container:lp-reach-amd64 -v $W:/w -v $T/reach_trace:/t:ro -v $REF:/sym/pdftex:ro lp-spike-gdb:multiarch sleep 86400 >/dev/null
docker exec lp-reach-amd64 sh -c 'uname -m; sha256sum /usr/local/texlive/2026/bin/ref/pdftex'
for t in $T/probes/*.tex $T/probes/lead/*.tex; do b=$(basename $t); f=${b%.tex}; d=/d; case $t in */lead/*) d=/d/lead;; esac
  H=-halt-on-error; case $f in nh-*) H=;; esac
  docker exec lp-reach-amd64 sh -c "rm -rf /w/o-$f; mkdir /w/o-$f; cp $d/$b /w/o-$f/; cp /d/*.jpg /d/*.pdf /w/o-$f/ 2>/dev/null; true"
  docker exec -d lp-reach-amd64 sh -c "cd /w/o-$f && SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 timeout 900 env QEMU_GDB=1234 QEMU_UNSET_ENV=QEMU_GDB,QEMU_UNSET_ENV /usr/local/texlive/2026/bin/ref/pdftex $H -interaction=nonstopmode $b </dev/null >term.txt 2>&1; echo \$? > rc"
  docker exec lp-reach-gdbx sh -c "n=0; until grep -q ':04D2 00000000:0000 0A' /proc/net/tcp; do n=\$((n+1)); [ \$n -gt 300 ] && { echo NOPORT; exit 9; }; sleep 0.2; done
    cd /w/o-$f && timeout 900 gdb-multiarch -batch -nx -x /t/trace_gdb.py -ex 'set pagination off' -ex 'set sysroot /nonexistent' \
      -ex 'set auto-solib-add off' -ex 'file /sym/pdftex' -ex 'target remote 127.0.0.1:1234' \
      -ex \"python install('/t/site_addrs.tsv', 'amd64')\" -ex continue -ex 'python stopped()' -ex continue \
      -ex \"python dump('/w/res/$f.json')\" > /w/res/$f.gdb.log 2>&1; echo $f gdbrc=\$?"
  n=0; until [ -s $W/o-$f/rc ]; do n=$((n+1)); [ $n -gt 600 ] && break; sleep 1; done
  echo "$f shellrc=$(cat $W/o-$f/rc 2>/dev/null)"
  grep -ohE '^!.*|\[[a-zA-Z0-9=-]+=[^]]*\]|too (large|small)[^.]*|number too big|invalid[^.]*' $W/o-$f/term.txt | tr '\n' ' ' | cut -c1-300 | sed 's/^/   /'; echo
done
docker rm -f lp-reach-gdbx lp-reach-amd64 >/dev/null
```

Invocation: `sh run-amd64.sh $T > run-amd64.out 2>&1`.

### Collecting the result

```sh
cp w-arm64/res/*.json w-arm64/res/*.gdb.log $T/reach_trace/raw/arm64/; cp run-arm64.out $T/reach_trace/raw/arm64/run.out
cp w-amd64/res/*.json w-amd64/res/*.gdb.log $T/reach_trace/raw/amd64/; cp run-amd64.out $T/reach_trace/raw/amd64/run.out
# raw/amd64/shellrc.tsv: the `<doc> shellrc=<n>` lines of run-amd64.out, as doc<TAB>rc
python3 $T/reach_trace/build_trace.py      # writes reach_trace.tsv; then (cd $T && python3 classify.py)
```

## Defects met on the way (disclosed)

1. **An x86_64 run that traced the wrong process.** The first x86_64 driver wrapped the engine
   as `QEMU_GDB=1234 … timeout 900 pdftex`. The stub then belonged to `timeout`, and gdb never
   saw `pdftex`. The symptoms: every breakpoint failed its placement check ("Cannot access
   memory"), and the SIGFPE was `timeout` re-raising its child's signal. That data was
   discarded. The driver now runs `timeout 900 env QEMU_GDB=1234 … pdftex`. `build_trace.py`
   refuses a raw file with fewer breakpoints than `site_addrs.tsv` has.
2. **qemu-user 7.0's gdbstub swaps the two halves of an xmm register.** gdb shows the scalar
   double in `v2_double[1]`. Reading `v2_double[0]` gave 0 edge hits for every x86_64
   conversion. Fix: each conversion's source is now matched against the result read at the next
   instruction (both lanes are candidates on x86_64, lane 0 tried first). Of the 10,927 x86_64
   conversion hits, lane 0 fails to explain the result in 10,926, and lane 1 explains it. In 1
   hit lane 0 explains it, and possibly lane 1 too, which counts as consistent only when both
   agree on edge or not. No hit is unexplained (`lanes` and `inconsistent` in the raw JSON). On
   aarch64, native gdb's scalar lane explains all 10,931 hits.
3. **One transient emulator failure.** In the second x86_64 run, `jpgbig` ended with rc 139
   (SIGSEGV) and no gdb log: the debugger side never attached. The recorded rc is 0. In the
   final run (the committed one), `jpgbig` gives rc 0 like every other document, and its gdb
   log is complete.
4. aarch64 gdb warns "Error disabling address space randomization" (the container has no
   `personality` permission). It does not matter here: every breakpoint is set at
   `symbol + offset` after `starti`, and its mnemonic is checked there.

## Files

| path | what it is |
|---|---|
| `site_addrs.py`, `site_addrs.tsv` | candidate-site instruction addresses, checked against the census |
| `trace_gdb.py` | the gdb script: breakpoints, operand reads, the conversion cross-check, JSON output |
| `raw/<arch>/<doc>.json`, `<doc>.gdb.log`, `run.out` | raw output of the final runs (aarch64 2026-10-01, x86_64 2026-10-01) |
| `raw/amd64/shellrc.tsv` | the shell rc of each traced x86_64 engine |
| `build_trace.py`, `reach_trace.tsv` | the table `classify.py` and `verify_h1.py` read; `--check` rebuilds and compares |
