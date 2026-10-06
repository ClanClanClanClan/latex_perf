# The H.2 differential: the extracted model against the pinned binary

Review A of spike H.2 (2026-09-30) ran 153 INITEX inputs through the extracted model and the
pinned binary. This directory is that harness, committed and rerunnable: the seed of H.4's. The
report is [`../../H2-report.md`](../../H2-report.md) (checkpoint 3).

| path | what it is |
|---|---|
| `inputs/NAME.tex` | the terminal bytes `pdftex -ini` reads on standard input, unchanged |
| `inputs/NAME.spec` | optional: how this input's run identity differs from `base.spec` (`env N=V`, `unenv N`, `kpse N=V`, `clock SEC USEC`, and the file-system lines `fsfile`/`fsexists`/`fslist`/`fsdir`/`fsabsent`, which replace base.spec's line for the same path) |
| `inputs/NAME.files/` | optional (boundary step): the files of the run's working directory (`/w`); without it the working directory is empty |
| `base.spec` | the run identity every input shares: the command line C main was measured with, the environment the modelled externals read, kpathsea's values (from `../evidence/inirun/kpsevars.txt`, and the boundary step's gdb reading), kpathsea's format table (`kfmt`), the file-system snapshot of the TeX tree the searches reach (`fs*` lines; `@sha256:` bytes are copied out of the image by `snapshot.py`, and an `arm64:`/`amd64:` prefix marks one architecture's image), eight `gettimeofday` readings |
| `snapshot.py` | (boundary step) measures file-system snapshot entries in the pinned image with `test` and GNU `find`, and copies out bytes; never starts a TeX engine |
| `snapgrow.py` | (boundary step) grows a run's snapshot from the model's own questions: runs the model under `../../h3/tools/capped.sh`, measures the one path it was Stuck on, repeats |
| `gen/gen5.py`, `gen/gen6.py` | review A's random-document generators (verbatim but for the output path); `inputs/e100`–`e123` are `gen5.py 100 124`, `inputs/t200`–`t211` are `gen6.py 200 212` |
| `diff.py` | `prepare` (per input: the model's SPEC and the binary's environment), `model` (runs `ps.exe`), `compare` (classifies, writes `results-ARCH.tsv`) |
| `clockshim.c`, `clockshim-build.sh` | the `LD_PRELOAD` `gettimeofday` that gives the binary the run's clock readings, and how its two `.so` files were built (in `ubuntu:22.04`, gcc 11.4.0 and its x86_64 cross compiler; sha256 `981f50cb…` arm64, `360d4706…` amd64) |
| `results-arm64.tsv`, `results-amd64.tsv` | one row per input: class, the binary's rc, the model's result or Stuck reason, sha256 prefixes of the binary's outputs, the clock readings it used, the `ps.exe` that ran |

**Inputs (178).** Review A's 153 graded inputs and the three deep-recursion inputs it ran
without grading (`deep5000`, `deep20000`, `deep28000`), the INITEX run `t0` (`\relax`), and 21
regressions added at checkpoint 3: `clk-*` (`\pdfrandomseed`, the deviates, `\pdfelapsedtime`,
`\pdfresettimer`, a clock with too few readings, a `tv_sec` beyond 2038), `env-*`
(`FORCE_SOURCE_DATE` = `01`, empty, unset; `SOURCE_DATE_EPOCH` = empty, ` 1788076260`,
`+1788076260`, `1788076260x`, `-1`, unset, `0000000000`, 20 nines, 2⁵⁵) and `kpse-*` (`atoi` of
`70abc`, `  20`, `-5`, `99999999999`).

**Boundary step (2026-10-06, `../../H-boundary-report.md`): 28 inputs.** `kp-*` (23): `\input` of a file in the working
directory (with and without `.tex`, a name without extension, nested, CR/LF line ends, case-folded, absolute,
`./`, `../` (Stuck), `$` (Stuck), `~` (Stuck)), a missing file (retyped, end of file, `.sty`), `\openin`/`\read`
of a working-directory file and of a TeX-tree file found through ls-R (`story`), a missing `\openin`,
`\openout` with `openout_any=p` (accepted, an absolute name refused, a dot file refused) and `\input` of a
file the run wrote (Stuck). `tf-*` (5): `\font` of cmr10 and five other Computer Modern fonts at sizes, an
`\hbox` of them under `\showbox`, a `.tfm` name, a working-directory TFM that shadows the tree's, and a
missing font (Stuck: `mktextfm`). Their binary side runs with a container-local working directory
(`run_bin_local.zsh` below): a macOS bind mount is case-insensitive, the snapshot's working directory is not.

**Rerun.** The model side (writes only under WORK):

```sh
python3 diff.py prepare --arch arm64 --work WORK      # and amd64
python3 diff.py model --arch arm64 --work WORK --ps ~/.cache/lp-spike-h1/h2/run/build/ps.exe --jobs 4
```

The binary side starts the engine, which this repository's `check_oracle_pin.py` allows only
inside `scripts/tools/_oracle.py`; `_oracle.py` has no terminal input, no architecture choice and
no clock shim. So it is not committed as an executable: it is this recipe, run as the file
`run_bin.zsh` (sha256 `8e016ab3…`) with the two shim `.so` files in SHIMDIR, as
`run_bin.zsh arm64 WORK SHIMDIR` and `run_bin.zsh amd64 WORK SHIMDIR` (amd64 runs under qemu-user
emulation on an arm64 host):

```zsh
#!/bin/zsh
# The binary side of the H.2 differential (docs/v27/spike/h2/diff/README.md quotes this
# file verbatim). usage: run_bin.zsh ARCH WORK SHIMDIR [NAME...]
# WORK is the directory `diff.py prepare --arch ARCH --work WORK` wrote; SHIMDIR holds
# clockshim-ARCH.so built from diff/clockshim.c. For each input: WORK/NAME/bin/{out,err,rc}
# and the files the run wrote, in WORK/NAME/bin/w/ (clock.log: the clock readings used).
set -u
A=$1; WORK=$2; SHIM=$3; shift 3
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
names=($@); [ ${#names} -eq 0 ] && names=(${(f)"$(<$WORK/inputs.txt)"})
for n in $names; do
  d=$WORK/$n; rm -rf $d/bin; mkdir -p $d/bin/w
  envs=(); for l in ${(f)"$(<$d/docker.env)"}; do envs+=(-e "$l"); done
  docker run --rm -i --platform linux/$A --network none -v $SHIM:/shim:ro -v $d/bin/w:/w -w /w \
    -e LD_PRELOAD=/shim/clockshim-$A.so -e LP_CLOCK_LOG=/w/clock.log $envs \
    $IMG pdftex -ini < $d/stdin > $d/bin/out 2> $d/bin/err
  echo $? > $d/bin/rc
  echo "$n rc=$(<$d/bin/rc)"
done
```

The real-clock control of the INITEX run (no shim; `run_realclock.zsh ARCH WORK`, sha256
`dfe0cb7f…`) gave the same terminal output and log as the shimmed run on both architectures:

```zsh
#!/bin/zsh
# The real-clock control of the INITEX run (docs/v27/spike/h2/diff/README.md quotes this
# file verbatim): input t0 with no clock shim, so gettimeofday is the real clock.
# usage: run_realclock.zsh ARCH WORK
set -u
A=$1; WORK=$2
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
d=$WORK/t0; rm -rf $d/realclock; mkdir -p $d/realclock/w
docker run --rm -i --platform linux/$A --network none -v $d/realclock/w:/w -w /w \
  -e SOURCE_DATE_EPOCH=1788076260 -e FORCE_SOURCE_DATE=1 \
  $IMG pdftex -ini < $d/stdin > $d/realclock/out 2> $d/realclock/err
echo $? > $d/realclock/rc
echo "t0 real clock $A rc=$(<$d/realclock/rc)"
```

The boundary inputs (`kp-*`, `tf-*`) run their binary side with this recipe, `run_bin_local.zsh ARCH WORK
SHIMDIR NAME...` (sha256 `b5a87f27…`):

```zsh
#!/bin/zsh
# The binary side of the boundary inputs (docs/v27/spike/h2/diff/README.md quotes this file
# verbatim). usage: run_bin_local.zsh ARCH WORK SHIMDIR [NAME...]
# As run_bin.zsh, but the working directory is container-local (a tmpfs at /w, case-
# sensitive like the model's snapshot; a macOS bind mount is case-insensitive), holding a
# copy of WORK/NAME/cwd/ (the input's files) when the engine starts; afterwards /w is copied
# out to WORK/NAME/bin/w/. The clock shim is preloaded into the engine only. Output: WORK/NAME/bin/{out,err,rc}, WORK/NAME/bin/w/.
set -u
A=$1; WORK=$2; SHIM=$3; shift 3
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
names=($@); [ ${#names} -eq 0 ] && names=(${(f)"$(<$WORK/inputs.txt)"})
for n in $names; do
  d=$WORK/$n; rm -rf $d/bin; mkdir -p $d/bin/w
  envs=(); for l in ${(f)"$(<$d/docker.env)"}; do envs+=(-e "$l"); done
  docker run --rm -i --platform linux/$A --network none -v $SHIM:/shim:ro -v $d/cwd:/in:ro \
    -v $d/bin:/out --tmpfs /w -w /w -e SHIMSO=/shim/clockshim-$A.so -e LP_CLOCK_LOG=/w/clock.log $envs \
    $IMG sh -c 'cp -R /in/. /w/ && LD_PRELOAD=$SHIMSO pdftex -ini; rc=$?; cp -R /w/. /out/w/; exit $rc' \
    < $d/stdin > $d/bin/out 2> $d/bin/err
  echo $? > $d/bin/rc
  echo "$n rc=$(<$d/bin/rc)"
done
```

The `cm-*` inputs (checkpoint 3), whose spec gives its own `argv0`/`argv` lines, run with `run_bin_argv.zsh ARCH WORK SHIMDIR NAME...` (sha256 `a78a8092…`). The command comes from the `argv.txt` that `diff.py prepare` writes:

```zsh
#!/bin/zsh
# The binary side of the inputs with a command line of their own (docs/v27/spike/h2/diff/README.md
# quotes this file verbatim). usage: run_bin_argv.zsh ARCH WORK SHIMDIR [NAME...]
# As run_bin_local.zsh (a container-local working directory holding WORK/NAME/cwd/), but the
# command is WORK/NAME/argv.txt (argv[0], then one argument per line, as diff.py prepare
# wrote it from the input's spec), run by name from the image's PATH.
set -u
A=$1; WORK=$2; SHIM=$3; shift 3
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
names=($@); [ ${#names} -eq 0 ] && names=(${(f)"$(<$WORK/inputs.txt)"})
for n in $names; do
  d=$WORK/$n; rm -rf $d/bin; mkdir -p $d/bin/w
  envs=(); for l in ${(f)"$(<$d/docker.env)"}; do envs+=(-e "$l"); done
  cmd=(${(f)"$(<$d/argv.txt)"})
  docker run --rm -i --platform linux/$A --network none -v $SHIM:/shim:ro -v $d/cwd:/in:ro \
    -v $d/bin:/out --tmpfs /w -w /w -e SHIMSO=/shim/clockshim-$A.so -e LP_CLOCK_LOG=/w/clock.log $envs \
    $IMG sh -c 'cp -R /in/. /w/ && LD_PRELOAD=$SHIMSO "$@"; rc=$?; cp -R /w/. /out/w/; exit $rc' sh $cmd \
    < $d/stdin > $d/bin/out 2> $d/bin/err
  echo $? > $d/bin/rc
  echo "$n rc=$(<$d/bin/rc)"
done
```

`compare` leaves out of the binary's files the input files the run did not change.

Then `python3 diff.py compare --arch ARCH --work WORK --write`.

**Classes.** IDENTICAL: the model exits with the binary's status, and its terminal output,
standard error, every file it wrote and the number of clock readings it used are byte-identical
to the binary's. STUCK: the model is Stuck (outside the tier); the reason is recorded. LIMIT: the
model hit the 900 s time-out or a resource limit: no result. DIVERGENT: the model exited and
something differs.
