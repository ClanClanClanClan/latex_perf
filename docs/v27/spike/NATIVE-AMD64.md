# Spike E3: native amd64 confirmation of the H.1/H.2 x86_64 evidence

**Decision:** owner decision E3 of [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md)
(2026-09-30: a one-off GitHub Actions job is approved; "go" on 2026-10-02). Ledger OPEN-123.
**Run:** <https://github.com/ClanClanClanClan/latex_perf/actions/runs/36980556818> (2026-10-02,
workflow [`spike-native-amd64.yml`](../../../.github/workflows/spike-native-amd64.yml), commit
`6b5be1d1`). The committed native outcomes are this run's artifact
`native-amd64-outcomes`.
**Why:** every x86_64 result of spike H.1 and H.2 was produced by the amd64 binary under
qemu-user emulation on an arm64 Mac (H1-report.md §5.4, H2-report.md "Configurations").

**Verdict: CONFIRMS, with two qemu rows of H.2 REFUTED.** On a native x86_64 host the pinned
amd64 binary reproduces, byte for byte, every committed outcome of every H.1 architecture probe
(33 documents and their controls), the H.1 adversarial `rot2.tex`, the H.1 §3 format run, the
H.2 INITEX evidence, and 176 of the 178 inputs of the H.2 differential's binary side. The two
others, `t205` and `t208`, are the two inputs where the committed amd64 row recorded qemu
hanging (killed after 900 s, rc 137, with a qemu core file): natively the amd64 binary dies with
SIGSEGV, rc 139, at once, exactly as the native arm64 binary does, with terminal output,
standard error and log byte-identical to the qemu run's. That is correction C-112. No H.1
divergence between the architectures and no H.2 class (IDENTICAL/STUCK/LIMIT) changes.

Evidence tags as in H1-report.md: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## 1. The host [M]

From the run's own records ([`native-amd64/native/env/`](native-amd64/native/env/)):
- `uname -m` = `x86_64`, kernel `6.17.0-1022-azure`, CPU `AMD EPYC 9V74 80-Core Processor`
  (a GitHub-hosted Azure VM: hardware virtualisation, not instruction emulation);
- no binfmt_misc handler matches x86_64 ELF executables (the job checks every enabled handler
  for qemu with an x86_64 name or an ELF magic with `e_machine` 0x3e at offset 0, and fails if one
  exists; the registered handlers were `llvm-16/17/18-runtime.binfmt` and `python3.12`);
- inside the container, `uname -m` = `x86_64` and `pdftex` hashes to `1c5ff71156ee990c…`, the
  pinned amd64 binary (H1-report.md §1);
- the image is the digest `_oracle.py` reads from `tex-oracle.yml`
  (`texlive/texlive@sha256:4984977c…`, asserted equal to `_oracle.FINGERPRINTED_IMAGE`);
- `kernel.core_pattern` was set from systemd-coredump to `core`, the value on the qemu runs' host
  (colima's VM, MEASURED there), so a crashing run dumps core into its working directory on both.

## 2. The harness: the same scripts, checked by hash [M]

The job writes the scripts the committed qemu outcomes were produced with and checks each
against its recorded sha256 before running it (`native-amd64/native/env/harness-sha256.txt`: 10 of 10 OK):

| script | sha256 | recorded in | runs |
|---|---|---|---|
| `run-r.sh` | `91b42cf5…` | the qemu run directory `~/.cache/lp-spike-h1/archsem/probes/r-{arm64,amd64}/run.sh` | the round-2 set, `probes/out/r-*.out` |
| `run-qs.sh` | `bbce7ca0…` | `h1/recipes.md` (its block for the probes' run.sh) | `nh-intmin`, `nh-strings` (`q-*.out`, `s-*.out`) |
| `run2.sh` | `8f374495…` | `h1/recipes.md` | `slant*` (`t-*.out`) |
| `run-lead.sh` | `7bc156c3…` | `h1/recipes.md` (its block for the leaders' run.sh) | `probes/lead/` (`lead-*.out`) |
| `run-rot.sh` | `6192d620…` | the qemu run directory `~/.cache/lp-spike-h1/fmar1/rot/run.sh` | `h1/adversarial/rot2.tex` (H1-report.md §5.3) |
| `f7amd.sh` | `af70f5eb…` | `h1/recipes.md` | the format run of H1-report.md §3 |
| `run_bin.zsh` | `8e016ab3…` | `h2/diff/README.md` | the H.2 differential's binary side |
| `run_realclock.zsh` | `dfe0cb7f…` | `h2/diff/README.md` | the INITEX run's real-clock control |
| `clockshim-amd64.so` | `360d4706…` | `h2/evidence/inirun/run.json` | the `gettimeofday` shim (committed here as the binary that ran) |
| `intmin.tex` | `2ef8346d…` | the qemu run directory (both architectures) | the round-2 `intmin` line of `r-*.out` |

Two facts about the committed recipes, found while doing this [M]:
- `h1/recipes.md` gives `run.sh` `bbce7ca0…` for the round-2 probes; the `r` set was in fact run
  with an earlier version, `91b42cf5…`, which always passes `-halt-on-error` (the later one omits
  it for `nh-*` documents). The `r` set has no `nh-*` document, so the two behave identically on
  it; the job uses the script that ran.
- `r-*.out` has an `intmin` line from `intmin.tex`, which round 2 replaced by `nh-intmin.tex` and
  did not commit. It is committed here (`native-amd64/intmin.tex`) so that line can be re-run.

Invocations: those of `h1/recipes.md` and `h2/diff/README.md`
(`docker run --rm --platform linux/amd64 -v DIR:/w IMAGE sh -c 'uname -m; sh /w/run.sh'`, the
`RC=` trailer, `run_bin.zsh amd64 WORK SHIMDIR` after `diff.py prepare --arch amd64`). The qemu
H.2 run had a watchdog killing any container older than 900 s; the job has the same one
(`native-amd64/native/watchdog.log`: no kill).

## 3. How native was compared with qemu [M]

[`native-amd64/manifest.py`](native-amd64/manifest.py) hashes every file each run wrote.
It was run over the raw qemu run directories the spike left in `~/.cache/lp-spike-h1/`, giving
[`qemu-amd64-manifest.json`](native-amd64/qemu-amd64-manifest.json), and by the job over the
native ones. [`native-amd64/compare.py`](native-amd64/compare.py) compares them per probe: exit
status, every output file's sha256 (core dumps excluded: the host's core handler writes them,
not pdfTeX), the terminal summaries against the committed `h1/archsem/probes/out/*-amd64.out`,
the three committed full logs, the committed `h2/diff/results-amd64.tsv` row by row, and the
committed `h2/evidence/inirun/ref-*amd64*` files.

Checks on the comparison itself:
- **The raw qemu runs are the committed ones**: the qemu manifest reproduces every committed
  `*-amd64.out` byte for byte and all 178 rows of `results-amd64.tsv` (rc, stdout sha256 prefix,
  files, clock readings) and the INITEX files: 0 BASELINE mismatches.
- **Kill-test**: the comparator, given the raw native **arm64** runs as if they were the native
  amd64 side, reports REFUTES for every documented architecture difference (`imgwide`, `intmin`,
  `jpgconv`, `jpgdiv`, `matnan`, `snapy0`, `nh-intmin` and its log, `slanthuge` and its log,
  `slantnan`, the four `lead-*-x`, `rot2.pdf`, and `t205`/`t208`) and for the five terminal
  summaries (their first line is `uname -m`), and CONFIRMS every control, `nh-strings` and the
  other 176 H.2 inputs (the four real-clock ones under the `date` mask). Its `f7amd` row also
  said REFUTES, because the arm64 format run is a different script with different files: not a
  like-for-like input, so it tests nothing there.
- **Two declared masks, used only where stated**: `date` (the INITEX banner's date and a
  `[Y/M/D/T]` message) only for the four H.2 inputs whose run identity leaves pdfTeX on the real
  clock (`env-fsd01`, `env-fsd-empty`, `env-fsd-unset`, `env-sde-unset`; H2-report.md
  checkpoint 3); `coreline` (coreutils `timeout`'s "dumped core" message) for the H.1 probes. The
  `coreline` mask was **not needed**: every H.1 terminal file is byte-identical unmasked.

## 4. Results, per probe [M]

Per-probe rows with every hash: [`native-amd64/native/compare.tsv`](native-amd64/native/compare.tsv).
"rc" is the exit status (136 = SIGFPE, 139 = SIGSEGV, 137 = SIGKILL).

### H.1 architecture probes (H1-report.md §5.4; `h1/archsem/probes/`)

| document | what it probes | qemu rc | native rc | outputs | verdict |
|---|---|---|---|---|---|
| `snapy0` | `\pdfsnapy 0pt`, division (`gap_amount`) | 136 | 136 | all identical | CONFIRMS |
| `snapy1` | control | 0 | 0 | all identical | CONFIRMS |
| `imgwide` | 40000×8 px JPEG, conversion (`ext_xn_over_d`) | 0 | 0 | `\wd` = −32768pt; all identical | CONFIRMS |
| `jpgconv` | Exif resolution 2·10⁹/cm, conversion | 1 | 1 | all identical | CONFIRMS |
| `jpgdiv` | Exif INT_MIN / −1, division | 136 | 136 | all identical | CONFIRMS |
| `jpgctrl`, `jpgbig`, `jpgconvneg` | controls | 0, 0, 1 | 0, 0, 1 | all identical | CONFIRMS |
| `intmin` (round 2) | INT_MIN arithmetic | 1 | 1 | `[divself=1]`; all identical | CONFIRMS |
| `nh-intmin` | `x_over_n` and 21 other INT_MIN operations | 1 | 1 | `[divself=1]`; log = committed `nh-intmin.amd64.log` | CONFIRMS |
| `matnan` | `\pdfsetmatrix{nan 0 0 1}`, conversion | 0 | 0 | `/Rect [32645.579 …]`; PDF identical | CONFIRMS |
| `pdfboxinf`, `pdfboxnan` | included PDF with ∞ / ∞ − ∞ box | 0, 1 | 0, 1 | all identical | CONFIRMS |
| `slanthuge` | map line `1e30 SlantFont` | 0 | 0 | no warning; PDF `163a7ecf…`; log = committed `slanthuge.amd64.log` | CONFIRMS |
| `slantnan`, `slantctl` | `nan SlantFont`; control | 0, 0 | 0, 0 | PDFs `15f4f158…`, `75fc6b02…` | CONFIRMS |
| `nh-strings` | `char` signedness, 255-byte string sweep | 0 | 0 | log = committed `b513a15e…` | CONFIRMS |
| `lead-{hdvi,vdvi,hpdf,vpdf}-x` | `\xleaders` over a 2³¹−2 sp glue, the four leaders divisions | 136 ×4 | 136 ×4 | all identical | CONFIRMS |
| `lead-*-xctl`, `lead-*-a`, `lead-*-c` | controls (`\maxdimen`, `\leaders`, `\cleaders`) | 0 ×12 | 0 ×12 | all identical | CONFIRMS |
| the five terminal summaries `r`, `q`, `s`, `t`, `lead` `-amd64.out` | | | | byte-identical to the committed files | CONFIRMS |

### H.1 §5.3 and §3

| run | qemu | native | verdict |
|---|---|---|---|
| `rot2.tex` (160 `\rotatebox`es, 400,000 links; the FMA channel) | rc 0, PDF `043e4ebc…` | rc 0, PDF `043e4ebc…`; `.log`, `.aux`, terminal identical | CONFIRMS: the one-byte `/Rect` difference from aarch64's `c84b12a6…` is not an emulation artefact |
| `f7amd.sh`: INITEX of `pdflatex.fmt` at the amd64 build's own minute, and at the aarch64 build's | `5a9dfc4e…` (= shipped amd64), `a476533c…` (= shipped aarch64) | the same two hashes; every file identical | CONFIRMS: the format's architecture independence (C-100) holds natively |

### H.2 (H2-report.md checkpoint 3; `h2/diff/`, `h2/evidence/inirun/`)

| set | inputs | CONFIRMS | REFUTES |
|---|---|---|---|
| review A's graded inputs | 153 | 151 | 2 (`t205`, `t208`) |
| deep-recursion inputs (`deep5000`, `deep20000`, `deep28000`) | 3 | 3 | 0 |
| the INITEX run `t0` | 1 | 1 | 0 |
| checkpoint-3 regressions (`clk-*`, `env-*`, `kpse-*`) | 21 | 21 (4 of them under the `date` mask) | 0 |
| **all** | **178** | **176** | **2** |
| `h2/evidence/inirun/ref-amd64.*` (rc, stdout, stderr, `texput.log`, `clock.log`) | | byte-identical | |
| `h2/evidence/inirun/ref-realclock-amd64.*` (rc, stdout, `texput.log`) | | byte-identical | |

**The two REFUTES.** `t205` and `t208` (gen6 documents where `finiteshrink` prints to a log that
is not open; the model is Stuck there: "type: write to a non-file"):
- committed amd64 (qemu): rc 137, the container killed by the watchdog after 900 s, and a file
  `qemu_pdftex_….core` in the run's directory, which the committed row lists among the binary's
  output files;
- native amd64: rc 139 (SIGSEGV) at once, a kernel `core` file; stdout, stderr and `texput.log`
  byte-identical to the qemu run's;
- native arm64 (committed `results-arm64.tsv`): rc 139, a `core` file.

So the amd64 binary does not hang there: it crashes as the arm64 binary does, and qemu did not
deliver the fault. The committed `results-amd64.tsv` rows for these two inputs describe the
emulator, not the binary (C-112). The H.2 class is STUCK either way, and H2-report.md labelled
the 137 as qemu's; what it implied, a behavioural difference between the architectures at these
two inputs, does not exist natively.

## 5. What this does and does not settle

Settled natively [M]: every committed x86_64 outcome of the H.1 architecture probes, the H.1
adversarial PDF, the §3 format runs, and the H.2 binary side, as listed above. Since the native
binary's outputs equal the qemu binary's byte for byte on 176 inputs, the H.2 model's IDENTICAL
rows in the x86_64 configuration stand against the native binary too [I: transitivity of byte
equality; the model was not re-run].

Not re-run natively, so still qemu-only:
- H.1 §5.2's corpus comparisons (200 real papers, 489 evidence documents, 40 `\tracingall`
  traces): they run through `_oracle.py` on a local corpus that is not in the repository;
- H.1's gdb reach traces (`h1/archsem/reach_trace/`): x86_64 was traced through qemu-user's
  gdbstub, and the trace needs the unstripped reference build, which is not committed;
- H.1 §2.3's x86_64 rebuild of the binary (byte-identical to the pinned one under emulation).

**The runner is one CPU model** (AMD EPYC 9V74). glibc's x86_64 libm selects some functions by
CPU feature at load time (H1-report.md §5.1): only PDF-side code calls libm, and no probe here
showed a difference, but a different x86_64 CPU is not covered [I].

## 6. Files

`native-amd64/`: `manifest.py`, `compare.py`, `qemu-amd64-manifest.json` (the qemu baseline),
`clockshim-amd64.so`, `intmin.tex`, and `native/` (from the run's artifact
`native-amd64-outcomes`): `native-amd64-manifest.json`, `compare.tsv`, `compare-summary.txt`, the
five terminal summaries, `rot-amd.rc`, `f7amd.log`, `bin-amd64.log`, `realclock-amd64.log`,
`watchdog.log` and `env/` (host, image, binfmt, core pattern, harness hashes).
Re-check: `python3 docs/v27/spike/native-amd64/compare.py --native docs/v27/spike/native-amd64/native/native-amd64-manifest.json`.
