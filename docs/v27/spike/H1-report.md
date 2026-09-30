# Foundation spike, step H.1: the pinned pdfTeX's source revision, reproduced

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123),
step H.1 of the ADR-014 draft §9.
**Dates:** begun 2026-09-29 by a session that an API limit cut off; resumed and completed on
2026-09-30 from that session's transcripts and the build trees it left on disk.
**Kill criterion (H.1):** the revision cannot be identified **and** no revision reproduces the logs.

**Verdict: the kill criterion did not fire.** The revision is identified by three independent
sources. The aarch64 rebuild is byte-identical to the pinned binary. The shipped format is
reproducible byte for byte. On every document run, the two architectures' pinned binaries gave
the same results.

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## 0. Results at a glance

| question | answer | tag |
|---|---|---|
| Which source built the pinned `pdftex`? | TeX Live svn **r78081**, i.e. TeX-Live/texlive-source commit `dc8efcd41054ec4bf7f96c022cd2d91fe346f6e1` (tag `svn78081`, 2026-02-23T16:24:02Z) | M |
| Is the image's binary the upstream build of that source? | yes, for both architectures: byte-identical to the `svn78081` GitHub release assets | M |
| Does our rebuild reproduce it? | **aarch64: yes, byte for byte** (sha256 `cee621bf…`). amd64: not rebuilt, see §2.3 | M |
| Is `pdflatex.fmt` reproducible? | **yes, byte for byte**, given the INITEX run's clock; and it does not depend on the architecture (the ADR-014 draft's F7 was wrong: C-100) | M |
| Same binary, same inputs: same outputs? | yes: 3,907 of 3,907 evidence documents, and 200 of 200 real papers once the real clock is fixed | M |
| Do amd64 and arm64 differ (floating point)? | no difference observed: 489 of 489 evidence documents and 200 of 200 real papers agree, and so do the \tracingall logs of the traced runs that completed (§5). The code has one channel that could differ in principle, bounded in §5.1 | M + R + I |

## 1. The pinned engine

The oracle image is `texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b`,
a multi-architecture index with `linux/arm64` (`010653c0…`) and `linux/amd64` (`c268e1c3…`) [M].
In both: Debian forky/sid, glibc 2.43, `pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026)`,
kpathsea 6.4.2, libpng 1.6.55, zlib 1.3.2, xpdf 4.06. The binary links dynamically only to
`libm.so.6` and `libc.so.6` [M].

| | aarch64 | x86_64 |
|---|---|---|
| `bin/<arch>/pdftex` size, sha256 | 2,838,616, `cee621bf5fc41d15d44c0d00a837af5267a8a0f5170f5406da44fcee44d01459` | 2,405,736, `1c5ff71156ee990c3a18402cf06d3671ecf748bd84fb3983dbd5d62b600bc40b` |
| tlpdb package | `pdftex.aarch64-linux` r78082 | `pdftex.x86_64-linux` r78082 |
| `.comment` (compiler) | `GCC: (Debian 10.2.1-6) 10.2.1 20210110` | `GCC: (GNU) 8.5.0 20210514 (Red Hat 8.5.0-28)`, `GCC: (GNU) 11.2.1 20220127 (Red Hat 11.2.1-9)` |
| highest glibc symbol version | 2.29 | 2.14 |
| FMA instructions (`objdump -d`) | 524 | 0 |
| `pdflatex.fmt` sha256 (3,658,242 bytes each) | `a476533c…` (dumped 2026-08-30 07:51 UTC) | `5a9dfc4e…` (dumped 06:10 UTC) |

## 2. Identifying the revision and rebuilding it

### 2.1 Three independent identifications [M]

1. **tlpdb.** Both architecture packages of `pdftex` are at revision 78082 in the image's
   `texlive.tlpdb`.
2. **TeX Live's history.** The git mirror of the TeX Live svn (`git.texlive.info`) logs the last
   change to `Master/bin/{aarch64,x86_64}-linux/pdftex` as "2026-02-23 tl26 r78081 gh binaries -
   synctex, pdftex, xdvipsk" (Karl Berry). r78082 is the commit that installed binaries built
   from r78081.
3. **The binaries themselves.** The GitHub release `svn78081` of TeX-Live/texlive-source
   ("r78081 - synctex, pdftex png", published 2026-02-23T16:25:17Z) carries per-architecture
   tarballs with recorded digests. `texlive-bin-aarch64-linux.tar.gz` (sha256 `2d42f6fd…`) and
   `texlive-bin-x86_64-linux.tar.gz` (`be0841ce…`) matched those digests. **Their `pdftex` files
   have exactly the image's sha256** (`cee621bf…` and `1c5ff711…`).

The tag `svn78081` is commit `dc8efcd4…` (git-svn-id `trunk/Build/source@78081`; tree
`88f434867eb7da270b614cd115a129e07b6721c3`). The source used for the rebuild is `git archive` of
that commit: 617,021,440 bytes, sha256 `0aa8c538e491476c32d633606238b4458ecd74311730a2d81370cc75ad298cfd`.
In it, `pdftex.web` is 40,334 lines, sha256 `38537f10300d66d7…`, and `tex.web` has sha256
`c62ab513ef167e93…`.

**The ADR-014 draft read its sources from TeX Live trunk, not r78081.** On 2026-09-29, 10 of the
11 files it cites were byte-identical to r78081 (measured by the first H.1 session; the draft's
copies were lost with the scratchpad, and the two hashes above re-verify `pdftex.web` and
`tex.web`). The exception is **`tex.ch`**: trunk's differs from r78081's in 43 diff lines. Trunk
commit `637c7de4` (2026-06-19, "disallow recursive \input, by no longer ignoring \relax at the
beginning of an \input file") changed how `scan_file_name` treats `\relax`, so on that point the
pinned binary behaves as r78081 says, not as the draft read it (re-verified 2026-09-30 against
trunk's current `tex.ch`). **The spike translates r78081.**

### 2.2 The aarch64 rebuild: byte-identical [M]

The recipe mirrors TeX Live's own CI at that tag (`.github/scripts/build-tl.sh` and
`.github/workflows/main.yml` of `svn78081`), restricted to what pdfTeX needs:

- **Image:** `arm64v8/debian:bullseye`, the image upstream uses for aarch64.
- **Packages:** apt pinned to `snapshot.debian.org` at `20260223T160000Z`, the day of the
  upstream build. `libc6`/`libc-bin` were downgraded to 2.31-13+deb11u13 and `perl-base` to
  5.32.1-4+deb11u4, the versions of that snapshot. Toolchain: gcc 10.2.1-6, binutils 2.35.2-2.
- **Build:** `./Build -C --disable-all-pkgs --enable-web2c --enable-pdftex --enable-arm-neon=on`,
  with `CXXFLAGS=-std=c++17 -O2` and `TL_MAKE_FLAGS=-j 4`.

The build finished with 98 executables. Its `pdftex` is 2,838,616 bytes with sha256
**`cee621bf5fc41d15d44c0d00a837af5267a8a0f5170f5406da44fcee44d01459`, the pinned binary's**.
The unstripped link output (`Work/texk/web2c/pdftex`, 7,136,272 bytes) strips to the same sha256.
So its symbol table describes the pinned binary exactly, and §5.1 uses it.

**How pdfTeX is configured in this build [R]:**
- `INTEGER_TYPE` is C `int` (32 bits). `w2c/config.h` selects `INTEGER_IS_INT` when `long` is
  wider than 4 bytes, "to share format files".
- `GLUERATIO_TYPE` is `double` (`texmfmp.h`).
- C flags are autoconf's default `-g -O2` (TeX Live's CI sets none), plus `-Wimplicit
  -Wreturn-type`.
- There is no `-ffp-contract` flag. GCC's default for GNU C is `fast`, so the compiler may fuse
  `a*b+c` into one FMA instruction. It does on aarch64 (§5.1).

### 2.3 amd64: not rebuilt, and why that is deferred [M]

Upstream builds x86_64 on `almalinux:8` with `gcc-toolset-11`, on a native amd64 GitHub runner.
This host is arm64. Colima here runs amd64 containers through qemu-user binfmt emulation
(`vmType: vz`, `rosetta: false`), and the VM is shared with other work, so its configuration was
not changed.

Two attempts were made:
- **First attempt (2026-09-29):** it failed in `texk/kpathsea` with `Segmentation fault (core
  dumped)` from `gcc` compiling `rm-suffix.c`, a trivial file.
- **Second attempt (2026-09-30):** same flags, with automatic resumes. It crashed at seven more
  unrelated points:
  - `cc1` segfaults on `lj_api.c`, `cairo-device.c`, gmp's `toom32_mul.c` and mpfr's `set.c`;
  - `configure: error: cannot run C compiled programs` in freetype2 and in harfbuzz;
  - one crash left gmp half-built, which deadlocked a plain `make` resume, so the resume order
    had to be forced.

**Diagnosis: emulator instability, not a source or toolchain defect.** The crash sites are
unrelated and do not repeat. The upstream build of the same commit succeeds. The first attempt's
toolchain matched the binary's `.comment` (gcc-toolset-11 11.2.1-9).

**Status at the time of writing:** a third, resumed attempt was still building (five resumes so far, each after an emulator crash). Its outcome is recorded in §2.4 if it finishes.

**Decision (recorded; the owner may override):**
- Do not pursue a byte rebuild of amd64 under emulation.
- The amd64 binary's identity already rests on the release-asset digest (§2.1).
- A byte rebuild belongs on a native amd64 host: a CI runner, `almalinux:8`, with the package set
  pinned to the build date, which the vault supports.
- The spike's next steps (H.2–H.6) are specified for one architecture at a time, and aarch64 is
  the one whose binary is now reproduced.

The behavioural cross-architecture question does not need the rebuild; §5 answers it with the
pinned amd64 binary itself.

## 3. The format file: reproducible, and architecture-independent (C-100) [M]

Inside the pinned image, INITEX was re-run with the command recorded in `fmtutil.cnf`
(`pdftex -ini -jobname=pdflatex -progname=pdflatex -translate-file=cp227.tcx *pdflatex.ini`).

| run | clock | result |
|---|---|---|
| aarch64, today's clock | real | differs from the shipped format in **7 bytes** of 11,621,149 (uncompressed). Offsets 974,183–974,186 are the date digits of the format identifier ("2026.8.30" against "2026.9.29"). Offsets 4,539,858–4,539,875 are the dumped `\time`, `\day` and `\month` words |
| aarch64, `SOURCE_DATE_EPOCH`=2026-08-30 07:51 UTC (the shipped log's start minute), `FORCE_SOURCE_DATE=1` | forced | **byte-identical** to the shipped `a476533c…` (compressed and raw) |
| aarch64, one minute later | forced | differs in **exactly one byte**: offset 4,539,859, octal 327 → 330, that is `\time` 471 → 472 |
| x86_64 (emulated), its own start minute 06:10 UTC | forced | **byte-identical** to the shipped x86_64 `5a9dfc4e…` |
| x86_64 (emulated), the aarch64 start minute 07:51 UTC | forced | **byte-identical to the aarch64 `a476533c…`** |

The rebuild's log equals the shipped `pdflatex.log` except its first (banner) line and the two
lines `fmtutil` appends (the command line).

So:
1. the format is fully determined by the source, the input files and the INITEX clock;
2. the ADR-014 draft's F7 ("not byte-reproducible; differs from byte 229,028") compared a rebuild
   made at a different time — its compressed size and offset move with the date string;
3. the two images' formats differ only because they were dumped at different minutes. The
   comment "a dumped format is a memory image" on `TREE_FINGERPRINTS` in `_oracle.py` gives a
   false reason for a true difference.

For H.3 this means the model can load the shipped file and check it against a model-built dump
exactly.

## 4. Behaviour: the rebuilt binary against the pinned one (aarch64) [M]

### 4.1 How it was run

The **pinned** binary ran through `_oracle.py` (`get_oracle()`, `run_pdflatex`: the graded
environment, the allow-listed argv, the private TEXMF trees and the container backend). It
followed `run_to_fixpoint`'s pass protocol:
- up to 3 passes, stopping at the first rc 0;
- then one confirming pass;
- `-interaction=nonstopmode -halt-on-error`.

The **reference** binary ran with the same protocol, argv and environment
(`engine_env(graded_env(tex_env(td)))`) in a second container of the same image. The rebuilt
`pdftex` was mounted as `bin/ref`, so that kpathsea's `SELFAUTOPARENT`, `texmf.cnf` and
`pdflatex.fmt` were the image's own.

Every pass's rc, every file it wrote (sha256 and bytes) and its terminal output were kept. The
harness is `~/.cache/lp-spike-h1/harness/h1cmp.py` and `h1diff.py`. It is not committed: it starts
an engine outside `_oracle.py` for the reference binary, which `check_oracle_pin.py` forbids.

**How outputs were compared.** Byte comparison first. If bytes differ, masks are applied, one at
a time and only when needed; each document records which masks it needed. The masks:
- the banner's date and time;
- the per-run work directory, the oracle's random `mkdtemp` name, which also appears where mktex
  writes generated fonts;
- in a PDF, `/ID`, `/CreationDate` and `/ModDate`;
- two lines that `epstopdf` logs (a converted file's modification time and size);
- the byte size in "Output written on … (N pages, M bytes)";
- a SyncTeX file compared after gunzip;
- a canonical PDF form, used only where Ghostscript's random font-subset tags differ: streams
  decompressed, lengths and cross-reference offsets dropped;
- a "Segmentation fault" line printed on the terminal by a crashed helper under emulation.

The comparator was checked against injected differences. A changed log byte, a changed `.aux`,
a changed rc, a missing file, an engine error and a changed glyph position inside a compressed
PDF stream were each detected. A changed `/ID` and a changed banner date were each accepted, as
designed.

### 4.2 Results

| set | documents | outcome |
|---|---|---|
| (i) the strict tier's committed evidence: every document of `corpora/strict_s0/bytes_probes.json` | **3,907** (2,167 graded + 1,740 outside the fragment by design). The 12 larger than `HEX_MAX` were regenerated with `_strict_bytes` and matched by sha256 | **3,907 agree**: 3,697 byte-identical in every file, 210 equal once the banner's minute is masked. Final rc: 939 × 0, 2,968 × 1 |
| (ii) 200 real papers, frame ranks 2000–2199 (see note), oracle protocol, real clock | 200 | 193 agree (130 byte-identical, 63 masked). **7 differ, all through the real clock**: `\time` printed in a page header (1:19 vs 1:20); an XMP `InstanceID` uuid in 4 papers; "words of memory" +1 in 2 logs. Re-run with a fixed clock, **all 7 agree**. Final rc: 189 × 0, 11 × 1 |
| (ii′) the same 200, fixed clock (`FORCE_SOURCE_DATE=1`, one `SOURCE_DATE_EPOCH`, both binaries) | 200 | **200 agree**: 186 byte-identical, 14 masked (work-directory path, epstopdf's file date, SyncTeX gunzip) |
| (iii) `\tracingall` traces, 20 evidence documents | 20 | **20 agree** (19 byte-identical, 1 banner-masked) |
| (iii) `\tracingall` traces, 20 real papers | 20 | Under the real clock, 14 differ. The one examined diverges first at pgfmath's default random seed `\time`×`\year` (`\count302` = 123 against 124: the two runs started at 02:03 and 02:04 UTC). Both runs of one paper hit the 300 s limit. **Under a fixed clock (both binaries, limit 3,600 s): 20 agree**, 17 byte-identical in every file including logs of up to 1.9 GB, 3 masked (work-directory path) |

**Note on the real window.** Frame ranks 2000–2199 are neither sealed sample 3 (720–919) nor the
fix-policy confirmation window (2600–2718); the harness asserted both disjointnesses. The window
is not virgin: offsets 2000 and 2100 were used for fixer windows, and 2000–2718 for the clock
scan (#625). H.1 tunes nothing, so reusing it costs nothing.

**What this does and does not show.** On aarch64 the two binaries are the same bytes, so (i)–(iii)
test the harness and pdfTeX's determinism under the protocol, not a second implementation. The
result: **with the same binary, image and inputs, every output is reproduced, except where the
document reads the real clock.** That exception is exactly the set of run-dependent inputs
recorded in `STRICT_TIER_DESIGN.md` (`\time`, `\day`, `\month`, `\year` under
`SOURCE_DATE_EPOCH` without `FORCE_SOURCE_DATE`; `\pdfrandomseed`; `\pdfelapsedtime`;
`\pdffilemoddate`). For `FaithfulEngine` it confirms that the clock is part of the input: ADR-014
draft §5.2 / O-5.

**Not run:** the ≈9,000 generated differential documents (`differential_v2.json`,
`bytes_differential.json`). They are committed only as hashes, so running them needs the
extracted OCaml renderer to regenerate them. Given byte identity of the binaries, they would
exercise the harness again, not the engine.

## 5. Floating point: amd64 against arm64

### 5.1 Where the program uses floating point, and what each architecture's compiler did [R + M]

**The real arithmetic of the TeX program itself** (r78081 `pdftex.web`):
- `glue_ratio` is set by divisions: in `hpack`/`vpack` (`pdftex.web` lines 21157–21391) and when
  `fin_align` sets unset boxes (lines 24085–24113). It is used by multiplications:
  - in `hlist_out`/`vlist_out` and pdfTeX's `pdf_hlist_out`/`pdf_vlist_out` (ship-out positions);
  - in `fin_align` (`t:=t+round(float(glue_set(p))*stretch(v))`, spanned alignment columns: TeX
    state);
  - in the glue printing of `\showbox`/`\tracingoutput`, `round(unity*g)`.
- `make_accent` computes `delta:=round((w-a)/float_constant(2)+h*t-x*s)` (a kern width: TeX state).

**The aarch64 binary has 524 FMA instructions.** Mapped to functions through the unstripped
build (§2.2):
- **485** are in xpdf (the PDF-inclusion parser, C++);
- **39** are in C functions:
  - `pdfsetmatrix` 8;
  - `t1_scan_param` 4;
  - `makeaccent` 2;
  - `pdfhlistout` 2;
  - `hlistout` 2;
  - `zpdfsetrule` 2;
  - `do_matrixtransform` 2;
  - `read_jbig2_info` 2;
  - the rest in libpng's gamma code and in `ttf_read_post` and `read_pdf_info`.

**The x86_64 binary has none** (0 `vfmadd`/`vfmsub`/`vfnmadd`). It is built for baseline x86-64,
which has no FMA; doubles use SSE2, so there is no x87 excess precision [I, from the ABI
default].

In `makeaccent`, GCC fused `(w-a)/2 + h*t` into `fmadd` and `… - x*s` into `fmsub`. In
`pdfhlistout`, the glue product itself is a plain `fmul` (not fused). The function's one
`fmadd`/`fmsub` pair was not traced back to its source expression. `fin_align` (`zfinalign`) has
no FMA.

**When can a fused and an unfused computation differ?** Only when a product is inexact in double
precision. [I, from the operand bounds]:
- In `make_accent`, `h*t` is `h * slant/65536`, with `|h| < 2^30` sp. It is exact whenever
  `|slant| * |h| < 2^53`. That holds for every font whose slant parameter is below 128 in
  absolute value (real fonts: about 0.1–0.3).
- `(w-a)/2` is exact.
- So on real fonts both architectures compute the same `delta`. The channel is real only for
  absurd TFM parameters.
- The same argument covers the shipout sites. They move PDF coordinates, and `\pdflastxpos`
  after `\pdfsavepos`.

**libm:** both binaries import the same functions (`acos asin atan atan2 cos frexp log log10 modf
pow sin sqrt`, plus `floor` on x86_64). Within pdfTeX's own C code, calls reach them only from
PDF-side code:
- `create_fontdescriptor` (the `ItalicAngle`, via `atan`);
- `t1_scan_param` (Type 1 font parsing, `atan`);
- libpng's gamma tables (`pow`);
- xpdf (28 call sites).

None of pdfTeX's own procedures that change TeX state calls libm.

### 5.2 Measured [M]

Both architectures ran the **pinned** binary (amd64 under emulation) through `_oracle.py`, with
the clock fixed on both sides, so that runs hours apart are comparable.

| set | documents | outcome |
|---|---|---|
| `pdflatex.fmt` (INITEX over the whole LaTeX kernel) | 1 | **byte-identical** at the same clock (§3) |
| real papers, ranks 2000–2199 | 200 | **200 agree**: 186 byte-identical, 14 masked. Masks needed, counted in documents: the work-directory path (terminal output 9, log 7); Ghostscript's font-subset tags inside EPS conversions (PDF canonical form 4), and the PDF byte size that follows from them (3); epstopdf's file date (4) and size (2); SyncTeX gunzip (1); an emulator "Segmentation fault" terminal line (4). Final rc 189 × 0, 11 × 1 on both |
| evidence documents, every 8th of the 3,907 | 489 | **489 byte-identical** in every file, the terminal output included |
| `\tracingall` traces, 20 evidence documents | 20 | **20 byte-identical** |
| `\tracingall` traces, 20 real papers | 20 | 9 byte-identical; the other 11 did not finish under emulation within 300 s (see below) and are being re-run with a 5,400 s limit |

**Emulation artefacts, all re-run and none counted as agreement:**
- real papers: 3 engine runs segfaulted under qemu before printing pdfTeX's banner (exit 139; `_oracle.py` refused them as "pdfTeX did not run"); 1 left a `core` file from a crashed helper in the work directory; 1 hit the 300 s limit (emulated METAFONT). All 5 were re-run, with a 3,000 s limit, and agree;
- evidence sample: 8 engine segfaults (exit 139), re-run, and all 8 agree;
- traced real papers: 10 hit the 300 s limit under emulation, and 1 failed its first pass on a font that emulated `mktexpk` could not make (`missfont.log`). Re-run with a 5,400 s limit: in progress at the time of this commit.
- one emulated oracle container was **mutated** by the run (see §6.1). Every grade made after the
  mutation was discarded and re-run in a fresh container. From then on the harness checks
  every container after every document.

**Ghostscript is architecture-dependent; pdfTeX was not.** On one architecture, two runs hours
apart gave identical EPS conversions; across architectures the conversions' subset tags differed.

**Conclusion.**
- No difference between the two architectures was observed on any document.
- The one code-level channel (FMA contraction on aarch64 only) is bounded to inexact products,
  which real fonts and ordinary dimensions do not produce.
- `FaithfulEngine` stays per architecture, as ADR-015 states. For H.2, the Pascal-level semantics
  `PS` does not describe the aarch64 binary's arithmetic at the fused sites. Either `PS` models
  fused multiply-add at exactly those sites of the translated program, or a lemma shows the
  products exact under the fragment's bounds and a document outside the bounds is `Stuck`.

## 6. Findings for other tracks

### 6.1 Oracle (OPEN-118): a helper process can write into the image's TeX tree [M]

In the emulated amd64 oracle container (work root `work-h1-amd64`), at 22:49:47 UTC on
2026-09-29, a document that needed Cyrillic LH fonts ran `mktexmf`. A helper crashed with
SIGSEGV under qemu, and `mktexmf` then:
- wrote `lati0600.mf` into `/usr/local/texlive/2026/texmf-dist/fonts/source/lh/lh-t2a/`;
- rewrote `/usr/local/texlive/2026/texmf-dist/ls-R` (via `mktexupd`).

The container runs as root, so nothing stopped it. The oracle's `check_state` would refuse the
container at the **next** session, but every grade in the rest of that session came from a
mutated image (OPEN-118 known limit (h)).

It was caught here only because the cross-architecture comparison showed a terminal line naming
the system path. On native aarch64 no such write happened in any run: checked after the runs,
with no file of `/usr/local/texlive` newer than the container.

The trigger here was emulation. The exposure is not [I]:
- `mktexmf` writes wherever `mktexnam` names (`destdir`, `mktexmf` lines 68–75), then calls
  `mktexupd`;
- when a helper fails, that name fell back to the source's own directory in the system tree.
  The crashed helper was not identified, and whether a native failure can take the same path is
  unmeasured;
- as root, nothing refuses the write.

Suggested fix for the oracle track: mount the installation read-only in the oracle container
(`--read-only` or a read-only bind of `/usr/local/texlive`), so the write fails instead of
succeeding. That needs its own measurement.

### 6.2 Oracle: concurrent sessions in one container can make `check_state` refuse

`check_state` refused a new session because another session's `mktextfm` was, at that moment,
holding `/tmp/mt*.tmp` in the same container. This is a false refusal, so it fails closed, and
it is the C-93 class. It is worth recording because parallel graders share one container per
work root.

### 6.3 Already recorded elsewhere

The native backend's inherited stdin (ADR-014 draft, oracle branch C-99).

## 7. Reproducing this

Everything is under `~/.cache/lp-spike-h1/` on the machine that ran it:
- `src-dc8efcd4.tar` (sha256 above) and `buildpdftex.sh` (the recipe of §2.2);
- `b-arm64/`, the build tree, with `build-arm64.log`;
- `rel/`, the upstream release tarballs;
- `f7r/` and `f7amd/`, the format experiments of §3 (`f7r.sh`, `f7amd.sh`);
- `harness/`: `h1cmp.py` runs a set, `h1diff.py` compares two runs, and `drive_amd64*.sh` is the
  amd64 driver with container resets;
- `runs/`, raw outputs per set, architecture, document, engine and pass;
- `diff_*.json`, the comparison results;
- `emufail/`, the emulation failures that were re-run;
- `fma_by_function.txt`, the FMA map of §5.1.

A run:

```
python3 harness/h1cmp.py {strict|strict8|strict20|real|real20} {arm64|amd64} {pinned[,ref]} WORKERS [--trace] [--fixclock]
python3 harness/h1diff.py SET ARCH                               # pinned vs ref
python3 harness/h1diff.py SET --cross amd64:pinned arm64:pinned  # across architectures
```

The session's transcripts that produced §§1–2.1 are
`6724887f-375f-4639-96cf-722343631c21/subagents/agent-a06ca7da635c68236.jsonl` (the first H.1
session) and this session's.
