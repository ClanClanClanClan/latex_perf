# Foundation spike, step H.1: the pinned pdfTeX's source revision, reproduced

> **This copy on `main`.** Copied verbatim from branch `spike/v27165-engine-translation` at
> commit `6988d649`, which stays the home of the spike's code and evidence. Every relative `h1/…`
> path below (and `diffs/…`, `fma/…`, `tools/…`, `adversarial/…` in §7) names a file under
> `docs/v27/spike/h1/` on that commit, not on `main`. The only edits are that the links now point at
> that commit, that five path spans are written `6988d649:docs/v27/spike/h1/…`, the form
> `git show` takes, and this note.

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123),
step H.1 of the ADR-014 draft §9.
**Dates:** begun 2026-09-29 by a session that an API limit cut off; resumed and completed on
2026-09-30 from that session's transcripts and the build trees it left on disk.
**Kill criterion (H.1):** the revision cannot be identified **and** no revision reproduces the logs.

**Verdict: the kill criterion did not fire.** The revision is identified by three independent
sources. Our rebuilds from that source are byte-identical to the pinned binary on **both**
architectures. The shipped format is reproducible byte for byte. On every corpus document run, the two
architectures' pinned binaries gave the same results. **But the architectures do not run the same
program**: wherever C leaves a result undefined or implementation-defined, the two ISAs and the two
compilers answer differently, and adversarial documents turn that into different **exit codes**,
logs, TeX state and PDFs (§5.3, §5.4). `\pdfsnapy 0pt`, a pdfTeX primitive with no external file,
exits 0 on aarch64 and dies with SIGFPE on x86_64. The H.1 pass criterion held only with the clock
fixed (§4.2). Revised after review round 1 (§5, §4.1, [`h1/`](h1/README.md)), review round 2
(§5.4, [`h1/archsem/`](h1/archsem/README.md); round 1's "the architectures differ in the PDF only"
was wrong, C-103) and review round 3 (§5.4: round 2's hand-argued "safe" verdicts are no longer
verdicts, one of them was false and plain `\xleaders` diverges; the signed-overflow rule reaches
only the translated program; C-106).

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## 0. Results at a glance

| question | answer | tag |
|---|---|---|
| Which source built the pinned `pdftex`? | TeX Live svn **r78081**, i.e. TeX-Live/texlive-source commit `dc8efcd41054ec4bf7f96c022cd2d91fe346f6e1` (tag `svn78081`, 2026-02-23T16:24:02Z) | M |
| Is the image's binary the upstream build of that source? | yes, for both architectures: byte-identical to the `svn78081` GitHub release assets | M |
| Does our rebuild reproduce it? | **yes, byte for byte, on both architectures**: aarch64 natively (sha256 `cee621bf…`), amd64 under emulation (`1c5ff711…`, §2.3) | M |
| Is `pdflatex.fmt` reproducible? | **yes, byte for byte**, given the INITEX run's clock; and it does not depend on the architecture (the ADR-014 draft's F7 was wrong: C-100). The x86_64 INITEX run was emulated (qemu-user), not native | M |
| Same binary, same inputs: same outputs? | yes: 3,907 of 3,907 evidence documents, and 200 of 200 real papers once the real clock is fixed | M |
| Do amd64 and arm64 differ? | **on the corpus, no; in general, yes, in the compile verdict itself** (review round 2, C-103). Five classes of architecture-defined C semantics were enumerated from the two binaries (§5.4): integer division (x86_64 traps), float-to-int conversion out of range (x86_64 gives INT_MIN, aarch64 saturates), signed overflow (the two compilers exploit it differently), fused multiply-add, and `char` signedness. Adversarial documents reproduce the first three as different rc, log or TeX state: `\pdfsnapy 0pt` exits 0 / 136 (SIGFPE); a valid 40000×8 px JPEG with no resolution is "Huge page", rc 1, on aarch64 and `\wd` = −32768pt, rc 0, on x86_64; `\divide` of INT_MIN by INT_MIN gives −1 / 1; a plain `\xleaders` over a glue of 2³¹−2 sp exits 0 / 136 (review round 3). Of the 316 division and conversion sites, **15 diverge** (reproduced, and each probe traced under gdb on both architectures executing the site's own instruction with the diverging operand; review round 4 refuted 3 of round 3's 18 hand attributions), **4 are unreachable** (machine-checked), **77** are in the translated program with no divergence reproduced, and **220** are C-boundary sites with no evidence either way (152 in libpng and xpdf). Round 2's count "98 settled safe" rested on hand-argued bounds, one of them false (C-106); an argument is now a note, not a verdict. The proposed H.2 rule (Stuck on every undefined operation, pending the owner) covers the translated program's 85 sites without per-site bounds; the 227 boundary sites that are not unreachable, and the C-boundary functions whose code changes under `-fwrapv` (463) or `-fsigned-char` (314), are H.2's C-boundary work list. Round 1's FMA answer, kept below: **on the corpus, no; in general, yes, in the PDF.** 489 of 489 evidence documents and 200 of 200 real papers agree, and so do the \tracingall logs of 20 evidence documents and 20 real papers (§5.2). But the aarch64 binary fuses multiply-adds that the x86_64 one does not, and at the `\pdfsetmatrix` sites the products are inexact: an adversarial document of 160 `\rotatebox`es holding 400,000 links gives PDFs that differ in **1 byte** (a link `/Rect` coordinate), with rc, `.log` and `.aux` identical (§5.3). Every fused site outside xpdf is classified in §5.1; the ones that reach TeX state are exact on their whole input range or under a stated bound, except xpdf's real-number parser, which is open. All amd64 runs were emulated (qemu-user), not native | M + R + I |

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

### 2.3 The amd64 rebuild: byte-identical, after emulator crashes [M]

Upstream builds x86_64 on `almalinux:8` with `gcc-toolset-11`, on a native amd64 GitHub runner.
This host is arm64. Colima here runs amd64 containers through qemu-user binfmt emulation
(`vmType: vz`, `rosetta: false`), and the VM is shared with other work, so its configuration was
not changed.

Four attempts were made, all in `almalinux:8` under emulation with the recipe's flags:
- **Attempt 1 (2026-09-29):** failed in `texk/kpathsea` with `Segmentation fault (core dumped)`
  from `gcc` compiling `rm-suffix.c`, a trivial file.
- **Attempt 2 (from 2026-09-29 22:40 UTC):** a fresh build with automatic `make` resumes. It
  crashed at four unrelated points: `gcc` on LuaJIT's `lj_api.c`; `configure: error: cannot run C
  compiled programs` in freetype2; `cc1` on cairo's `cairo-device.c`; `cc1` on gmp's
  `toom32_mul.c`. The gmp crash left gmp half-built, and every further plain resume then stopped
  at mpfr's `configure: error: gmp.h not found` (five times).
- **Attempt 3 (2026-09-30 00:01–03:50 UTC):** resumed in place, making each library first, in
  dependency order. It crashed at 11 more points over 10 resumes:
  - `cc1` three times, once on mpfr's `set.c`;
  - `cc1plus` three times;
  - `cannot run C compiled programs` in harfbuzz's `configure`;
  - `cannot compute suffix of executables` in seetexk's `configure`;
  - `make` itself segfaulting three times: ICU's `icuexportdata.o`, web2c's own `tangle.p`, and
    fontforge's `libff_a-memory.o`.

- **Attempt 4 (2026-09-30 03:56 UTC):** the full `make world` was stopped, since every other
  engine it builds is one more chance of a crash. Instead, only web2c's `pdftex` target was built
  in the configured tree (`make -j 2 pdftex` in `Work/texk/web2c`, 26 compiler invocations). It
  succeeded on the first try. The link output (6,517,040 bytes) was stripped as TeX Live's
  `install-strip` does, with the toolset's `strip` (binutils 2.36.1) and with the system's.
  **Both give 2,405,736 bytes with sha256
  `1c5ff71156ee990c3a18402cf06d3671ecf748bd84fb3983dbd5d62b600bc40b`, the pinned x86_64
  binary** (`cmp`: identical).

**Diagnosis: emulator instability, not a source or toolchain defect.**
- The crash sites are unrelated, and no site crashed twice.
- The upstream build of the same commit succeeds.
- The toolchain matches the binary's `.comment` (gcc-toolset-11 11.2.1-9).
- The rest of the package set is today's AlmaLinux 8, not the 2026-02-23 one: glibc
  2.28-251.el8_10.40, and the toolset's linker, binutils 2.36.1-4.el8_6.alma.1.

The emulator crashes could have left a half-written target that a later `make` took as up to
date. The byte identity rules that out for this binary. The package set was not pinned to
2026-02-23, and the result is identical anyway, so the difference in versions did not reach this
binary.

**Consequence:** no deferral is needed; both pinned binaries are reproduced from source. Future
engine pins should rebuild amd64 on a native amd64 host (a CI runner, as upstream does), not
under emulation.

The behavioural cross-architecture question does not need the rebuild; §5 answers it with the
pinned amd64 binary itself.

## 3. The format file: reproducible, and architecture-independent (C-100) [M]

Inside the pinned image, INITEX was re-run with the command recorded in `fmtutil.cnf`
(`pdftex -ini -jobname=pdflatex -progname=pdflatex -translate-file=cp227.tcx *pdflatex.ini`).

| run | clock | result |
|---|---|---|
| aarch64, today's clock (2026-09-29) | real | differs from the shipped format in **7 bytes** of 11,621,149 (uncompressed). Offsets 974,182, 974,184 and 974,185 are date digits of the format identifier ("2026.8.30" against "2026.9.29"). Offsets 4,539,857 and 4,539,858 are in the dumped `\time` word (bytes 4,539,855–4,539,858), 4,539,866 in `\day` and 4,539,874 in `\month` |
| aarch64, `SOURCE_DATE_EPOCH`=2026-08-30 07:51 UTC (the shipped log's start minute), `FORCE_SOURCE_DATE=1` | forced | **byte-identical** to the shipped `a476533c…` (compressed and raw) |
| aarch64, one minute later | forced | differs in **exactly one byte**: offset 4,539,858, 215 → 216 (octal 327 → 330), the low byte of the big-endian `\time` word: 471 → 472 |
| x86_64 (emulated), its own start minute 06:10 UTC | forced | **byte-identical** to the shipped x86_64 `5a9dfc4e…` |
| x86_64 (emulated), the aarch64 start minute 07:51 UTC | forced | **byte-identical to the aarch64 `a476533c…`** |

Offsets are 0-based byte positions in the gunzipped format (`cmp -l` prints them 1-based, one
higher; the first version of this table gave `cmp`'s 1-based offsets in every row without saying
so, and gave ranges where the differing bytes are not contiguous).

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
runner is `~/.cache/lp-spike-h1/harness/h1cmp.py`. It is not committed as code: it starts an engine
outside `_oracle.py` for the reference binary, which `check_oracle_pin.py` forbids for tracked
code; `6988d649:docs/v27/spike/h1/README.md` records its sha256. The comparator `h1diff.py`, its kill-tests and every
comparison summary are committed under [`h1/`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/README.md).

**How outputs were compared.** Byte comparison first. If bytes differ, masks are applied, one at
a time and only when needed; each document records which masks it needed. The masks:
- the banner's date and time;
- the per-run work directory, the oracle's random `mkdtemp` name, which also appears where mktex
  writes generated fonts;
- in a PDF, `/ID`, `/CreationDate` and `/ModDate`;
- two lines that `epstopdf` logs (a converted file's modification time and size);
- the byte size in "Output written on … (N pages, M bytes)";
- a SyncTeX file compared after gunzip;
- a canonical PDF form, engaged only when the PDFs still differ **and** at least one side wrote a
  Ghostscript intermediate (`*-eps-converted-to.pdf` of the same run): streams decompressed (bytes
  after a stream's zlib end, or a truncated stream, are kept and compared); `/Length` values
  masked; the cross-reference stream decoded row by row with only the byte offset of a type-1
  entry dropped (entry types, generations, object-stream numbers and indices are compared);
  classic xref entries' offsets and `startxref` dropped; and only those `/XXXXXX+` tags replaced
  that occur in the same side's Ghostscript intermediates. pdfTeX's own subset tags, `/Size`, `/W`
  and `/Index` are compared. (Review round 1: the first version replaced every tag and dropped
  `/Size`, `/W` and `/Index`. Review round 2: the second still engaged on any PDF difference, even
  with no Ghostscript intermediate, and dropped the whole xref stream and any bytes after a zlib
  end, so it absorbed a zlib-level change, an object moved into an object stream, and trailing
  bytes. Every comparison was re-run with each fix (`h1/diffs/r1/`, `h1/diffs/r2/`); no verdict
  and no count changed. `6988d649:docs/v27/spike/h1/tools/h1diff_selftest.py`: 2 of the first 5 cases pass on the first
  version; 6 of 12 on the second; 12 of 12 now);
- a "Segmentation fault" line printed on the terminal by a crashed helper under emulation.

The work-directory mask assumes both sides' work roots have the same length (line wrapping of
long paths depends on it). A run in a work root of another length fails closed, as DIFF (it
happened once, §5.2).

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

**The H.1 pass criterion** (ADR-014 draft §9: "the reference build's logs and `.aux` equal the
pinned binary's on 200 corpus documents (PDF modulo `/ID`)"). Under the protocol's real clock it
is **not met as written**: 7 of the 200 differ, 2 of them in the log ("words of memory" +1) and 5
in the PDF beyond `/ID`. Every one traces to the real clock (the two binaries are the same
bytes, so the engine cannot be the cause). With the clock fixed, **it is met: 200 of 200**, with
masks beyond `/ID`: the work-directory path (7 logs, 9 terminal outputs, 1 SyncTeX file),
epstopdf's file date (4 logs) and SyncTeX compared after gunzip (1); no PDF needed a mask. So the criterion held only after the
clock was made an input, which is ADR-014 draft O-5's open question, not a result of H.1.

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

## 5. amd64 against arm64: floating point (§5.1–5.3) and every other architecture-defined C semantics (§5.4)

### 5.1 Where the program uses floating point, and what each architecture's compiler did [R + M]

**The real arithmetic of the TeX program itself** (r78081 `pdftex.web`):
- `glue_ratio` is set by divisions: in `hpack`/`vpack` (`pdftex.web` lines 21157–21391) and when
  `fin_align` sets unset boxes (lines 24085–24113). It is used by multiplications:
  - in `hlist_out`/`vlist_out` and pdfTeX's `pdf_hlist_out`/`pdf_vlist_out` (ship-out positions);
  - in `fin_align` (`t:=t+round(float(glue_set(p))*stretch(v))`, spanned alignment columns: TeX
    state);
  - in the glue printing of `\showbox`/`\tracingoutput`, `round(unity*g)`.
- `make_accent` computes `delta:=round((w-a)/float_constant(2)+h*t-x*s)` (a kern width: TeX state).

**The aarch64 binary has 524 FMA instructions; the x86_64 binary has none** (0
`vfmadd`/`vfmsub`/`vfnmadd`). The x86_64 build targets baseline x86-64, which has no FMA; doubles
use SSE2, so there is no x87 excess precision [I, from the ABI default].

A fused `a*b+c` rounds once; the unfused one rounds the product and then the sum. The two can
differ **only when the product `a*b` is inexact** in double precision. So each site is settled by
one of two things: an argument that its products are exact over the site's inputs, or a
counterexample.

**Where the 524 are [M].** Each instruction was mapped to its function and source line through the
DWARF line table of the unstripped build (§2.2; `objdump -d -l`, file
[`h1/fma/fma_sites_aarch64.tsv`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/fma_sites_aarch64.tsv)). 485 are in xpdf (C++, no line
table). The other **39** are below, every one classified. (Round 0 of this report traced only
`make_accent` and claimed that "the same argument covers the shipout sites". That was untested,
and it was false for `\pdfsetmatrix`: review round 1 refuted it with the document of §5.3.)

| sites (FMA count) | source, r78081 | expression | what the result reaches | products exact? | channel |
|---|---|---|---|---|---|
| `makeaccent` (2) | `pdftex0.c:34419`, `make_accent` | `round((w-a)/2 + h*t - x*s)`, with `t = s = slant/65536` | **TeX state**: the width of the accent kern | yes when `|h|·|slant|` and `|x|·|slant|` are below 2^53, with `slant` in raw TFM units. That holds whenever `|slant| < 128` (`|h|, |x| < 2^30` sp). Real fonts have 0.1–0.3 [I, bound] | **none under the bound**. Beyond it, model per architecture or Stuck |
| `hlistout` (2), `pdfhlistout` (2) | `pdftex0.c:17915`, `24020`: MLTeX character substitution in `tex.ch` (lines 5050–5059) | the same `delta`, over `base_slant` | `cur_h`: DVI/PDF positions, and `\pdflastxpos` after `\pdfsavepos` (**TeX state**) | same bound as `makeaccent` [I]. Reached only when the format was dumped with MLTeX enabled; `pdflatex.fmt` was not (`fmtutil.cnf` has no `-mltex`) [R] | **none** in the pinned configuration |
| `zpdfsetrule` (2) | `pdftex0.c:20230`, `20255` | `y - (h+1)/2.0` (the halving compiled as `×0.5`) | PDF rule coordinates | yes, for every integer `h` | **none** |
| `pdfsetmatrix` (8) | `utils.c:1420–1431` | `e = cur_h·(1-a) - cur_v·c`; the product with the enclosing matrix | the matrix stack, which is read only by `matrixtransformrect`/`matrixtransformpoint` for link, destination and thread rectangles (`pdftex.web` 36445–36553, 36720–36738): **PDF only** | **no**: `a, b, c, d` come from `\pdfsetmatrix`, for example `cos θ` from graphicx's `\rotatebox` (`pdftex.def`) | **yes, output-only** |
| `do_matrixtransform` (2) | `utils.c:1494–1495` | `DO_ROUND(x·a + y·c + e)`; aarch64 computes `fma(x, a, y·c) + e` | the same rectangles: **PDF only** | **no**. [`6988d649:docs/v27/spike/h1/fma/matrix_search.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/matrix_search.py) finds 3 rounding flips in 1,705,191 random sp positions at `a = 0.866025` | **yes, output-only, reproduced end to end** (§5.3) |
| `read_jbig2_info` (2) | `writejbig2.c:798–799` | `(int)(xres·0.0254 + 0.5)` | **TeX state**: the image resolution sets a JBIG2 image's default width and height (`pdftex.web` 34475–34480) | not always, but **exhaustively, no input flips the result**: every unsigned 32-bit `xres` next to a rounding boundary was tested ([`jbig2_exhaustive.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/jbig2_exhaustive.py): 0 flips among the 109,092,170 boundaries) [M] | **none** |
| `read_pdf_info` (1) | `pdftoepdf.cc` (confirmed from the disassembly: `scvtf`, `scvtf`, `fmadd`, `fcvt s`) | `(float)(major + minor·0.1)`, the PDF version allowed | a warning in the log, or an error when `\pdfinclusionerrorlevel` > 0 (**TeX-visible**) | not always, but after the conversion to `float` the results differ only when `minor = -10·major` ([`pdfversion_exhaustive.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/pdfversion_exhaustive.py)). pdfTeX refuses `\pdfminorversion` outside 0..9 (`pdftex.web` 15475) [M] | **none** |
| `t1_scan_param` (4) | `writet1.c:621`, `655` | a font's `FontMatrix` under the map file's `SlantFont`/`ExtendFont`; `ItalicAngle` | the embedded Type 1 font program: **PDF only** | no | output-only, not observed |
| `ttf_read_post` (1) | `writettf.c:485` | `ItalicAngle` | the font descriptor: **PDF only** | no | output-only, not observed |
| libpng (13: `png_fixed`, `png_fixed_ITU`, `png_XYZ_from_xy` 2, `png_build_gamma_table`, `png_build_8bit_table`, `png_build_16bit_table`, `png_gamma_8bit_correct`, `png_gamma_16bit_correct`, `png_gamma_correct` 2, `png_get_pHYs_dpi` 2) | `png.c`, `pngget.c` | gamma and colour-space arithmetic | PNG pixel data: **PDF only**. `png_get_pHYs_dpi` has **no call site** in the binary; pdfTeX computes a PNG's resolution itself (`writepng.c:51`, `round(0.0254·ppm)`: a product, no FMA) | no | output-only, not observed |

**xpdf (485), not traced one by one.** pdfTeX uses xpdf to parse and copy included PDF files. One
path from xpdf into TeX state was found. `Lexer::getObj` (2 FMAs) parses PDF real numbers by
`xf = xf + scale·d` with `scale = 0.1^k`, which is fused on aarch64. The page box of an included
PDF is parsed this way, and becomes `epdf_width`/`epdf_height` (C `float`, `pdftoepdf.cc:770`),
then the image's width and height in sp (`writeimg.c:320`): **TeX state**. Measured with
[`lexsim.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/lexsim.py), a transcription of `Lexer.cc` lines 157–221:
- 29 of 300,000 random numerals (0–2,000, 1–6 decimals) parse to different doubles;
- none of them to different floats;
- a search at 20,000 float rounding midpoints, with numerals of 8–25 digits, found none either
  ([`lexmid.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/lexmid.py)).

This channel is **open**: not observed, not excluded. The other 483 xpdf sites are in rendering,
shading, annotation and form code, and in number formatting. None of them was followed to a
TeX-visible value.

**libm:** both binaries import the same functions (`acos asin atan atan2 cos frexp log log10 modf
pow sin sqrt`, plus `floor` on x86_64). Within pdfTeX's own C code, calls reach them only from
PDF-side code:
- `create_fontdescriptor` (the `ItalicAngle`, via `atan`);
- `t1_scan_param` (Type 1 font parsing, `atan`);
- libpng's gamma tables (`pow`);
- xpdf (28 call sites).

None of pdfTeX's own procedures that change TeX state calls libm. glibc's x86_64 libm selects
some implementations at load time by CPU feature (the `ifunc` variants), so an emulated and a
native amd64 CPU may run different code for the same call. This matters only for the PDF-side
calls above [I].

### 5.2 Measured [M]

Both architectures ran the **pinned** binary (amd64 under emulation) through `_oracle.py`, with
the clock fixed on both sides, so that runs hours apart are comparable.

| set | documents | outcome |
|---|---|---|
| `pdflatex.fmt` (INITEX over the whole LaTeX kernel) | 1 | **byte-identical** at the same clock (§3) |
| real papers, ranks 2000–2199 | 200 | **200 agree**: 186 byte-identical, 14 masked. Masks needed, counted in documents: the work-directory path (terminal output 9, log 7); Ghostscript's font-subset tags inside EPS conversions (PDF canonical form 4), and the PDF byte size that follows from them (3); epstopdf's file date (4) and size (2); SyncTeX gunzip (1); an emulator "Segmentation fault" terminal line (4). Final rc 189 × 0, 11 × 1 on both |
| evidence documents, every 8th of the 3,907 | 489 | **489 byte-identical** in every file, the terminal output included |
| `\tracingall` traces, 20 evidence documents | 20 | **20 byte-identical** |
| `\tracingall` traces, 20 real papers | 20 | **20 agree**: 17 byte-identical in every file, the \tracingall logs included (up to 1.9 GB), and 3 masked (work-directory path; one emulator "Segmentation fault" terminal line). Final rc 18 × 0, 2 × 1 on both |

**Emulation artefacts, all re-run and none counted as agreement:**
- real papers: 3 engine runs segfaulted under qemu before printing pdfTeX's banner (exit 139; `_oracle.py` refused them as "pdfTeX did not run"); 1 left a `core` file from a crashed helper in the work directory; 1 hit the 300 s limit (emulated METAFONT). All 5 were re-run, with a 3,000 s limit, and agree;
- evidence sample: 8 engine segfaults (exit 139), re-run, and all 8 agree;
- traced real papers: 10 hit the 300 s limit under emulation, and 1 failed its first pass on a font that emulated `mktexpk` could not make (`missfont.log`). All 11 were re-run with a 5,400 s limit, finished, and agree.
- one emulated oracle container was **mutated** by the run (see §6.1). Every grade made after the
  mutation was discarded and re-run in a fresh container. From then on the harness checks
  every container after every document.
- **the 13 grades made before the mutation, in that container, before the guard existed**
  (result files dated 22:42:34–22:49:36 UTC; the mutation was at 22:49:47) had been kept on the
  inference that the container was still clean then. Review round 1 asked for a measurement
  instead: all 13 were **re-graded in a fresh, guarded container** (`6988d649:docs/v27/spike/h1/tools/real13_ids.json`),
  0 mutations. **13 of 13 agree** with the arm64 grades and with the kept amd64 grades, 11
  byte-identical and 2 on the work-directory mask (`h1/diffs/r1/diff_real13-fixclock-regrade2__*`).
  A first re-grade (`…-regrade__*`, kept) used a work root 3 characters longer and failed closed on
  those 2 documents, where the longer path wraps a log line differently (§4.1); it was repeated
  with a work root of equal length.
- **superseded and aborted runs, all disclosed** (none is counted above; each is kept in the
  cache and summarised in `6988d649:docs/v27/spike/h1/README.md`): a first cross-architecture comparison of 25 real papers
  (`DIFF_STDOUT_ONLY` 1: that document is the mutation itself, whose terminal line named the
  system path, which is how the mutation was found); the 48 grades made in the mutated container
  (1 timed out under emulation, 1 differs on the mutation's terminal line, 46 agree); an aborted
  full-evidence amd64 run replaced, for time, by every 8th document (53 of 53 identical); an
  aborted amd64 run under the protocol clock (4 documents).

**On the corpus, Ghostscript's output depended on the architecture and pdfTeX's did not.** On one
architecture, two runs hours apart gave identical EPS conversions; across architectures the
conversions' subset tags differed. That pdfTeX's own output can differ too is shown in §5.3.

### 5.3 Adversarial: the architectures do write different PDFs [M]

Review round 1 built [`h1/adversarial/rot2.tex`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/adversarial/rot2.tex) (sha256 `af4bf4b7…`):
160 `\rotatebox` blocks at pseudo-random angles holding 400,000 `\pdfstartlink` annotations, with
`\pdfdecimaldigits=4`. Re-run here in fresh containers of the pinned image (native arm64, emulated
amd64), `SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`: rc 0 on both; `.log` and `.aux`
byte-identical; the PDFs (56,483,205 bytes each) differ in **exactly one byte**, at offset
2,929,960 (0-based): `/Rect [418.7665 390.6534 …]` on aarch64 against `/Rect [418.7666 …]` on
x86_64. Same PDF sha256s as the reviewer's run (`c84b12a6…` aarch64, `043e4ebc…` x86_64). This is
the `do_matrixtransform`/`pdfsetmatrix` channel of §5.1: a link rectangle's corner rounded to the
other side of a half-sp. (`sscanf`'s parse of the matrix is correctly rounded on both
architectures, so the matrix entries agree [I].)

**Conclusion** (of the FMA question; the conclusion about the architectures as a whole is §5.4,
which refutes round 1's "in the PDF only").
- **On the corpus, no difference between the architectures was observed** (200 real papers, 489
  evidence documents, 40 traced documents).
- **FMA makes them differ in the PDF**: the fused multiply-adds of `\pdfsetmatrix`'s matrix
  arithmetic change link, destination and thread rectangles (reproduced; output-only: no TeX
  state, rc or log depends on them). Other classes make them differ in rc and TeX state (§5.4).
- **Every fused site outside xpdf that reaches TeX state is exact** over its whole input range
  (`read_jbig2_info`, `read_pdf_info`), under a stated bound (`make_accent`: |slant| < 128), or
  unreachable in the pinned configuration (MLTeX). The exception is xpdf's real-number parser
  (included PDFs' page boxes), which is **open**.
- All amd64 evidence, the behaviour runs and the format run, is **emulated** (qemu-user TCG). A
  confirmation on a native amd64 host (the CI runner of `tex-oracle.yml`) has not been done.
- For the FMA sites: `PS` must model fused multiply-add per architecture **at the matrix sites**
  (or the model's PDF output is not claimed there); no exactness lemma is available at those
  sites. `make_accent` needs an exactness lemma with the slant bound, and Stuck beyond it. The
  exhaustive results above suffice for JBIG2 and the PDF version (the PDF-version check now covers
  pdfTeX's whole input range, every major 1..2^31−1 with every minor 0..9:
  [`fma/pdfversion_full.c`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/fma/pdfversion_full.c), 21,474,836,470 pairs, 0 differ; review
  round 2 found that the round-1 script, called exhaustive, covered majors 0..9 only). An included
  PDF's dimensions stay at the C boundary, modelled per architecture or Stuck. This is **not
  sufficient** on its own: §5.4.

### 5.4 The class: C semantics the architecture defines [M + R]

Review round 2 found that §5.1–5.3 answered "do the architectures differ?" by a census of **one**
member of a class, the fused multiply-add, and reproduced a JPEG that gives rc 0 on aarch64 and
rc 1 (or SIGFPE) on x86_64 through two other members. C-102's rule ("enumerate the sites from the
binary") had been applied to the instance, not to the class (C-103). This section enumerates the
class.

**The class.** The same C source compiles to programs that answer differently wherever C leaves
the result undefined (UB) or implementation-defined, and the two targets (or their two compilers:
aarch64 gcc 10.2.1, x86_64 gcc-toolset-11) choose differently. From the two ISAs and ABIs [R]:

| member | C status | aarch64 | x86_64 | how the sites were enumerated |
|---|---|---|---|---|
| integer division by 0, and INT_MIN / −1 | UB | `sdiv`/`udiv` return 0 and INT_MIN; remainders via `msub` | `idiv`/`div` trap: SIGFPE, the process dies with rc 136 | every `sdiv`/`udiv` and `idiv`/`div` instruction of both unstripped builds, mapped to source lines by DWARF |
| float → int conversion of NaN or an out-of-range value | UB | `fcvtz*` saturate; NaN → 0 | `cvtt*2si` give INT_MIN ("integer indefinite") | every `fcvtz*`/`fcvta*`/… and `cvt(t)*2si` instruction, likewise |
| signed integer overflow | UB | whatever gcc 10 compiled | whatever gcc 11 compiled | functions whose code changes when the aarch64 build is repeated with `-fwrapv` |
| plain `char` signedness | implementation-defined | unsigned | signed | functions whose code changes when the aarch64 build is repeated with `-fsigned-char` |
| floating-point contraction | allowed by gcc's default `-ffp-contract=fast` | fused (`fmadd`) | none (baseline x86-64 has no FMA) | §5.1 |

Checked and absent: `long double` (x87 instructions on x86_64, `__*tf*` soft-float calls on
aarch64): **0** in both binaries. Not enumerated [I]: shift counts (both ISAs reduce a variable
shift count modulo the operand width, so they agree; a constant UB shift is the compiler's, i.e.
the signed-overflow member's kind), C stack depth (frame sizes differ, so a recursion that
overflows the 8 MB stack does so at different depths), and uninitialised or out-of-bounds reads
(heap layout; `read_APP1_Exif` reads an attacker-chosen offset `tiff_header + value` without a
bounds check).

**Division and conversion sites** ([`archsem/census_sites.tsv`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/archsem/census_sites.tsv),
from [`census.py`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/archsem/census.py); every instruction in `census_insns.tsv.gz`). 620 DIV
and 474 F2I instructions over both binaries, at **316 sites** (source lines; xpdf, C++ without a
line table, by function). Each site has one verdict in
[`classification.tsv`](h1/archsem/classification.tsv), computed by
[`classify.py`](h1/archsem/classify.py) from evidence only, and a scope:
*translated* (`pdftex0.c`, `pdftexini.c`: web2c's C for the tangled Pascal that H.2 translates;
85 sites) or *boundary* (every other file: C that H.2 does not translate; 231 sites).

**Review round 3 changed the method (C-106).** Round 2 gave 93 sites a SAFE verdict and 13 a
NOT-REACHED or OUTPUT-ONLY verdict from hand-stated arguments, none of them probed or
machine-checked. One was false: the 12 leaders divisions of `hlist_out`, `vlist_out`,
`pdf_hlist_out` and `pdf_vlist_out` were "SAFE-GUARD" because "rule_wd ≤ 2³⁰ + 10⁹ (`vet_glue`
clamps the glue)". `vet_glue` clamps the glue *set*, not the width, and `\advance` on a skip is
not range-checked: a glue width of 2³¹−2 sp is reachable, `rule_wd + 10` then wraps (C signed
overflow), `lq` = −1, and `\xleaders` divides by `lq + 1` = 0. An argument is therefore no longer a
verdict; the table keeps it in its `argued` column as an [I] note. The verdicts are:

| verdict | sites | evidence |
|---|---|---|
| **DIVERGES** | **15** (8 translated, 7 boundary) | a committed probe whose recorded outcomes differ between the architectures (`verify_h1.py` re-reads them) **and** which, run under gdb on both architectures, executes the site's own instructions with an edge operand (divisor 0 or −1, an INT_MIN operand, a NaN or out-of-int-range conversion source) on every architecture on which the site has instructions ([`reach_trace/`](h1/archsem/reach_trace/RUN.md); `verify_h1.py` re-checks the link from the committed trace). Review round 4 refuted 3 of round 3's 18 hand attributions: `pdftex0.c:1365` (`nh-intmin` never executes it), `writejpg.c:222` (`jpgdiv` never executes it), `writejpg.c:237` (`jpgconv` executes it only with an in-range source) |
| NOT-REACHED | 4 | every function holding the site's instructions is unreferenced in both builds: no instruction outside it names it, no aarch64 `adrp`+`add` pair computes its address, its address is no 8-byte word of the stripped binary ([`reach.py`](h1/archsem/reach.py), [`reach.out`](h1/archsem/reach.out)): zlib's `gzfread` and `gzfwrite`. Round 2's fifth, kpathsea's `hash_print`, is called by `kpathsea_init_db` (under a debug flag) and is OPEN |
| PS-STUCK | 77 | translated, no divergence reproduced. Needs no per-site bound **if** the owner adopts the proposed `PS` rule (below): the operation is Stuck whenever C would be undefined. H.2 must then show mechanically that its translator emits the checked operation at every `div`, `mod`, `+`, `−`, `*` |
| **OPEN** | **220** | boundary, none of the above: 68 in pdfTeX's own C, web2c's C runtime, kpathsea and zlib (SyncTeX's unit 24, Type 1 number parsing 8, TrueType `unitsPerEm` 4, mktex's base resolution 4, `ExtendFont` 1, 25 with a round-2 argument that is now only a note, and 2 whose DIVERGES attribution the round-4 trace refuted, `writejpg.c:222` and `writejpg.c:237`), 46 in libpng, 106 in xpdf |

The 12 leaders sites, reproduced ([`probes/lead/`](h1/archsem/probes/lead/), outputs
`probes/out/lead-*.out`): for each of the four procedures (`\pdfoutput` 0 and 1, horizontal and
vertical), `\xleaders\copy1\hskip\skip0` with `\skip0` = 2³¹−2 sp and a leader box of
1,598,029,823 sp gives **rc 0 on aarch64 and rc 136 (SIGFPE) on x86_64**; the controls (`\skip0`
= `\maxdimen`; `\leaders`; `\cleaders`) give rc 0 and identical output on both. So the four
`lx = lr div (lq + 1)` sites DIVERGE; the other eight cannot trap (their divisor is the leader box
size, positive by the guard) but take the wrapped dividend, with equal results measured. The
outer box has width 0, so this is not a "Huge page". The review's first run of the `\pdfoutput=0`
horizontal case recorded rc 139 on x86_64; the rerun here records 136.

**Signed overflow.** The `-fwrapv` rebuild changes **876 of 4,280 functions**
([`wrapv_changed.txt`](h1/archsem/wrapv_changed.txt); every function with its source file, from
the DWARF line table, in [`functions.tsv`](h1/archsem/functions.tsv), by
[`fnmap.py`](h1/archsem/fnmap.py)): **413 translated** (396 in `pdftex0.c`, 17 in `pdftexini.c`:
gcc uses "signed overflow cannot happen" for index arithmetic everywhere) and **463 boundary**
(338 in C++ without a line table, i.e. xpdf and pdfTeX's `pdftoepdf.cc`; 125 in C, among them
`input_line`, which fills TeX's buffer from every input line, `getmd5sum`, `getfiledump`,
`gettexstring`, `makepdftime`, `open_in_or_pipe`, `read_jpg_info`, `readimage`, `fm_scan_line`,
`pdfsetmatrix` and `do_matrixtransform`). Round 2 said classification site by site "is not
needed" because `PS` makes overflow Stuck. **That was wrong for the 463** (review round 3):
`PS` is the semantics of the translated Pascal only, and ADR-015 keeps the C boundary
hand-modelled, so the rule does not reach them. They join the C-boundary work list below. One
site is reproduced: `x_over_n` (`\divide`). For `x = n = INT_MIN`, aarch64 gcc 10 compiles `(-x) div n`
as an unsigned divide and gets −1; x86_64 gcc 11 compiles it as `x div n` and gets 1. INT_MIN is
reachable from plain TeX, because `\advance` does not check integer overflow.

**`char` signedness.** The `-fsigned-char` rebuild changes **317 functions**
([`signedchar_changed.txt`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/archsem/signedchar_changed.txt)): 163 in xpdf; the rest in
kpathsea (file names and `texmf.cnf`), the font loaders (Type 1, TrueType, Type 3, encodings, map
files), libpng's text chunks, SyncTeX, and pdfTeX's string utilities. Of the translated program
only three functions change, `open_log_file`, `prompt_file_name` and `main_body` (file names and
the command line); the pool loader `loadpoolstrings`, which round 2 counted with them, is in
`pdftex-pool.c`, C generated from the pool file, so boundary (`functions.tsv`: 3 translated, 314
boundary). None of TeX's arithmetic,
token, box or paragraph procedures changes. The TeX-visible string primitives among the changed
functions were swept over all 255 non-null bytes (`\pdfescapestring`, `\pdfescapename`,
`\pdfescapehex`, `\pdfstrcmp` against `A`, `^^80` and `^^ff`, `\pdfmdfivesum`): the log is
byte-identical on both architectures (sha256 `b513a15e…`). The other changed functions are OPEN
(file names with bytes ≥ 0x80, font and map files).

**Reproduced** ([`archsem/probes/`](https://github.com/ClanClanClanClan/latex_perf/tree/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/archsem/probes/), documents and outputs; plain `pdftex`
in fresh containers of the pinned image, native aarch64 and emulated x86_64,
`SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`):

| document | member, site | aarch64 | x86_64 |
|---|---|---|---|
| `snapy0.tex`: `\pdfsnapy 0pt` (the primitive only refuses a *negative* snap glue) | division, `gap_amount` (`pdftex0.c:23709`: the only division by the snap unit [I]; the rc and the `snapy1` control are [M]) | rc 0 | **rc 136 (SIGFPE)** |
| `snapy1.tex`: `\pdfsnapy 1pt` (control) | | rc 0 | rc 0 |
| `lead/lead-{hdvi,vdvi,hpdf,vpdf}-x.tex` (review round 3): `\xleaders` over a glue of 2³¹−2 sp, a leader box of 1,598,029,823 sp, in `hlist_out`, `vlist_out`, `pdf_hlist_out`, `pdf_vlist_out` | signed overflow (`rule_wd + 10`) then division by `lq + 1` = 0 (`pdftex0.c:18140`, `18511`, `24311`, `24739`) | rc 0 | **rc 136 (SIGFPE)** |
| `lead/lead-*-xctl.tex`, `lead-*-a.tex`, `lead-*-c.tex` (controls: `\maxdimen` glue; `\leaders`; `\cleaders`) | | rc 0 | rc 0, output identical |
| `imgwide.tex`: a valid 40000×8 px JPEG, no resolution | conversion, `ext_xn_over_d` (`utils.c:405`), which only warns "number too big" | `\wd` = 32767.99998pt, **rc 1** ("Huge page cannot be shipped out") | `\wd` = −32768pt, **rc 0** |
| `jpgconv.tex`: Exif XResolution 2·10⁹ per cm | conversion, `read_APP1_Exif` (`writejpg.c:236`) | rc 0 (resolution ignored) | **rc 1** ("invalid image dimensions") |
| `jpgdiv.tex`: Exif XResolution INT_MIN / −1 | division, `writejpg.c:218` | rc 1 | **rc 136 (SIGFPE)** |
| `jpgctrl.tex`, `jpgbig.tex`, `jpgconvneg.tex` (controls) | | 0, 0, 1 | 0, 0, 1 |
| `nh-intmin.tex`: `\count1` = INT_MIN via `\advance`, then `\divide\count3 by \count1` | signed overflow, `x_over_n` | **−1** | **1** |
| (same document, 21 other operations on INT_MIN: `\divide` by −1, 2, 7, `\multiply`, `\numexpr`, `\dimexpr`, `\romannumeral`) | | equal | equal |
| `slanthuge.tex`: map line `1e30 SlantFont` | conversion, `mapfile.c:487`; then `abs(slant) > 1000`, and abs(INT_MIN) = INT_MIN passes | log warns "SlantFont value too big" | **no warning**; PDFs differ |
| `slantnan.tex`: `nan SlantFont` | same | slant 0 | slant INT_MIN; PDFs differ |
| `matnan.tex` (review round 2): `\pdfsetmatrix{nan 0 0 1}`, a link | conversion, `do_matrixtransform` | `/Rect [0 0 0 0]` | `/Rect [32645.579 …]` |
| `pdfboxnan.tex`: an included PDF whose MediaBox width is ∞ − ∞ | conversion of NaN in TeX's `round` | rc 1 | rc 1 (both refuse the image) |
| `nh-strings.tex`: the string sweep above | `char` signedness | log `b513a15e…` | identical |

All x86_64 runs are qemu-user emulation. qemu implements `cvttsd2si`'s INT_MIN and the `#DE`
trap as the x86 specification defines them, so a native amd64 host is expected to agree [I]; that
confirmation is **still open** after review round 3 (OPEN-123). It needs a native amd64 host,
e.g. a run of these probes on `tex-oracle.yml`'s runner; no native host was available to the
spike.

**What this means.**
- **The architectures differ in the compile verdict.** Round 1's "in the PDF only" was wrong.
  None of this showed on the corpus, but `\pdfsnapy 0pt` and a wide photograph are not exotic.
- **`FaithfulEngine` is per architecture in substance**: a proven verdict is a verdict for one
  architecture. The project grades locally on aarch64 and in CI (`tex-oracle.yml`) on amd64, from
  the *same* image digest: the same document can get different grades from "the" oracle (§6.4).
- **Proposed for H.2, by member (a rule per class, not per site). PENDING THE OWNER'S DECISION**
  (review round 3: round 2 stated it as settled; it is a proposal, with the TeX-level consequence
  below):
  - *UB members* (division by zero or INT_MIN/−1, out-of-range conversion, signed overflow), **in
    the translated program**: `PS` makes every such operation **Stuck**, i.e. outside the tier. That is Pascal's own reading
    of `div` by 0 and of overflow, it needs no per-architecture model, and on every run that does
    not get Stuck both binaries compute the defined C result [I: assumes the compilers are correct
    on UB-free runs]. TeX-level consequence: a document that reaches `\pdfsnapy 0pt`, overflows
    `\advance`, ships out leaders over a glue whose width plus 10 sp overflows (`\advance` of a
    skip is not range-checked either), or includes an image whose size overflows is outside the
    tier on *both* architectures.
  - *Implementation-defined and contraction members* (`char` signedness, FMA): these are defined
    behaviour that differs, so `PS` must take them from the architecture (a parameter of
    `FaithfulEngine`), or the affected output is not claimed.
  - The rule does **not** reach the C boundary. H.2's C-boundary work list is: the 227 boundary
    division and conversion sites that are not machine-checked unreachable (220 OPEN, 7 DIVERGES),
    the 463 boundary functions whose code changes under `-fwrapv` and the 314 under
    `-fsigned-char` (649 distinct, `functions.tsv`), and the unenumerated members. Each is either
    shown unreachable from the translated program's inputs or made Stuck in the boundary model.

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

### 6.4 Oracle: one image digest, two architectures, two grades [M]

`_oracle.py` records each artefact's architecture and checks it against that architecture's
fingerprints, but the project treats the digest-pinned image as **one** oracle, graded locally on
aarch64 and in CI (`tex-oracle.yml`, `ubuntu-latest`) on amd64. §5.4 shows documents whose grade
depends on which: `snapy0.tex` compiles on one and dies on the other. None of the corpus documents
graded so far is one of them, but nothing checks that. Suggested for the oracle track: make the
architecture part of the oracle's identity in every comparison of grades (a grade made on aarch64
is not evidence about amd64), or grade proven-tier evidence on both and treat disagreement as
outside the tier.

### 6.3 Already recorded elsewhere

The native backend's inherited stdin (ADR-014 draft, oracle branch C-99).

## 7. Reproducing this

**Committed evidence** (review round 1: every number above can be re-checked from the repo; review
round 2 added [`h1/archsem/`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/archsem/README.md), the census, classification and probes of §5.4,
and `diffs/r2/`, every comparison re-run with the round-2 comparator):
[`docs/v27/spike/h1/`](https://github.com/ClanClanClanClan/latex_perf/blob/6988d649a02be825729c2eefcbf3c89f9de7b0bb/docs/v27/spike/h1/README.md) holds every comparison summary (`diffs/r1/`, the narrowed
mask; `diffs/r0/`, the round-0 files these numbers were first read from), the FMA site map and the
exhaustive/search scripts with their outputs (`fma/`), the comparator and its kill-tests, the
document id lists (`tools/`), the adversarial document (`adversarial/`), the build recipe and the
emulator crash sites. `python3 docs/v27/spike/h1/verify_h1.py` recomputes this report's numbers
from those files and fails on any mismatch.

**Raw runs** (62 GB of the cache's 72 GB) are under `~/.cache/lp-spike-h1/` on the machine that ran
it. No number quoted here needs them; pruning them loses only the ability to re-run the comparator
on the raw outputs (keep `runs/` if a later step, H.4 or H.6, wants to diff against these grades):
- `src-dc8efcd4.tar` (sha256 above) and `buildpdftex.sh` (the recipe of §2.2);
- `b-arm64/` and `b-amd64/`, the build trees, with `build-arm64.log` and the amd64 logs
  (`build-amd64.fail1.log`, `.attempt2.log`, `.attempt3.log`, and `build-amd64.log` for the
  pdftex-only build: `build-amd64-retry.sh`, `build-amd64-resume2.sh`, `build-amd64-pdftex.sh`);
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

## 8. Pending owner decisions (review round 3)

H.1 raises three questions that only the owner can answer. Until he does, none of them is a
decision, and the ADR, the ledger and this report state them as proposals:

1. **The `PS` rule for C's undefined operations** (§5.4, "Proposed for H.2"): Stuck in the
   translated program; implementation-defined behaviour a parameter of `FaithfulEngine`. The price:
   `\pdfsnapy 0pt`, an overflowing `\advance`, leaders over an overflowing glue and an image whose
   size overflows are outside the tier on both architectures. The rule does not reach the C
   boundary, whose work list §5.4 states.
2. **The architecture in the oracle's identity** (§6.4): grade on one architecture and scope
   verdicts to it, or grade on both and treat disagreement as outside the tier.
3. **A native amd64 confirmation** (§5.4): every x86_64 result here is qemu-user emulation. A run
   of the committed probes on a native amd64 host (for example `tex-oracle.yml`'s runner) would
   close it; it needs a CI change or a host, which the spike does not have.

**The owner's answers (2026-09-30; recorded on `main` by a separate docs change, whose wording
wins):** (1) the `PS` rule is accepted; (2) the CPU architecture is part of the oracle's identity;
(3) the native amd64 confirmation is approved but not run: it needs a CI workflow, which needs
the owner's permission.
