# Spike H.1, review round 2: C semantics the architecture defines

Backs report §5.4 ([`../../H1-report.md`](../../H1-report.md)). `python3 docs/v27/spike/h1/verify_h1.py`
checks that every site here has exactly one verdict and that the report quotes these files'
numbers.

| path | what it is |
|---|---|
| `census.py` | reads `objdump -d -l` of the two unstripped reference builds (whose stripped forms are the pinned binaries, report §2) and lists every integer-division, float-to-int, x87/`long double` and FMA instruction with its function and source line |
| `census_insns.tsv.gz` | its output: 620 DIV, 474 F2I, 524 FMA instructions; 0 `long double` |
| `census_sites.tsv` | the DIV and F2I instructions grouped into 316 sites (source line; xpdf, C++ without a line table, by function), with per-architecture instruction counts |
| `classify.py`, `classification.tsv` | one verdict per site, computed from evidence only (review round 3, C-106): DIVERGES (a probe), NOT-REACHED (`reach.py`), PS-STUCK (translated scope, the proposed rule) or OPEN; round 2's hand argument is kept in the `argued` and `reason` columns as an [I] note. The vocabulary is in `classify.py`'s docstring |
| `reach.py`, `reach.out` | the machine check behind NOT-REACHED: a function is unreferenced when no instruction outside it names it, no aarch64 `adrp`+`add` pair computes its address, and its address is no 8-byte word of the stripped (pinned) binary. `reach.out` is its literal output, the two runs of `../recipes.md` concatenated: `reach.py arm64.dis ../rel/aarch64-linux/pdftex …` and `reach.py amd64.dis ../rel/x86_64-linux/pdftex …`, run in `~/.cache/lp-spike-h1/archsem/`, so the binaries are `~/.cache/lp-spike-h1/rel/aarch64-linux/pdftex` and `rel/x86_64-linux/pdftex` (the stripped pinned binaries from the release tarballs, sha256 `cee621bf…` and `1c5ff711…`); the `.dis` files are `objdump` of the unstripped reference builds (`dis.sh` in `../recipes.md`) |
| `fnmap.py`, `functions.tsv` | every function of the aarch64 build with its source file (first DWARF line record after its symbol; NOLINE for C++ without a line table) and scope (TRANSLATED = `pdftex0.c`/`pdftexini.c`), joined to the `-fwrapv` and `-fsigned-char` change lists; the totals 4,280 / 876 / 413 / 463 and 317 / 3 / 314 are recomputed from it by `verify_h1.py` |
| `scdiff.py` | compares two builds function by function after removing addresses, branch targets, page offsets and the linker's Cortex-A53 erratum-843419 veneers |
| `signedchar_changed.txt` | functions whose code changes when the aarch64 build is repeated with `-fsigned-char` (317) |
| `wrapv_changed.txt` | functions whose code changes when it is repeated with `-fwrapv` (876 of 4,280) |
| `probes/` | the adversarial documents (`mkprobes.py`, `mkjpg.py` generate them; `matnan.tex` is review round 2's; `probes/lead/` is review round 3's leaders set, 12 documents and 4 controls) and, under `probes/out/`, what each architecture printed (`probes/out/lead-*.out` for `probes/lead/`) |
| `reach_trace/` | review round 4 (MEDIUM-2): the gdb trace that ties each DIVERGES probe to its site. Every probe document was run under gdb on both architectures with a breakpoint on every DIV/F2I instruction of the candidate sites, counting hits and hits with an edge operand; `classify.py` grants DIVERGES only where the trace shows the probe's edge operand AT the site, and `verify_h1.py` re-checks that from the committed trace ([`reach_trace/RUN.md`](reach_trace/RUN.md)) |

**How the variant builds were made.** Exactly the recipe of report §2.2 (`recipes.md`,
`buildpdftex.sh`) with two lines changed: `CXXFLAGS='-std=c++17 -fsigned-char'` (or `-fwrapv`) for
aarch64, and `CFLAGS="-g -fsigned-char"` (or `-g -fwrapv`) before the script appends `-O2`. The
build log shows `-g -fsigned-char -O2` (`-g -fwrapv -O2`) on every C compile and the flag on every
C++ compile. The builds are in `~/.cache/lp-spike-h1/b-arm64-sc/` and `~/.cache/lp-spike-h1/b-arm64-wrapv/`
(pdftex sha256 after `strip`: `07c7baa3…` and `ff35daa9…`; the base build `~/.cache/lp-spike-h1/b-arm64/`, unstripped `b23c26d6…`, strips to the pinned `cee621bf…`).
Disassembly: `objdump` from Debian bullseye's `binutils-multiarch`, in a container.

**How the probes were run.** In fresh containers of the pinned image
(`texlive/texlive@sha256:4984977c…`, `--platform linux/arm64` native and `linux/amd64` under
qemu-user), each document with `pdftex -halt-on-error -interaction=nonstopmode` (the `nh-*`
documents without `-halt-on-error`), `SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`. The run
scripts are in `../recipes.md` (they start an engine outside `_oracle.py`, so they are not
committed as executables). Outputs:
- `probes/out/r-*.out`: every document once. It includes an `intmin` line from a first version that
  halted at the first error; that document was replaced by `nh-intmin.tex`, whose run is
  `probes/out/q-*.out` with full logs `probes/out/nh-intmin.*.log`;
- `probes/out/s-*.out`: the string sweep; both logs have sha256 `b513a15e…` (`probes/out/nh-strings.arm64.log`);
- `probes/out/t-*.out`: the `SlantFont` map lines, with PDF hashes; logs `probes/out/slanthuge.*.log`.
