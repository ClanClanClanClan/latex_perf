# Spike H.1, review round 2: C semantics the architecture defines

Backs report §5.4 ([`../../H1-report.md`](../../H1-report.md)). `python3 docs/v27/spike/h1/verify_h1.py`
checks that every site here has exactly one verdict and that the report quotes these files'
numbers.

| path | what it is |
|---|---|
| `census.py` | reads `objdump -d -l` of the two unstripped reference builds (whose stripped forms are the pinned binaries, report §2) and lists every integer-division, float-to-int, x87/`long double` and FMA instruction with its function and source line |
| `census_insns.tsv.gz` | its output: 620 DIV, 474 F2I, 524 FMA instructions; 0 `long double` |
| `census_sites.tsv` | the DIV and F2I instructions grouped into 316 sites (source line; xpdf, C++ without a line table, by function), with per-architecture instruction counts |
| `classify.py`, `classification.tsv` | one verdict and reason per site (the verdict vocabulary is in `classify.py`'s docstring) |
| `scdiff.py` | compares two builds function by function after removing addresses, branch targets, page offsets and the linker's Cortex-A53 erratum-843419 veneers |
| `signedchar_changed.txt` | functions whose code changes when the aarch64 build is repeated with `-fsigned-char` (317) |
| `wrapv_changed.txt` | functions whose code changes when it is repeated with `-fwrapv` (876 of 4,280) |
| `probes/` | the adversarial documents (`mkprobes.py`, `mkjpg.py` generate them; `matnan.tex` is review round 2's) and, under `out/`, what each architecture printed |

**How the variant builds were made.** Exactly the recipe of report §2.2 (`recipes.md`,
`buildpdftex.sh`) with two lines changed: `CXXFLAGS='-std=c++17 -fsigned-char'` (or `-fwrapv`) for
aarch64, and `CFLAGS="-g -fsigned-char"` (or `-g -fwrapv`) before the script appends `-O2`. The
build log shows `-g -fsigned-char -O2` (`-g -fwrapv -O2`) on every C compile and the flag on every
C++ compile. The builds are in `~/.cache/lp-spike-h1/b-arm64-sc/` and `b-arm64-wrapv/`
(pdftex sha256 `07c7baa3…` and `ff35daa9…`; the base build's is the pinned `cee621bf…`).
Disassembly: `objdump` from Debian bullseye's `binutils-multiarch`, in a container.

**How the probes were run.** In fresh containers of the pinned image
(`texlive/texlive@sha256:4984977c…`, `--platform linux/arm64` native and `linux/amd64` under
qemu-user), each document with `pdftex -halt-on-error -interaction=nonstopmode` (the `nh-*`
documents without `-halt-on-error`), `SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`. The run
scripts are in `../recipes.md` (they start an engine outside `_oracle.py`, so they are not
committed as executables). Outputs:
- `out/r-*.out`: every document once. It includes an `intmin` line from a first version that
  halted at the first error; that document was replaced by `nh-intmin.tex`, whose run is
  `out/q-*.out` with full logs `out/nh-intmin.*.log`;
- `out/s-*.out`: the string sweep; both logs have sha256 `b513a15e…` (`out/nh-strings.arm64.log`);
- `out/t-*.out`: the `SlantFont` map lines, with PDF hashes; logs `out/slanthuge.*.log`.
