# Foundation spike, step H.3: loading the real `pdflatex.fmt`

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123),
step H.3 of the ADR-014 draft §9, run on the program of [H.2](H2-report.md). Code and evidence:
[`h3/`](h3/).

**Work (ADR-015 D3, verbatim):** "load the real `pdflatex.fmt` in the model; round-trip
`store_fmt_file`; meanings of the kernel names; locate F7's byte difference".
**Pass criterion (verbatim):** "round trip byte-exact; meanings byte-identical to the contract
generator's; F7 explained".
**Kill criterion (verbatim):** "the load cannot be made exact within the spike".

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## Checkpoint 1 (2026-10-02): the load and the round trip are exact; the meaning dump ran out of memory, diagnosed

| criterion | state |
|---|---|
| round trip byte-exact | **met in the form the binary itself satisfies** [M]; the literal form `store(load(x)) = x` is not what the binary does (below): an owner reading is needed |
| meanings byte-identical to the contract generator's | **not yet**: the harness reproduces the generator's digest with the binary [M]; the model's first full run exceeded the machine's memory; diagnosed and partly fixed [M]; the full run is not done |
| F7 explained | explained by H.1 [M] (C-100: the only run-dependent bytes are the INITEX run's clock); not re-derived by the model |
| kill criterion | **not fired**: the load is exact (below) |

### The run

`pdftex -ini` (the command line C main was measured with, so `CMain.v` applies unchanged), its
first terminal line `&pdflatex \dump`: INITEX loads the format named after `&`, runs `\everyjob`,
and `\dump` stores a new format, `texput.fmt`. The run identity is H.2's base (`diff/base.spec`)
plus two measured inputs: kpathsea's `kpse_find_file("pdflatex.fmt", kpse_fmt_format, 1)` =
`/usr/local/texlive/2026/texmf-var/web2c/pdftex/pdflatex.fmt` (`kpsewhich -engine=pdftex
-progname=pdftex -format=fmt` in the pinned image), and that file's decompressed stream.

**Decompression (TB-7).** The shipped `pdflatex.fmt` (sha256 `a476533c…`, 3,658,242 bytes) is a
gzip stream; pdfTeX reads it through zlib's `gzread`. Decompression is outside the model: the run
is given the stream. Three inflaters agree on it (11,621,149 bytes, sha256 `6fccc888…`): Python's
`gzip` and Apple's `gzip` (both zlib), and BusyBox's `gunzip` (its own inflate, not zlib) [M]. The
independent pair is zlib and BusyBox.

### The externals the load and the dump call (`h3/model.patch`, `Boundary.v`) [R]

Each modelled from its C source of r78081 (texmfmp.h, texmfmp.c, openclose.c, writeimg.c,
tounicode.c, cpascal.h), with the environment class of H.2:
- `wopenin` (`open_input(&f, kpse_fmt_format, "rb")` then `gzdopen`): `fullnameoffile`,
  `kpse_find_file` from the run's table (a query not in it is Stuck), the `./` rule, `xfopen` from
  the run's file system, `nameoffile` reallocated with its first cell never written; `wopenout`
  (`open_output` + `gzdopen` + `gzsetparams`): the H.2 rule for a new single-component name; the
  model keeps the uncompressed stream `gzwrite` receives; `wclose` (`gzclose`);
- `undumpthings`, `undumpint`, `undumphh`, `undumpcheckedthings`, `undumpuppercheckthings`
  (`do_undump`: `item_size * nitems` bytes, FATAL on a short file, `swap_items` on a
  little-endian host: the file is big-endian; the checked forms' FATAL ranges): Stuck where C is
  FATAL; `dumpthings`, `dumpint`, `dumphh` (`do_dump`): a never-written byte is the binary's
  garbage, so dumping one is Stuck;
- `undumpimagemeta`/`dumpimagemeta` (no images: images are re-read from their files on load, not
  modelled, Stuck), `undumptounicode`/`dumptounicode` (the glyph-to-unicode AVL tree; the format
  holds one: its records are kept and re-dumped in `strcmp` order, which the model requires the
  undumped names to be in already, else Stuck);
- `strcmp` (equal strings: 0; different: glibc's value, Stuck), `strlen`, `strcpy`, `ucharcast`,
  and `getcreationdate` (texmfmp.c: `start_time_str` of `makepdftime(start_time, utc)`; from the
  real clock, Stuck); `TEXMFENGINENAME` is now the string literal web2c's C has (texmfmp.h:54),
  not an external.

20 externals added: **43 of the program's 188 externals are modelled.** The evaluation-order
analysis now knows which externals have no I/O effect (`stdout`, `stringcast`, ...) and which read
their arguments only (`undumpimagemeta`, ...): 25 sites of 45,756 pairs are Stuck (29 of 45,742 at
H.2); `loadfmtfile` and `openfmtfile` had three false conflicts.

### Round trip [M]

The model and the pinned arm64 binary (same run identity, clock shim) both exit 0 and write the
same terminal output, the same `texput.log` and **the same `texput.fmt` stream: 11,621,681 bytes,
sha256 `55629ae0…`** (the binary's file gunzipped). Every one of the 11.6 MB passes through the
translated `loadfmtfile` and `storefmtfile` and the modelled (un)dump externals, so a decoding or
encoding defect anywhere would show (`h3/evidence/roundtrip/`). The model build that measured it
(`17677bfb…`) and the memory-fixed build (`e41941bf…`, below) give the same bytes; the fixed build
takes 100 s wall, peak 1.5 GB.

**The binary's own round trip is not the identity**, so `store(load(x)) = x`, the ADR-014
draft's wording (§3.2), is not a property pdfTeX has on this command line
(`h3/tools/fmtdiff.py`, `h3/evidence/roundtrip/fmtdiff-shipped-vs-roundtrip.json`): the shipped
format's 32,901 strings are an exact prefix of the round trip's 32,913; the 12 new strings are
this run's (the `pdftexbanner` string, nine `sys_if_shell...` names that `\everyjob` creates with
`\csname`, `texput.log`, and the new format identifier ` (preloaded format=texput 2026.8.30)`);
`hash_high` grows by 7; after the string pool the two streams have 10,646,962 and 10,647,098
bytes and differ in 1,881,851 bytes at equal offsets, which this checkpoint has **not decoded**
(the shifts follow from the new hash entries and `\everyjob`'s assignments [I]). So the criterion
is met in the form the binary satisfies (the model's round trip equals the binary's, byte for
byte), and its literal form is not; whether that is the criterion's meaning is the owner's call.

### Meanings of the kernel names

The contract generator (`scripts/tools/gen_contract.py`, M1 slice 1) dumps `\meaning` of every
one of the 23,519 kernel names in format state and records the sha256 of the sorted
`name<TAB>meaning` lines (`corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json`,
`4879fa65…`). The H.3 harness generates the same dump block with the generator's own
`dump_block`, feeds it to `pdftex -ini` after `&pdflatex` on the terminal, with the generator's
environment (`SOURCE_DATE_EPOCH=0`, `FORCE_SOURCE_DATE=1`, `max_print_line=1000000`,
`error_line=254`, `half_error_line=238`, `openin_any=openout_any=p`), and recomputes the digest
with the generator's own `parse_dump` (`h3/tools/meandigest.py`). **The pinned binary run this way
gives `4879fa65…`, the contract's digest exactly** (23,519 records, all defined, no error) [M].

**The model's first full run exceeded the machine's memory** [M]: started at 22:38, it was killed
after 10.5 h, having used 31 minutes of CPU, in uninterruptible state, with 20 GB of swap in use.
This is a measurement, not noise, and it was diagnosed on bounded prefixes of the dump (0 to 2,000
names) under a 4–9 GB resident cap and a wall-clock time-out (`h3/tools/capped.sh`;
`evidence/memory/curve.tsv`):

- **The cause was retention, not the data.** The model's heap is persistent arrays (Coq's
  `PArray`, coq-core's `Parray`: a write turns the old version into a diff node pointing at the
  new one, so an old version that stays reachable keeps every later write alive). Four things kept
  old versions reachable, each found by measurement (`Obj.reachable_words` per heap block; an
  instrumented `Parray` that reports a read through a superseded version):
  1. `new_block` stored a small block's only chunk as `PArray.make`'s *default*, which a
     persistent array keeps for ever: every scalar global (`curchr`, `curcs`, `avail`, `tally`,
     ...) kept every write ever made to it (one such global held 2.1 M words after 500 names);
  2. the initial heap was a module-level constant of the extracted program, so its version, and
     through it every block's first version, was never collected;
  3. `callp`'s return closure referred to the caller's state for the whole call;
  4. `ERealloc` read the old block's size through a superseded heap (one of the two stale reads in
     a run).
  After the four fixes the live data at exit is flat: 73.5 M words with 0 names, 74.0 M with
  500, 75.4 M with 2,000 (before: 81.6 M and 97.0 M with 0 and 500, and growing).
- **What remains is not live data:** OCaml's peak major heap still grows with the work done
  (385 M words with 0 names, 558 M with 500, 1,147 M with 2,000), independent of
  `space_overhead` 120 or 40 and the minor heap size; periodic compaction lowers the resident peak
  (5.8 GB → 3.6 GB at 2,000 names) but not the heap high-water mark [M]. Every write promotes its
  diff node and boxed cell to the major heap through the old version's write barrier [I]; the
  heap representation, not TeX, sets this cost.
- A full run of all 23,519 names was started under a 9 GB cap and a 3 h time-out, with compaction
  every third major cycle, and stopped by hand after 4 minutes: the machine was under memory
  pressure from other work (another process at 8 GB, 6.5 of 7 GB of swap in use) and the run's
  resident size fell to 40 MB, i.e. it was being paged out. That showed the cap itself was wrong:
  `ps`'s resident size drops when the system pages a process out, so it cannot cap a process under
  pressure. `capped.sh` now polls the physical footprint (`top`'s MEM: resident, compressed and
  swapped). The resident peaks in `curve.tsv` were taken under light pressure and are upper-bound
  indications only; the live-word counts (the GC's own, after a compaction at exit) are the
  measurement. The full run is the next checkpoint's, on a machine with the memory free.

### Is this a kill criterion?

- **H.3's kill** is "the load cannot be made exact within the spike". It has **not fired**: the
  load is exact, byte for byte against the binary, over the whole format.
- **H.5's kill** is "> 200× with no profile-guided fix in sight" (speed); H.5 has not been
  measured. The memory finding is the kind of profile-guided fix that criterion means: four causes
  found by measurement and fixed, one (GC pressure from persistent arrays) located and not yet
  fixed. It bears on H.5, and it is recorded here so that it is not a surprise there.
- **H.2's kill** ("> 2 h compile or > 16 GB") is about the Coq term and its extraction, not runs.
- Every long run from now on carries a memory cap and a wall-clock time-out.

### What this checkpoint commits, and what it does not

- `h3/model.patch`: the model changes since H.2 (`h2/` at `0ab6005e`), exactly as built and
  measured here, as a patch. `h2/` itself is unchanged in this checkpoint, because H.2's committed
  evidence is bound by sha256 to `h2/`'s sources (`verify_h2.py`); the patch is merged into `h2/`
  at the next checkpoint, together with a re-run of H.2's INITEX evidence and differential on the
  new build.
- `h3/evidence/roundtrip/`: the run's identity template, the model's and the binary's terminal
  output and log, and the format comparison; the 11.6 MB format streams by sha256 only.
- `h3/evidence/memory/`: the curve and the per-block measurement.
- The binary-side commands (the round trip, the meaning dump) start the engine outside
  `_oracle.py`, so as in H.1 and H.2 they are recipes ([`h3/README.md`](h3/README.md)).

## Open

- The meaning comparison (the full run, then a per-name comparison if the digest differs).
- The owner's reading of "round trip byte-exact" (model = binary, met; or `store(load(x)) = x`,
  which pdfTeX does not satisfy here); and a full decoding of the round trip's difference after
  the string pool.
- The amd64 configuration of the round trip (only arm64 here).
- Peak memory under persistent arrays (H.5's question).
