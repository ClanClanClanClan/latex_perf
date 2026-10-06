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
- **What remains is not live data** (**corrected, C-142:** it IS live data during the run, old versions kept reachable by the extraction's fuel closures, invisible at exit; `H5-heap-design.md` §2): OCaml's peak major heap still grows with the work done
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

## Checkpoint 2 (2026-10-05): the model patch merged; the round trip's difference decoded byte by byte

Owner decisions E6–E8 of 2026-10-05 (ADR-015) apply from here. E6: the pass clause "round trip
byte-exact" means MODEL = BINARY, and the difference between the re-dumped and the shipped format
must be fully explained, byte by byte.

### The merge and the re-measurement [M]

- `h3/model.patch` is merged into `h2/` (applied with `patch -p0`; the resulting sources equal
  checkpoint 1's measured working copy file for file). `h2/pipeline.sh` also runs on Linux now
  (GNU `time`, `/proc/loadavg`, the opam switch from `OPAM_SWITCH`), for E8's CI job.
- The rebuild gives `ps.exe` `e41941bf…`: the same bytes as checkpoint 1's memory-fixed build.
  `h2/evidence/build/` records it; `verify_h2.py` pure, `--reproduce translate` and
  `--reproduce model` all pass on it.
- H.2's INITEX evidence: the model's terminal output, standard error and `texput.log` are
  byte-identical to H.2's committed ones in both configurations (only the driver's `TIME:` line
  changed).
- H.2's 178-input differential, model side re-run in both configurations against the unchanged
  binary outputs: the same totals (134 identical, 43 Stuck, 1 without a result, 0 divergent per
  configuration) and **no IDENTICAL row changed**. Two rows changed, per configuration: `dump1`
  stays Stuck with a new reason (the now modelled `wopenout` is passed; it is Stuck at a read of
  an uninitialised value in `storefmtfile`); `romn` stays without a result, now by the new
  5,000 MB memory cap instead of the 900 s time-out, and alone under 12,000 MB it is killed by the cap after 325 s (H2-report.md, "Re-measured on H.3's model").
- The round trip on the new build: exit 0, the same terminal output and `texput.log` as the
  binary, the same `texput.fmt` stream (`55629ae0…`), 79 s, peak footprint 4.1 GB
  (`h3/evidence/roundtrip/roundtrip.json`, `checkpoint_2_rerun`). **E6's clause, model = binary,
  holds on the new build.**

### E6: the re-dumped format against the shipped one, every byte [M]

`h3/tools/fmtdecode.py` decodes a decompressed pdfTeX format stream completely, following
`storefmtfile` of the tangled `pdftex.p` of r78081 (tex.web §1299ff with tex.ch, e-TeX's
`sa_root`, the MLTeX and encTeX headers, the string pool, the dynamic memory by the rover ring,
eqtb with §1493/§1494's run-length rule, `prim` and the sparse and dense hash, font info and the
23 per-font arrays, hyphenation exceptions, the trie, pdfTeX's image meta, `pdf_mem`, `obj_tab`,
counters and the ToUnicode tree, the trailer) with the C types of `pdftexd.h`/`texmfmem.h`. Every
byte of both streams is assigned to one field, and **re-encoding the decoded state with
store_fmt_file's own algorithms gives both streams back byte for byte**: that is the check that
no byte is skipped or misread. The counts the binary prints while dumping (`texput.log`: 32913
strings, 435021 memory locations, 243&403295, 29447 control sequences, 627714 words of font
info, 1141 exceptions, the trie) equal the decoded ones.

`h3/tools/fmtexplain.py` then compares the two streams element by element (an element is keyed
by what it holds — `mem[a]`, `eqtb[k]`, `hash[p]`, pool byte `i` — not by its offset) and
attributes every changed, new or removed element to a cause whose check holds
(`h3/evidence/roundtrip/fmtexplain.json`; 21 checks, all hold; **0 elements unexplained**):

| cause | what changed | the check |
|---|---|---|
| S strings | 12 new strings, 348 pool bytes, `str_ptr`, `pool_ptr` | the shipped pool is an exact prefix; the strings are the banner `load_fmt_file`'s `makepdftexbanner` makes, the 9 names `\csname` entered, `texput.log`, the format identifier |
| F | `format_ident` | it is the last string, §1508's ` (preloaded format=texput 2026.8.30)` from the job name and eqtb's `\year`, `\month`, `\day` |
| H hash | 2 home slots (3912, 3961), 7 new `hash_extra` entries (51557–51563), 7 chain links, `hash_high` 21364 → 21371, `cs_count` 29438 → 29447 | replaying `idlookup` (pdftex.p §259/§279, web2c's `hash_extra`) for the 9 names in string order on the shipped hash gives the round trip's hash, `hash_used` and `hash_high` exactly; `cs_count` is §1318's formula in both |
| E eqtb | 29 entries (20 existing, 9 new) | the differing entries are **exactly** the 29 `everyjob_names` the contract generator recorded from its own trace of the `\everyjob` replay (an independent measurement); each entry's old and new meaning is decoded in the JSON |
| R | 17 elements: run-length headers, and words that moved between explicit and copied | a function of the eqtb array (the encoder reproduces both streams), which differs only at E's entries |
| M one-word memory | 351 words of hi mem (none of lo mem), `avail`, `dyn_used` | below |

One-word memory. TeX's single-word allocator is a stack, and the round trip's free list is 626
cells pushed on the shipped list after 330 were popped (common suffix 30,854 cells). Each
differing word is in exactly one verified class: **M-live** (33 popped cells now in the new token
lists of changed entries: set equality), **M-freed** (329 cells of old meanings freed: set
equality; only 2 words differ, each the last cell of its list, only in its link, as
`flush_list` writes), **M-refcount** (9 lists whose reference count moved by exactly the change
in eqtb references), **M-scratch** (`temp_head`, `garbage`: their links point at freed cells or
at `temp_head`, as `the_toks` of an empty list leaves it), **M-temp** (305 cells popped and
pushed back, 13 of them in place — a list built from consecutive pops and returned whole by
`flush_list` restores the free list's order, so only its info fields show it was used). `dyn_used`
and `avail` follow from the free list.

M-temp's 537 info bytes are dead data (no TeX state reads a free cell's info), so a class alone
would not say why they hold the values they hold. They are therefore derived from the run
itself: `h3/tools/trace_build.py` builds a DIAGNOSTIC variant of the model (the extracted OCaml
plus a write hook in `put_cell` and a procedure stack in `callp0`; patches asserted to apply
once) which records every write into `mem` after `load_fmt_file` returns
(`h3/evidence/roundtrip/memtrace.txt.gz`, 15,956 writes into 430 words). The traced run writes the
same `texput.fmt`, terminal output and log as `ps.exe` and the binary. **Replaying those writes
on the shipped `mem` gives the round trip's `mem` exactly, and every differing word was written
during the run**; the last writer of each is recorded (M-temp: `macrocall` 276 words — the
parameter lists of the `\everyjob` code's macro calls, flushed after the call — `expand` 18,
`flushlist` 11; M-live: `strtoks` 17, `scantoks` 14, `prefixedcommand` 2).

Byte totals (`fmtexplain.json`): of the round trip's 3,338,996 elements, 3,338,224 hold the same
bytes as the shipped element with the same key. Compared naively at equal offsets the streams
differ in 5,443,537 bytes; 5,440,744 of them lie in unchanged elements that moved. The
checkpoint-1 figure, 1,881,851 differing bytes after the string pool, is reproduced and splits
into 1,880,748 moved-unchanged bytes and 1,103 bytes of changed or new elements, every one
attributed above.

What this does not establish: the write record is the model's, not the binary's. That the
binary executed the same writes is inferred [I] from the model writing the same bytes; only the
binary's outputs, not its writes, were observed. The `\time`/`\day`/`\month`/`\year` entries do
not differ because this run's clock is the shipped build's start minute (H.1); a run at another
date would add those entries to E.

### §meanings: E8's run on a GitHub-hosted runner [M]

Workflow `.github/workflows/spike-h3-meanings.yml` on branch `ci/v27165-h3-meanings` (owner
decision E8). Run 2, the measurement: https://github.com/ClanClanClanClan/latex_perf/actions/runs/37306038862
(run 1, https://github.com/ClanClanClanClan/latex_perf/actions/runs/37302258127, same result,
cap 1 GiB under RAM). Outputs: `h3/evidence/meanings/run2-37306038862/`, `run1-37302258127/`.

- **Runner** (recorded): `MemTotal` 16,372,436–16,373,452 kB, 4 cores (`nproc`), x86_64.
- **Build**: texlive-source r78081 rebuilt on the runner; the 7 translator inputs hash as
  `h2/evidence/build/provenance.json` records; `pipeline.sh` with Coq 8.18.0 / OCaml 5.2.0 gives
  the same generated Coq tree (`e9ae7712…`) and the same sources and inputs; the extracted OCaml
  tree hashes `72b2ea79…` there (**corrected, C-143:** the same value as the macOS build's, all 93 files equal; this report first said "a different value", which its own `provenance-check.txt` refutes);
  `ps.exe` is that host's compilation (`f7d6631a…`).
- **Binary side** (linux/arm64 under qemu, the h3/README.md recipe): exit 0 in 4–5 s;
  `meanings_sha256` = `4879fa65…`, **the contract's digest**, 23,519 records, all defined.
- **The model: no result. It ran out of memory in every full run.** Each run was in a systemd
  scope with `MemoryMax` = MemTotal − 2 GiB (run 2) or − 1 GiB (run 1), swap off. The cgroup's
  memory, sampled every 5 s, grew linearly until it reached the cap, and the step then ended by
  SIGTERM (exit 143):

  | run | GC | cap (bytes) | last cgroup peak (bytes) | at |
  |---|---|---|---|---|
  | run 2 full | default | 14,617,890,816 | 14,593,478,656 | 367 s |
  | run 2 full-compact | `PS_COMPACT=3` | 14,618,931,200 | 14,556,397,568 | 437 s |
  | run 1 full | default | 15,692,668,928 | 15,631,466,496 | 472 s |
  | run 1 full-compact | `PS_COMPACT=3` | 15,692,668,928 | 15,580,200,960 | 316 s |

  The cgroup's `memory.events` copy is 5 s old at the kill and shows no `oom_kill` yet; the
  kernel log was not uploaded because the step had been killed. So "killed by the cap" is
  inferred [I] from the peak reaching the cap in all four runs, and not observed directly.
- **Growth curve** (run 2 `prefixes`: the first N names, `meanblock.py`, each run to the end):

  | names | result | wall | peak RSS (`time -v`, kB) | cgroup peak (bytes) |
  |---|---|---|---|---|
  | 0 | exit 0 | 60 s | 3,106,260 | 3,105,062,912 |
  | 250 | exit 0 | 85 s | 3,741,424 | 3,804,864,512 |
  | 500 | exit 0 | 115 s | 4,441,264 | 4,512,489,472 |
  | 1,000 | exit 0 | 180 s | 6,164,572 | 6,248,902,656 |
  | 2,000 | exit 0 | 301 s | 9,157,536 | 9,317,666,816 |
  | 4,000 | killed at the cap | ≈ 497 s | — | 14,521,110,528 at the last sample |

  About 3.1 GB at 0 names plus about 3.1 MB per name between 1,000 and 2,000 names. Extrapolated
  linearly [I], the 23,519 names need about 76 GB. Compaction every third major cycle does not
  change the outcome (the compact runs died at the same level). The full runs reached the cap
  after about 2,000–2,500 names [I: from their time against the prefixes'].
- **Comparison with the binary**: not possible (no model output); the binary's digest equals
  the contract's.

**Does this touch a kill criterion?** H.3's kill is "the load cannot be made exact within the
spike": no, the load is exact. H.2's kill, "the Coq term or its extraction is intractable (> 2 h
compile or > 16 GB)", is about building the term, not running it: the build is minutes and
under 1 GB. H.5's kill is "> 200× with no profile-guided fix in sight", and its pass criterion
"≤ 60× pdfTeX per pass"; H.5 measures speed on three documents, which this run does not. The
memory is not a speed measurement, but it bears on H.5: the same run puts the model near
0.12 s per name (2,000 names in 301 s, 60 s of it load) against the binary's 23,519 names in
4–5 s under qemu, a ratio far above 200× [I: different processes, the binary emulated]. The
profile-guided fixes of checkpoint 1 removed the retention but not the growth; **the remaining
growth (≈ 3 MB per name; "not live data" was wrong, C-142) has no fix in sight within the current heap
representation**, which E8 leaves unfunded. Owner decision needed (below). *(Corrected 2026-10-06,
C-148: wrong. The retention was held by the extraction's fuel closures, not by the representation.
B2 removes it with coq-core's persistent arrays unchanged (§"H.5 stage 2", below).)*

### H.3's criteria at checkpoint 2

| criterion (verbatim) | state |
|---|---|
| "round trip byte-exact" | **met** in E6's reading (model = binary) on the checkpoint-2 build; and the difference from the shipped format is accounted for byte by byte (above) |
| "meanings byte-identical to the contract generator's" | **MET at H.5 stage 2 (2026-10-06) on the B2 model build** (`ps.exe` `cae7a953…`): the full dump is IDENTICAL to the binary's, digest `4879fa65…` (§"H.5 stage 2", below). At checkpoint 2 it was **NOT MET**: the binary side reproduces the contract's digest `4879fa65…`; the model's full dump ran out of memory at ≈ 14.6 GB and ≈ 15.6 GB on 16 GB runners (E8, §meanings), so there is no model output to compare. The CI prefix runs up to 2,000 names finished but were not compared with the binary; one local 50-name prefix (arm64, `ps.exe` `e41941bf…`) is byte-identical to the binary's run of the same input (`h3/evidence/meanings/local-prefix50/compare.json`) |
| "F7 explained" | explained by H.1 (C-100); not re-derived by the model |
| kill: "the load cannot be made exact within the spike" | **not fired** |

## H.5 stage 2 (2026-10-06): the meaning dump on the B2 model build [M]

The heap fix the owner funded (E11) was built as candidate B2 (H5-heap-design.md §8): the
interpreter's fuelled block was restructured at the source, and proved equal to the pre-B2 term
by reflexivity (`h2/coq/B2Equiv.v`). There is no new realizer, no change to `Extract.v`, and
neither T1 nor T2. This is the **model build**, `h2/evidence/build/provenance.json`: `ps.exe`
`cae7a953…` (macOS arm64) and extracted tree `dbace323…`. It is not a profiling variant.

**The round trip, re-run** (`h3/evidence/roundtrip/roundtrip.json`, `h5_stage2_b2_rerun`):
- exit 0, and the same terminal output and `texput.log` as the binary;
- the same `texput.fmt` stream, `55629ae0…`;
- 78.0 s user CPU, peak footprint 1,624 MB (checkpoint 2's build: 4,102 MB).

**E6's clause, model = binary, holds on the B2 build.**

**E8's workflow, run 3** (https://github.com/ClanClanClanClan/latex_perf/actions/runs/37397064131;
`h3/evidence/meanings/run3-37397064131/`). The runner builds the model with `pipeline.sh`: the
same generated and extracted trees as the committed build, `differs … in: []`. Its OCaml is 5.2.0
**without flambda** (`ocamlopt -config`), on x86_64, with 4 cores and 16 GB. So B2's memory
property is measured on the other compiler as well (H5-heap-design.md §5 B(d)).

The memory against names, on the same runner type as run 2:

| names | run 2 (pre-B2): wall, peak RSS (`time -v`, kB) | run 3 (B2): wall, peak RSS (kB) |
|---|---|---|
| 0 | 60 s, 3,106,260 | 50 s, 1,422,348 |
| 250 | 85 s, 3,741,424 | 71 s, 1,587,252 |
| 500 | 115 s, 4,441,264 | 95 s, 1,721,560 |
| 1,000 | 180 s, 6,164,572 | 151 s, 1,850,744 |
| 2,000 | 301 s, 9,157,536 | 251 s, 1,931,828 |
| 4,000 | killed at the cap (≈ 14.5 GB) | 482 s, 2,017,664 |

Between 2,000 and 4,000 names the peak grows by 86 MB, which is ≈ 43 kB per name, against ≈ 3.1 MB
per name before B2. What is left is the I/O lists (H5-heap-design.md §2.5): the log kept in memory
at 24 bytes per byte. At 4,000 names, the margin cost is ≈ 0.116 s of wall time per name.

**The full meaning dump on the model build, local** (`h5/evidence/stage2/fulldump/`; macOS arm64,
`ps.exe` `cae7a953…`, all 23,519 names, under `capped.sh` with a 4,000 MB cap):
- **finished, exit 0**: 2,564.9 s user + 107.7 s sys = **2,672.6 s CPU** (44.5 min), 3,623 s wall;
- **peak footprint 2,463 MB** (maximum resident set 2.49 GB): 1,974 MB at 1 min, 2,243 MB at
  10 min, 2,339 MB at 30 min, 2,463 MB at the end;
- the one-minute load average was 8.3–283 (median 171, 63 samples): the machine was shared, so
  the wall time is an upper bound;
- **`meancompare`: IDENTICAL to the pinned arm64 binary's run of the same input**: the same exit
  status, terminal output, `texput.log` (`335b024c…`, 7,014,728 bytes) and clock readings, and
  23,519 records, all defined, on both sides. **The model's `meanings_sha256` is `4879fa65…`, the
  contract's.**

**The full meaning dump on the runner** (run 3, job `meanings-full`,
`h3/evidence/meanings/run3-37397064131/full/`): x86_64, OCaml without flambda, `ps.exe` this
host's compilation of the same extracted tree (`274ae67e…`), under the cgroup cap of 14.3 GB:
- **finished, exit 0**: 2,473.6 s user + 1.3 s sys, 2,476 s wall;
- peak RSS 2,466,032 kB; cgroup peak 2,522,820,608 bytes; 0 OOM kills;
- **`meancompare`: IDENTICAL** to the binary's run on the same runner (arm64 under qemu, exit 0
  in 6 s); the model's digest, the binary's and the contract's are all `4879fa65…`.

So the result holds on both compilers (flambda on macOS arm64, without flambda on Linux x86_64)
and on both hosts.

**H.3's meanings clause, "meanings byte-identical to the contract generator's", is MET on a model
build**: the build `verify_h2.py` checks, not a profiling variant.

## Open

- ~~The meaning comparison: blocked by memory.~~ Closed at H.5 stage 2 (the owner funded the
  heap fix, E11): the full dump on the B2 model build is IDENTICAL to the binary's (§"H.5 stage 2").
- Done at checkpoint 2: the owner's reading (E6: model = binary) and the full decoding of the
  round trip's difference.
- The amd64 configuration of the round trip (only arm64 here).
- Peak memory under persistent arrays (H.5's question): answered for B2: 2.5 GB for the full dump
  locally, and 2.0 GB at 4,000 names on the runner (§"H.5 stage 2"). Speed is H.5's (H5-heap-design.md §3).
