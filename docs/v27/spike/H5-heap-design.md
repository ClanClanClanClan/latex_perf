# Foundation spike, step H.5, stage 1: where the model's memory and time go, and which heap representation to fund

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123).
**Owner decision (2026-10-05, to be recorded as ADR-015 E11):** fund a time-boxed fix of the heap
representation, the "profile-guided fix" that H.5's kill criterion allows for. Stage 1 (this
document): profile and design, by the end of 2026-10-06. Stage 2: implement and measure, by the end
of 2026-10-10. If at the end of the box no representation gives memory that does not grow with
the work done and a speed at or below 200× pdfTeX on H.5's documents, H.5's kill criterion fires,
and that is reported as such.

**H.5, verbatim (ADR-015 D3, the ADR-014 draft §9's table):**
- work: "speed: the one-line document, the 12-page synthetic paper, a 40-page corpus paper; cold and from a preamble snapshot";
- pass criterion: "≤ 60× pdfTeX per pass";
- kill criterion: "> 200× with no profile-guided fix in sight. Fallback: a verified-refinement fast interpreter becomes its own project".

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred. Every number below
comes from a command in §1. Code and evidence: [`h5/`](h5/).

## Summary

1. **The memory growth is retention, and it is live data during the run** [M]. With coq-core's
   persistent arrays, a forced full GC in the middle of a run finds 211–245 M words (1.7–2.0 GB)
   reachable, but not from the current state. The extraction keeps them alive. `ExtrOcamlNatInt`'s
   realizer of `match` on the fuel wraps every fuelled function's body in a closure that holds
   the function's state argument across each non-tail call. Through the persistent array's chain
   of versions, an old state holds every write made since it. At exit the stack is gone, so H.3's
   measurement at exit could not see any of this: its "not live data" was an inference, and it
   was wrong (C-142).
2. **An in-place array that refuses access to a superseded version removes the growth** [M]. The
   live words stay at 74.2–74.8 M from the end of the format load to the 1,000th name. The top of
   the major heap is 137 M words at 250 names, against the current 472 M (773 M at 1,000 names).
   Over the whole 23,519-name dump, the only growth left is the I/O lists: the output kept in
   memory and the consumed input still referenced, 24 bytes of heap per byte read or written.
   No run read a superseded version. Every instrumented run, persistent or in place, recorded 0
   reads through an old version.
3. **The time goes to integer conversions, not to the heap or to interpreting the IR** [M].
   - In the current build, 40 % of the CPU samples during the format load are `Uint63`/`Sint63`
     ↔ `Z` conversions from Coq's library. In the extracted code these are 63-step loops, run
     mostly for the IR's integer literals (`zi`).
   - Another 34 % are zarith and extracted `BinInt`/`BinPos` code. This is mostly the same
     conversions, plus the `Z` functions that `ExtrOcamlZBigInt` does not realize (`land`,
     `lor`, `testbit`, `quot`/`rem`), which the extracted code computes bit by bit with one
     division per bit.
   - The interpreter takes 2–3 %, the persistent arrays 2 %, and the GC 4 % during the load and
     27 % later in the run.
4. **O(1) realizers for those functions, together with A, make the model 10× faster** [M].
   Median CPU time at 250 names, in interleaved rounds:
   - 90.7 s for the current build;
   - 83.3 s with in-place arrays (A);
   - 29.1 s with the conversion realizers (T1);
   - 19.7 s with T1 and A;
   - 8.9 s with T1, the `Z` realizers (T2) and A.

   These are profiling builds, not model builds. In every call of a whole run, each realizer
   was compared with the extracted Coq definition: no mismatch. **With T1, T2 and A, a
   profiling build runs the whole dump** (345 s, 2.0 GB). It is IDENTICAL to the pinned binary,
   and its digest is the contract's `4879fa65…`.
5. **Speed against H.5: below the kill line on the proxy, not yet at the pass line**
   [M on a proxy, I for H.5]. H.5's documents cannot run yet (the PDF path's externals are
   Stuck), so the meaning dump is the proxy. The current model is 183× pdfTeX on the format load
   and ≈ 1,090× per name. With A, T1 and T2 it is 25× on the load, 46× over 1,000 names and
   ≈ 103× per name. The pass line is ≤ 60× and the kill line > 200×.
6. **Platform:** the extracted OCaml tree is the same on the Linux runner and on macOS: all 93
   files, `72b2ea79…` on both [M]. The H.3 report says otherwise; that sentence is a
   transcription error (C-143). The only build output that differs is `ps.exe`, the native code
   of two hosts.
7. **Recommendation:** candidate A, an in-place `PArray` realizer that fails closed on a
   superseded version. It keeps the Coq term unchanged and adds to the trusted base a realizer
   whose model is proved in Coq. T1 and T2 ship with it, in the same `Extract.v` change. It is
   the only option within the box that stops the growth by construction and moves the speed by
   a factor. It does not reach ≤ 60× on the marginal cost (§3.3, §6), and two owner questions
   remain (§6).

## 1. Method

**Builds.** The model is the H.3 checkpoint-2 build: `ps.exe` `e41941bf…`, generated Coq tree
`e9ae7712…`, extracted OCaml tree `72b2ea79…` (`h2/evidence/build/provenance.json`). Each profile
uses a **profiling variant** of that extracted tree, made by
[`h5/tools/mkvariant.py`](h5/tools/mkvariant.py). Every textual replacement in it is asserted to
match exactly the expected number of times. Regenerating `prof` and `t2` with the committed tools
reproduces the measured source trees byte for byte (`t1`: see `h5/evidence/exe-sha256.txt`). A variant is never a model build: it exists only to measure. The variants:

| variant | what changes against the model build | `ps.exe` sha256 |
|---|---|---|
| `prof` | coq-core's `Parray` replaced by [`parrayc.ml`](h5/tools/parrayc.ml): the same algorithm (coq-core 8.18.0, module `Parray` of its kernel library) with counters (sets, gets, makes, reroot steps, reads through a superseded version). `PS_PARRAY=linear` switches to the **in-place** mode: a set mutates the array, the old version becomes `Invalid`, and any later access to it stops the run (exit 4). Also a GC probe ([`prof.ml`](h5/tools/prof.ml)) at the C boundary: `PS_PROBE=S` prints `Gc.quick_stat` every S s; `PS_PROBE_DEEP=1` adds a forced full major GC, the live words, the words reachable from the **current** state, and the stdin bytes not yet read | `dd152947…` |
| `t1` | `prof`, plus O(1) realizers of `Uint63.to_Z`, `Uint63.of_Z` and `Sint63.to_Z` ([`zr.ml`](h5/tools/zr.ml)), with the extracted Coq definitions kept: `PS_T1CHECK=1` compares every call and stops on a mismatch (exit 5) | `2713803c…` |
| `t2` | `t1`, plus O(1) realizers of the `Z` functions that `ExtrOcamlZBigInt` leaves to the extracted Coq code: `Z.land`, `Z.lor`, `Z.lxor`, `Z.testbit`, `Z.quotrem` (thus `Z.quot`, `Z.rem`) and `Z.of_nat`, under the same check | `2639e188…` |

**Inputs.** The meaning dump of H.3 (`h3/tools/meanblock.py`, from the committed kernel contract)
for the first 0, 50, 250 and 1,000 names and for all 23,519. The run identity is H.3's
(`h3/evidence/meanings/model.spec.template`).

**Runs.** Each run goes through [`h5/tools/run.sh`](h5/tools/run.sh) under
[`h3/tools/capped.sh`](h3/tools/capped.sh), with a physical-footprint cap (3–8 GB) and a time-out:

```zsh
zsh h5/tools/run.sh NAME EXE PREFIX CAP_MB TIMEOUT_S [ENV=VALUE ...]
# e.g. the in-place variant with the conversion realizers on the first 1,000 names:
zsh h5/tools/run.sh t2lin-p1000 prof-t2/ps-t2.exe p1000 6000 2400 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
```

The time profiles are macOS `sample PID SECONDS` on a running model. They are grouped by cost
class ([`selfprof.py`](h5/tools/selfprof.py), top-of-stack samples) and by nearest
non-matching caller ([`callers.py`](h5/tools/callers.py); OCaml frames without frame pointers
make the caller attribution partial).

**Comparison.** [`cmp.sh`](h5/tools/cmp.sh) runs H.3's `meancompare.py` on a model run and on the
pinned arm64 binary's run of the same input (the `h3/README.md` recipe, repeated in [`h5/README.md`](h5/README.md)). Its result is IDENTICAL only when the exit status, the terminal output,
every file written and the clock readings are byte-identical; it also checks the contract's
digest. **Binary timing** (the other recipe there): five runs inside one container on
colima's native arm64 VM. The clock shim fakes the wall clock, so the user and system CPU times are
what is measured.

**The machine.** The laptop: Apple arm64, 8 cores, 24 GB, shared with other work. Its load
average moved between 13 and 177 (`load.txt` of each run). So **wall times are not used. Every
model time below is the process's own CPU time** (`Sys.time` at the end of the run), and
variants are compared only in interleaved rounds (§3.2). That is enough for ratios between
variants. It is not the quiet-machine speed measurement E4 asks for H.5.

**A defect found in my own harness and fixed (C-144).** My first `run.sh` put `/usr/bin/time -l`
between `capped.sh` and the model, so the cap polled the footprint of `time` (0 MB) and not of
the model (3.3 GB). The run was watched and finished. `capped.sh` now polls, and on a kill stops,
the whole process tree it started. Tested: a 400 MB child under `/usr/bin/time` with a 200 MB cap
is killed at 406 MB.

## 2. Memory profile

### 2.1 What is live during a run (persistent arrays: the current representation) [M]

Forced full GC at the C boundary (`PS_PROBE_DEEP=1`, `prof` variant, first 50 names; the runs
were stopped by hand once the probes had been read, because a probe every 5–15 s left no time for
the run itself):

| point in the run (run) | CPU s | array sets so far | live words | reachable from the current state | program constants | **reachable only from elsewhere** |
|---|---|---|---|---|---|---|
| end of the format load (`prof-p50-deep-probe5-aborted`) | 63.8 | 25,369,339 | 269,107,743 | 57,337,394 | 298,780 | **211,471,569** |
| later, before the first name is read (`prof-p50-deep-probe15-aborted`) | 269.2 | 30,058,244 | 314,702,156 | 69,219,541 | 298,780 | **245,183,835** |

So 79 % of the live heap is reachable but not from the state the program is computing with. It is
live, not garbage: a full major GC cannot free it. At exit it is gone. That is why H.3's
checkpoint-1 measurement found "live data at exit flat" (73.5 M words at 0 names, 75.4 M at
2,000), and why it inferred that the remaining growth was "not live data". That inference is
wrong: C-142.

### 2.2 What keeps it alive [M, R]

`ExtrOcamlNatInt` extracts `match fuel with O => a | S f => b` as
`(fun fO fS n -> if n=0 then fO () else fS (n-1)) (fun _ -> a) (fun f -> b) fuel`. OCaml 5.2's
`ocamlopt`, without flambda, keeps `fS` as a heap closure that captures every free variable of
`b`, including the state `st`. Here is `exec_list` in `-dcmm` (`h5/evidence/profile/exec_list.cmm`):

```
(function camlInterp.exec_list_1536 (fuel all rest st env)
 (let fS (alloc ... "camlInterp.fS_5274" ... all rest st)        <- st captured
   (if (== fuel 1) ... (app "camlInterp.fS_5274" (+ fuel -2) fS))))
(function camlInterp.fS_5274 (f env)
   ... (app "camlInterp.exec_1534" f (load (load env+48)) (load env+56) ...)   <- exec s st
   ... (app "camlInterp.exec_list_1536" f (load env+40) ...)                   <- env used after the call
```

The closure's environment is used after the call `exec f s st` returns: it reads `all` and `rest`.
So the environment, and the `st` inside it, stays reachable for the whole execution of the
statement `s`. The same holds for every fuelled function of `Interp.v`. At any moment, each
active frame of the interpreter therefore holds the state with which its current statement
began. For the frames around TeX's main loop, that is a state from the start of the run.

A persistent array (coq-core `Parray`) turns the version written over into
`Updated (i, old value, newer version)`. An old version thus points *forward* to every later
version, and holding the old version holds every write made since. So the retained memory grows
with the number of writes, which is the 3.1 MB per name measured on the GitHub runner (H.3
§meanings). The four leaks fixed by C-112 were particular instances of this mechanism; this one
is general, and the earlier fixes could not remove it.

### 2.3 Every answer to "what retains memory?" [M]

| suspect | measured | verdict |
|---|---|---|
| persistent-array version chains | 211–245 M words retained beyond the current state (2.1). In place, where a superseded version holds nothing: −0.3 M to +0.1 M words over 1,000 names (2.4). Over the whole dump, the consumed input still referenced by old states, 3 words per byte read (2.5) | **the cause** |
| closures and continuations | they are the *roots* of the retention (2.2); their own size is small: with in-place arrays the same closures exist and nothing beyond the current state is live | roots, not volume |
| fuel or recursion depth | fuel is an OCaml `int`; the depth of the OCaml stack is bounded by TeX's call depth; nothing grows with the names once the chains are gone (2.4) | no |
| `Z` and `nat` boxing | zarith keeps small integers unboxed. A written cell is a `KInt z` block (2 words) plus its array slot, about 3 words for a 4-byte C cell. This is constant per cell, not per write | constant, not growth |
| the string pool | `str_pool` (block 837) is 7.9 M words at 250 names, sized by `pool_size`, not by the work | constant |
| I/O buffers | the `io` record holds **35.1 M of the 73.7 M live words** (`PS_MEMDIAG`, 250 names), nearly all of it the decompressed format stream, kept as a `list Z` in `io_gz` for the whole run (11.6 M bytes at 3 words each: 34.9 M) [M, I]. The output (`io_out`) is a list of bytes, 3 words per byte written: this grows with the *output* (the 7.0 MB log of the full dump ≈ 21 M words) | constant (`io_gz`) and output-proportional (`io_out`). Both can be reduced, neither is the defect |

### 2.4 The in-place representation, measured (`PS_PARRAY=linear`) [M]

| run | variant | names | live words, start → end of the names | top of the major heap (words) | peak footprint | `meancompare` |
|---|---|---|---|---|---|---|
| `prof-p250-pers` | `prof`, persistent | 250 | — | 471,547,057 | 3,768 MB | outputs byte-equal to the current build's (`base-p250`: IDENTICAL) |
| `prof-p250-lin` | `prof`, in place | 250 | — | 136,580,273 | 1,237 MB | outputs byte-equal to the current build's |
| `prof-p1000-pers` | `prof`, persistent | 1,000 | — | 772,873,393 | 6,070 MB | IDENTICAL |
| `lin-p1000-deep` | `prof`, in place, deep probes | 1,000 | 74,217,772 → 74,473,906 (and 74.2–74.8 M at every probe) | 112,592,754 | 1,906 MB | IDENTICAL |
| `t2lin-p1000` | `t2`, in place | 1,000 | — | 126,900,372 | 1,073 MB | IDENTICAL |

CPU times are in §3.2: a single run's CPU time depends on the machine's load, so the times are
compared only in interleaved rounds.

With the chains gone, "reachable only from elsewhere" is between −0.3 M and +0.1 M words at every
probe: the program constants are counted twice, so a small negative number means nothing is
retained. 0 reads through a superseded version occurred in every in-place run: such a read would
have stopped the run with exit 4. In the persistent runs `reroot` never walked a single `Updated`
node: 0 reroot steps in 45.3 M sets and 114.8 M gets. So the program uses its arrays linearly
in practice. It keeps old versions *alive*, but it never *reads* one.

### 2.5 The whole dump, in place, with T1 and T2 (a profiling variant, not the model build) [M]

`t2lin-pall`: all 23,519 names, `t2` variant, in place. **Finished: exit 0, 345.0 s of CPU (420 s
wall, at a load of 35–70), peak footprint 1,991 MB, top of the major heap 267 M words. `meancompare`:
IDENTICAL to the pinned binary**: the same terminal output, the same `texput.log`
(`335b024c…`), the same clock readings, and the log's `meanings_sha256` is `4879fa65…`, the
contract's. The current build needs about 76 GB for the same run (H.3 §meanings).
This is a profiling variant, so it does **not** meet H.3's meanings clause. The model build of
stage 2 must repeat it.

`t2lin-pall-deep`: the same run with a forced full GC every 60 s (`PS_PROBE_DEEP=1`; finished,
exit 0, 373.8 s of CPU of which 35.1 s are the probes; peak footprint 3,214 MB, which the probes'
heap walks inflate). What is live, and why:

| CPU s | array sets | live words | reachable from the current state | reachable only from elsewhere | stdin bytes not yet read |
|---|---|---|---|---|---|
| 57.8 | 165,614,154 | 88,297,822 | 86,776,334 | 1,222,708 | 3,464,424 |
| 108.9 | 295,211,535 | 90,977,932 | 88,238,116 | 2,441,036 | 3,058,316 |
| 166.6 | 451,377,843 | 94,285,693 | 89,904,571 | 4,082,342 | 2,511,206 |
| 223.5 | 597,092,876 | 97,642,486 | 91,047,264 | 6,296,442 | 1,773,190 |
| 279.6 | 752,785,578 | 101,133,721 | 92,500,561 | 8,334,380 | 1,093,868 |
| 328.4 | 875,977,404 | 104,031,606 | 93,645,738 | 10,087,088 | 509,624 |
| end of the run | 984,515,932 | 94,698,457 | 94,684,344 | −284,667 | 0 |

Over 820 M array writes the live words grow by 16 M, and **all of the growth is the I/O lists, not
the arrays**:
- the state's own reachable data grows by the output (the log, a `list Z` at 3 words per byte:
  7.0 MB written ≈ 21 M words) minus the input it consumes;
- "reachable only from elsewhere" grows by about 3 words per stdin byte consumed (2.95 M bytes
  consumed, +8.9 M words). That is the input list still referenced by states kept in frames
  (§2.2): an old state's `io_stdin` is a longer suffix of the same list. It is bounded by the
  size of the input and gone at exit.

Neither grows with the computation. They grow with the bytes read and written, at 24 bytes of
heap per byte of I/O: a 7 MB log costs about 170 MB. This is the one residual against E11's
"memory that does not grow with the work done", and it is stated here rather than rounded away.
Both could be removed in stage 2 or later, by streaming the output in the driver and keeping the input as an index
into a string. Neither is needed to pass E11. The top of the heap without probes (267 M words,
`mean_space_overhead` 6.2) is OCaml's GC pacing letting the heap run ahead of live data at this
allocation rate. A `space_overhead` setting or a periodic compaction in the driver (`PS_COMPACT`
exists) bounds it; stage 2 records the setting it uses.

## 3. Time profile

### 3.1 Where the CPU goes [M]

Top-of-stack samples (`sample`, 1 ms interval) grouped by cost class
(`h5/evidence/profile/*.selfprof.txt`):

| class | current build, format load (`base-p250`, 15 s at t ≈ 20 s) | current build, later (`base-p250`, 20 s at t ≈ 110 s) | T1 + in place, load (`t1lin-p1000`, 15 s at t ≈ 5 s) | T1 + T2 + in place, names (`t2lin-pall`, 15 s at t ≈ 40 s) |
|---|---|---|---|---|
| `Uint63`/`Sint63` ↔ `Z` conversions (extracted Coq library) | **40.3 %** | **27.1 %** | 1.3 % | 3.0 % (+ 2.1 % in the realizers, 5.0 % `caml_copy_int64`) |
| zarith (`Z` arithmetic, its C stubs) | 20.9 % | 17.7 % | **35.7 %** | 19.0 % |
| extracted `BinInt`/`BinPos` (Coq's `Z`/`positive` code) | 13.4 % | 8.6 % | 17.6 % | 5.7 % |
| allocation | 12.2 % | 12.0 % | 15.8 % | 15.1 % |
| the interpreter (`Interp`) | 3.3 % | 1.8 % | 11.1 % | **21.9 %** |
| storage and values (`Values`) | 1.9 % | 0.9 % | 3.4 % | 8.3 % |
| the arrays (`Parray` / `parrayc`) | 1.6 % | 1.3 % | 4.9 % | 10.7 % |
| minor GC (promotion) | 2.0 % | 4.3 % | 0.6 % | 0.7 % |
| major GC | 1.8 % | **22.8 %** | 1.3 % | 2.7 % |
| write barrier | 0.2 % | 0.3 % | 0.8 % | 1.7 % |
| C boundary (`Boundary`) | < 0.2 % | 1.0 % | < 0.5 % | < 0.5 % |
| system (`mmap`, TLS) | 2.0 % | 1.7 % | 2.7 % | 2.3 % |

How to read it:
- **The conversions.** `Sint63.to_Z` in the extracted code is a 63-step loop (`Uint0.to_Z_rec`,
  each step a closure, `Z.double` and a shift). `Uint63.of_Z` divides by 2 once per bit
  (`of_pos_rec`). Of the 7,351 samples inside the conversions (load phase, `callers.py`), 3,735
  (51 %) are under the interpreter's `evall` closure (`fS_3068`) and 709 (10 %) under `evale`'s
  (`fS_1559`). Both decode the IR's integer literals (`zi g`, `zi k`, `zi lo`, `zi esz`) at
  every evaluation. 179 (2 %) are under the heap's index conversions (`bget`, `bset`, `cell_at`,
  `put_cell`, `hput`), and 2,658 (36 %) could not be attributed, because OCaml frames have no
  frame pointers.
- **The zarith and `BinPos` share after T1** is mostly the `Z` functions `ExtrOcamlZBigInt` does
  not realize. `Z.land` (`BinPos.coq_land`, `f2p`, `f2p1`), `Z.testbit` and `Z.quotrem` match
  a `positive` by one `quomod p 2` per bit (`ml_z_div_rem`, `Z.ediv_rem`, `ml_z_sign`). They
  serve the word slices (`load_slice`, `store_slice`), the chunk index in `bget`/`bset`, C's
  `/` and `%` (`Z.quot`, `Z.rem`), and the decimal printing (`digits_rev`). T2 removes them.
- **The major GC's 22.8 % later in the current build** is the retained chains of §2 being
  marked, again and again.
- **After T1, T2 and in place, no single class dominates.** The interpreter's closures (one
  `fS` closure per IR node: the fuel realizer of §2.2), `Z` arithmetic, allocation (result
  pairs, `mkst`, `mkloc`, cells) and the arrays each take 10–22 %. That is the shape of a
  profile with no further profile-guided fix of the same size left.

### 3.2 CPU time, model against the pinned binary (the meaning dump as a proxy) [M]

The machine's load moved between 13 and 177 during this work, and CPU time under contention
moves with it (the same persistent 250-name run took 123.6 s at a load of 100–175 and 88–98 s at
15–27). So the comparison is made by **interleaved rounds**: each round runs every variant once,
one after the other, on the same input ([`h5/evidence/commands/abtest.sh`](h5/evidence/commands/abtest.sh);
three rounds at 250 names, two at 0 and at 1,000; load 13–47). Median CPU seconds
(`h5/evidence/abtest.tsv`, made by `h5/tools/abtable.py`):

| | 0 names | 250 names | 1,000 names | 23,519 names |
|---|---|---|---|---|
| pinned binary, native arm64 (min of 5, user + sys) | 0.342 | 0.259 | 0.452 | 3.089 |
| current representation (`prof`, persistent) | 62.6 | 90.7 | 189.7 | out of memory (≈ 76 GB needed) |
| A alone (`prof`, in place) | — | 83.3 | — | — |
| T1 (`t1`, persistent) | — | 29.1 | — | out of memory |
| A + T1 (`t1`, in place) | — | 19.7 | — | — |
| **A + T1 + T2** (`t2`, in place) | **8.5** | **8.9** | **20.6** | **345.0** (one run, at load 35–70) |

Per-round spread around the median: from −12 % to +27 %. The shortest runs vary most: `t2` at 250
names took 8.0, 8.9 and 11.2 s.

The binary's 0-name run is its own format load: about 0.3 s. Its 250-name minimum is lower than
that, which is noise. The ratios:

| | current | A + T1 + T2 |
|---|---|---|
| the format load (0 names) | 62.6 / 0.342 ≈ **183×** | 8.5 / 0.342 ≈ **25×** |
| the whole 1,000-name run | 189.7 / 0.452 ≈ **420×** | 20.6 / 0.452 ≈ **46×** |
| per name, the marginal cost (macro expansion and `\meaning`): model (p1000 − p0) / 1,000 against the binary's (3.089 − 0.342) / 23,519 = 0.117 ms | 127 ms ≈ **1,090×** | 12.1 ms ≈ **103×** |
| the whole dump | — | 345.0 / 3.089 ≈ 112× (a contended run; at the uncontended per-name rate, ≈ 8.5 + 23,519 × 12.1 ms ≈ 293 s ≈ 95×) [I] |

So T1, T2 and A together are **10.2×** faster at 250 names and **10.5×** per name than today.

These ratios are approximate in both directions. The model ran on the macOS host and the binary in
colima's Linux VM on the same hardware, both under the same varying load. Neither is the
quiet-machine measurement E4 asks for.

### 3.3 What this says about H.5 [M on the proxy; I for H.5's documents]

H.5's documents (the one-line document, the 12-page synthetic paper, a 40-page corpus paper)
**cannot be run in the model yet**: a `pdflatex` pass ships PDF through externals that are
Stuck (43 of 188 are modelled). The meaning dump is macro expansion and printing: the same
interpreter, arrays and arithmetic as typesetting, but none of the paragraph builder's or the
font machinery's mix. On that proxy:
- **The current representation: 183× on the format load, ≈ 1,090× per name**, and out of memory
  before 4,000 names. Well past the kill line.
- **A + T1 + T2: 25× on the format load, 46× on the 1,000-name run, ≈ 103× per name.** That is
  below the kill line (200×). It is under the pass line (60×) for the load and the short run, and
  about 1.7× over it on the marginal cost. A pass of a real document is load plus typesetting,
  so its ratio falls between the two; where it falls depends on the document [I].
- **The pass line (≤ 60× per pass) is not in sight from the heap representation.** What is left
  is spread over the interpreter, `Z` arithmetic, allocation and the arrays (3.1). Each further
  factor needs a change to the term (C or D), or to the value representation (machine integers
  for C's `int` in place of `Z`), and none of those fits the box.

## 4. Platform reproducibility: the extracted tree is identical [M, R]

H3-report.md §meanings says the extracted OCaml tree "hashes `72b2ea79…` there (a different value
from the macOS build's; not investigated, recorded)". Checked file by file:

| what | Linux x86_64 runner (run 37306038862, `h3/evidence/meanings/run2-37306038862/prefixes/provenance-ci.json`) | macOS arm64 (committed `h2/evidence/build/provenance.json`; local rebuild `~/.cache/lp-spike-h1/h3/cp2`) |
|---|---|---|
| translator inputs (10) | equal | equal |
| committed sources (17) | equal | equal |
| generated Coq tree (22 files) | `e9ae7712…` | `e9ae7712…` |
| extracted OCaml tree (93 files, per-file sha256 and `_tree`) | `72b2ea79…` | `72b2ea79…` |
| `ps.exe` | `f7d6631a…` | `e41941bf…` |
| tools | Coq 8.18.0, OCaml 5.2.0, zarith 1.14 (the workflow's pins) | Coq 8.18.0, OCaml 5.2.0, zarith 1.14 |

The workflow's own check (`spike-h3-meanings.yml`, the `bad = [k for k in ("inputs", "sources",
"generated", "extracted") if ci[k] != ref[k]]` step) printed `differs from the measured build in:
[]` in each of the four jobs whose output is committed (`provenance-check.txt`: run 1 `full`;
run 2 `full`, `full-compact`, `prefixes`). Each of those four jobs also built the same `ps.exe`,
`f7d6631a…`, so the compilation on Linux reproduces itself. The sentence in the H.3 report is
therefore a transcription error, and nothing was investigated because there was nothing to find
(C-143).

**Every byte of the trusted path, accounted for:** the source pin, the translator and the
committed Coq sources are hash-equal; Coq's output (the generated tree, then the extraction) is
byte-identical across the two hosts. Only `ps.exe` differs, and it must: it is native code for
two instruction sets and two object formats, produced by the same OCaml 5.2.0 compiler from the
same 93 files and linked with the same zarith 1.14 and coq-core 8.18.0 kernel library. That
compilation step is TB-1's "OCaml compiler and runtime". Its per-host output is checked only by
running it: the differential, the round trip and the meaning prefixes, per architecture as E2
requires. The provenance does **not** record the versions of GMP (under zarith) or of the C
toolchain that compiled the OCaml runtime and zarith's stubs; stage 2 adds them to
`provenance.json` (`opam list`, `gmp` version), because both are on the trusted path of
`ps.exe`.

## 5. Candidate representations

What each candidate must deliver (E11): memory that does not grow with the work done, and speed.
The profile fixes what "grounded" means here. The growth is old versions kept reachable (§2). The
time goes to integer conversions, then to zarith calls, allocation, the interpreter and the arrays,
in roughly equal shares (§3). The order of the options for (b) is the task's: a refinement proved in
Coq; the same Coq term with different extraction realizers, added to the trusted base with a
justification; tested only, which is not acceptable as the end state.

### Candidate A: an in-place `PArray` realizer that fails closed on a superseded version

**(a) What changes.** Only the extraction realizers. `Extract.v`'s seven `PArray` directives
point to a new OCaml module, `Linparray`, of about 60 lines, in place of coq-core's `Parray`. A
set writes into the array, returns a fresh handle and marks the old handle `Invalid`. Every
operation on an `Invalid` handle raises `Linparray.Superseded`. The driver catches it as it
catches `Stack_overflow`: `RESULT: model resource limit: superseded array version (no
verdict)`, exit 3. No Coq term changes: `Values.v`, `Interp.v`, `Boundary.v` and the generated
program stay byte-identical, and so does the extracted tree except `PArray0.ml`.

**(b) How equivalence is established.** The Coq term is the same, so every statement about `PS`
holds unchanged. What changes is a realizer, so TB-1 gains one row. It is justified in three
layers, the first of them proved:
1. **A Coq proof about a model of the realizer** (new file `LinArray.v`, about 150 lines). The
   functional side is Coq's own `PArray` primitive, with its axioms (`get_set_same`,
   `get_set_other`, `get_make`, `length_set`, `default_set`, `get_copy`, ...). The store side is
   an explicit model of `Linparray`: a store maps array ids to (current stamp, contents, default,
   length), and a handle is (id, stamp). Over any *trace* of operations, each op naming a handle
   returned earlier, the theorem: **if the store run does not abort, every value it returns
   equals the value the `PArray` run returns.** Proof: the invariant "the valid handle of each
   id denotes, in the store, exactly the contents its `PArray` version has" is preserved by
   every op, and an op on an invalid handle aborts.
2. **The OCaml module implements that model**, checked line by line against `LinArray.v`. This is
   the same kind of trust TB-1 already gives coq-core's `Parray`, which nothing proves either.
   The module is about 60 lines with one branch per operation, against `Parray`'s 200 lines with
   rerooting.
3. **The link from the trace theorem to the extracted program is OCaml's type abstraction.**
   `'a Linparray.t` is abstract, so the extracted program can touch arrays only through the seven
   operations, and every execution of it induces such a trace. This is stated in the TB row. It
   is not proved in Coq, because it is a statement about OCaml.

So **soundness does not rest on the program being linear.** A non-linear access stops the run
with no verdict, which is outside the tier, like Stack_overflow. Linearity matters only for
completeness, meaning how many runs finish. Measured: 0 superseded reads in every run (§2.4).
Some places return a state older than the newest: for example the error branches of
`undump_result` and of `ERealloc`, after a partial write. They return it inside a Stuck result,
and the driver reads only `st_io`'s lists from such a result, never an array. So a Stuck verdict
stays Stuck, with the same output. Stage 2 lists every such site; the differential's Stuck rows
check it.

**(c) Memory and speed.** Memory: live data only, measured flat at 74.2–74.8 M words from the end
of the load to 1,000 names (§2.4). The top of the heap stays under about 2× live under OCaml's
default pacing (113–137 M words, 1.0–1.9 GB footprint). The only part that grows is the output,
held as `io_out` lists at 3 words per byte (≈ 21 M words for the full dump's 7 MB log). Speed:
alone, −8 % CPU at 250 names (median 90.7 → 83.3 s, §3.2), from 4.5× fewer promoted words (427 M →
94 M). That is a fraction, not a factor: the arrays were never the time.

**(d) Risk to fidelity, and re-verification.** The Coq term carries no risk. A bug in
`Linparray` (an index, the default, `copy`'s independence) would make outputs differ, or would
abort. Re-verification, all on the stage-2 model build:
- H.2's 178-input differential on both architectures (each row's class unchanged, and no row
  turning to LIMIT);
- the INITEX evidence;
- H.3's round trip: 11.6 MB of format through `loadfmtfile`/`storefmtfile`, which is the
  heaviest array traffic of any input;
- the committed meaning prefix (`local-prefix50`);
- prefixes of 250 and 1,000 names against the binary;
- the full 23,519-name dump against `4879fa65…`.
`LinArray.v` is compiled in `pipeline.sh` with `Print Assumptions` closed except for the `PArray`
axioms.

**(e) Effort.** About 1.5 days: the module and the driver message (0.25 day), `LinArray.v` (0.5–1
day), the rebuild, re-verification and CI runs (0.5 day). It fits the box.

### Companion to every candidate: O(1) realizers for the conversions (T1, T2)

Not a heap representation. It is in this design because the profile puts **≈ 75 % of the time**
there (§3), and E11 is decided on speed as well as memory.

**(a) What changes.** `Extract Constant` for `Uint63.to_Z`, `Uint63.of_Z`, `Sint63.to_Z` (T1), and
for `Z.land`, `Z.lor`, `Z.lxor`, `Z.testbit`, `Z.quotrem` and `Z.of_nat` (T2), each as a one-line
zarith expression (`h5/tools/zr.ml` is the measured version). The Coq term does not change.
`ExtrOcamlZBigInt` already realizes `Z.add`, `Z.mul`, `Z.div`, `Z.modulo`, `Z.shiftl`,
`Z.shiftr`, `Z.compare` and the rest of the arithmetic this way; T1 and T2 fill its gaps.

**(b) Equivalence.** These are realizers of defined Coq functions, so TB-1 gains one row. Each
realizer's obligation is a Coq theorem that already exists:
- `Uint63.of_Z_spec` (`φ (of_Z z) = z mod wB`) and `Uint63.to_Z_bounded` (the value lies in
  [0, 2^63));
- `Sint63.to_Z`'s two cases, which follow from its definition and `Sint63.to_Z_bounded`;
- `Z.testbit` with `Z.bits_inj` for `land`/`lor`/`lxor` (zarith's `logand` and the others are
  infinite two's complement, as Coq's are);
- `Z.quotrem_eq` and `Z.quot_rem'` with Coq's `quotrem a 0 = (0, a)` (zarith raises on 0; the
  realizer handles 0 first);
- for `of_nat`, `Nat2Z.inj_succ` together with `Z.of_nat 0 = 0`, read on `ExtrOcamlNatInt`'s
  `int` representation of `nat`.

Measured as supplementary evidence, never as the argument:
- `h5/tools/t1test.ml`: 3,032,088 comparisons of T1 against the extracted Coq definitions on
  every ±64 neighbour of ±2^k (k ≤ 70) and 10^6 random values, 0 mismatches;
- whole runs with `PS_T1CHECK=1`, which compare every call of a 250-name dump (T1 alone, then T1
  and T2): 0 mismatches, IDENTICAL output.

An alternative that adds no realizer for the largest single cost: the translator emits the IR's
integer literals as `Z` instead of `int`, so `zi` disappears. H.2 chose `int` to keep the
extracted program small, so that alternative would need H.2's size and time measurement again
(its kill criterion: > 2 h or > 16 GB to build).

**(c) Speed (median CPU s, §3.2).** At 250 names: 90.7 (current) → 29.1 (T1) → 19.7 (T1 and A)
→ 8.9 (T1, T2 and A). At 1,000 names: 189.7 → 20.6 s (T1, T2 and A). Memory is unchanged by T1 and T2:
they speed up the run but do not remove the growth (`t1-p250`: top of the heap 466 M words,
3.7 GB).

**(d) Risk.** A wrong realizer changes arithmetic everywhere. That risk is why the check mode and
the whole-run comparison exist, and the same re-verification as A covers it. One more
precaution: `caml_copy_int64` (5 % of the samples after T2) shows the measured realizers box an
`Int64`. The stage-2 version uses `Uint63.to_int2`/`of_int` on the 63-bit representation and is
re-checked the same way.

**(e) Effort.** 0.5 day, the test included. It fits the box.

### Candidate B: keep coq-core's persistent arrays, and make old versions unreachable

**(a) What changes.** The Coq term, so that no extracted closure holds a state across a call:
**B2**, a mechanical restructuring of every fuelled `Fixpoint` in `Interp.v` and `Boundary.v`
(and of every `Fixpoint` that threads a `state`). Its successor branch becomes a call to a
separate body function, `match fuel with O => .. | S f => evale_body f e st end`. Then the
`fS` closure only tail-calls, and `ocamlopt`'s precise liveness frees `st` after its last use.
Coq's guard checker must accept the body function. Either it is passed the recursive calls as
arguments and unfolded, or the body stays in the mutual block with a decreasing fuel argument
of its own; which of the two Coq 8.18 accepts is untested. Variant **B1** changes the compiler
instead of the term: `ocamlfind ocamlopt -O3` with flambda inlines the immediately-applied
`(fun fO fS n -> …)`. No opam switch here has flambda with coq-core and zarith; one would be
built.

**(b) Equivalence.** B2: for each restructured function, a Coq lemma `evale_new = evale` (by
`reflexivity` or one `destruct fuel`). This is the best class: proved in Coq, and no realizer is
added. B1: no term change; TB-1's compiler row grows by flambda. But **the memory property itself
is "tested only" under both B1 and B2.** That old versions are unreachable is a fact about
compiled code and the GC, which no Coq statement reaches. It can only be measured, with the
"reachable only from elsewhere" probe of §2.1. One new closure capturing a state anywhere,
in an external, a helper or a future boundary model, brings the growth back silently, and only
the probe would show it.

**(c) Memory and speed.** Memory [I]: live data plus the garbage of `Updated` nodes, which every
write still promotes through the old version's write barrier (427 M promoted words at 250 names,
against 94 M in place). The probe would read near zero; the top of the heap would be between A's
137 M words and the current 472 M, depending on the GC's pacing. Speed [I]: no better than A
(the same allocation, plus the diff nodes, plus a closure per node exactly as now). B2 adds a
function call per node, which is neutral to slightly negative.

**(d) Risk.** None to fidelity (B2 is proved). The risk is to the property E11 funds: the
growth can come back with no test failing, because no fidelity test measures memory.

**(e) Effort.** B2: 1.5–2.5 days, depending on the guard checker, over about 15 functions, with
the same re-verification as A. B1: about 1 day (an opam switch with flambda, coq-core and
zarith), plus TB-1 review of the flambda pipeline. It fits the box, but it buys a weaker memory
guarantee and no speed.

### Candidate C: a state monad over an abstract heap interface, realised by mutable arrays

**(a) What changes.** A new Coq implementation of `PS`. `Interp.v` and `Boundary.v` are written
against a `HEAP` module type (`read`, `write`, `alloc`, `free`, `io` access, with their laws) in
a state monad whose state they never name, so they never hold it. It is instantiated in Coq with
today's `PArray`-backed `state`. Extraction realizes the monad by a global mutable store and
`HEAP` by OCaml arrays.

**(b) Equivalence.** A refinement theorem in Coq: the monadic `run`, instantiated with the
functional heap, equals today's `run` on every input. It is proved by induction on fuel, case by
case, over 1,800 lines of definitions: mechanical, but large. The mutable realizer of the monad
stays in TB-1. Its justification is linearity *by construction*: the state is abstract, and
only `bind`, `get` and `put` reach it. That is a parametricity argument, stronger than A's
run-time check, but still not a Coq theorem about OCaml.

**(c) Memory and speed [I].** Memory: live data only. Speed: on top of A, it removes the `state`
record rebuilt at every write (6 words), the `EOk (v, st)`-style result pairs, and the 3-level
`heap → block → chunk` indirection of every access. From the allocation share of §3 (15 %) and
the arrays' share (11 %), about 1.3–1.6× over A with T1 and T2.

**(d) Risk.** The refinement proof makes the rewrite safe, but the rewrite touches every line of
TB-4 and TB-5. Until the proof is closed, the differential is the only check.

**(e) Effort.** 6–10 days: the rewrite, the proof, re-verification. It **does not fit** the box
(stage 2 has 4 days). It is a candidate after H.5, if A's run-time check is to be replaced by
linearity by construction.

### Candidate D: compile the IR to a shallow embedding, with a proved equivalence

**(a) What changes.** The translator emits, for each of the program's procedures, a Coq function
that does what `exec fuel (p_body p)` does, with literals as `Z` constants and the IR's
dispatch resolved at translation time. It also emits a reflection lemma per procedure.

**(b) Equivalence.** A per-procedure lemma `exec fuel (p_body p) st = shallow_p fuel st`, proved
by computation (`cbn`/`reflexivity` after unfolding the interpreter on the known syntax), so
the refinement is proved in Coq. This is ADR-014 draft H.2's own fallback ("emit a shallow
embedding with a generated reflection lemma").

**(c) Memory and speed.** Memory: whatever heap representation it uses, so it needs A or C as
well: D does not address the growth. Speed: the profile says the interpreter proper is 2–3 % of
the samples now and 22 % after T1, T2 and A (§3). D removes most of that, the `fS` closures and
the result wrappers, so at most about 1.3× on top of A with T1 and T2 [I]. Most of the remaining
cost would still be there: `Z` arithmetic, allocation of cells and values, and the arrays.

**(d) Risk.** High. The Coq term grows by the whole program again, and proof by computation over
it risks H.2's kill criterion (> 2 h or > 16 GB to compile). The emitted functions are a second
translator output to keep in sync.

**(e) Effort.** Weeks. It **does not fit** the box. It is the shape of ADR-014's H.5 fallback ("a
verified-refinement fast interpreter becomes its own project"), and the profile says it is not
where the time is.

### The candidates side by side

| | memory stops growing | how it is proved | trusted base added | speed over today (250 names, CPU) | fits the box |
|---|---|---|---|---|---|
| **A** in place, fail-closed | **yes**, by construction: a superseded version holds nothing, and a read of one stops the run | the term is unchanged; `LinArray.v` proves the realizer's model refines `PArray`; the OCaml module is checked against the model | one realizer row (≈ 60 lines), with a Coq-proved model | 1.09× alone; **10.2× with T1 + T2** (measured, profiling variant) | yes (≈ 1.5 days) |
| **B** persistent, retention removed | measured only, and fragile: any closure that captures a state brings it back | B2: Coq lemmas, by `reflexivity`; B1: none (a compiler change) | none (B2) or flambda (B1) | ≈ 1× alone [I]; T1 + T2 apply equally | yes, with no speed gain |
| **C** state monad, mutable realizer | yes, by construction | a refinement theorem in Coq over the whole of `PS` | the monad's realizer (parametricity) | ≈ 1.3–1.6× over A + T1 + T2 [I] | **no** (6–10 days) |
| **D** shallow embedding | no (needs A or C) | generated reflection lemmas | none beyond A or C | ≈ 1.3× over A + T1 + T2 [I] | **no** (weeks) |

## 6. Recommendation and the stage-2 plan

**Fund candidate A, with T1 and T2 in the same `Extract.v` change.**

1. It is the only candidate that removes the growth **by construction** within the box. B removes
   it only as a measured property, and one new closure brings it back silently. C removes it by
   construction too, but does not fit.
2. It keeps the Coq term byte-identical, so no theorem about `PS` and no translated line is
   touched. The trust it adds is one realizer whose model is **proved** in Coq to refine
   `PArray`, and its failure mode is a "no verdict", not a wrong verdict.
3. With T1 and T2, it is the change that moves speed by a **factor** (10.2× at 250 names, 10.5× per name; the
   whole dump in 345 s and 2.0 GB, IDENTICAL to the binary, on a profiling variant). T1 and T2 are where
   the profile puts the time. They are realizers of the same kind `ExtrOcamlZBigInt` already
   uses, and each one's obligation is an existing Coq theorem.

**Stage 2, 2026-10-07 → 2026-10-10:**

| day | work | done when |
|---|---|---|
| 10-07 | `Linparray` (OCaml) and `Superseded` in the driver; `Extract.v`: the `PArray` directives, then T1 and T2 as `Extract Constant` with no `Int64` boxing; `pipeline.sh` rebuild; `provenance.json` with zarith, GMP and the C toolchain recorded | the build passes; `t1test` extended to T2 passes; the 50-name prefix is IDENTICAL to the committed one |
| 10-08 | `LinArray.v` (the store model, the trace semantics on `PArray`, the simulation theorem), compiled by `pipeline.sh`, `Print Assumptions` limited to the `PArray` axioms; H.2 re-verification: INITEX evidence, the 178-input differential (arm64 locally) | the theorem closed; no differential row changes class |
| 10-09 | H.3 re-verification: the round trip; E8's workflow re-run on a 16 GB runner, all 23,519 names (expected ≈ 2 GB from §2.5), with the native amd64 differential | the round trip = binary; the meanings clause compared against `4879fa65…` on the model build |
| 10-10 | H.5 speed on what can run (§3.3, the question below), on a quiet machine or a CI runner, per E4; the report | the E11 verdict, written up either way |

**The kill accounting, as E11 states it.** Memory that does not grow with the work done: A gives
it (the live words are flat; only the I/O lists grow, at 24 bytes of heap per byte read or
written, §2.5). Speed at or below 200×
pdfTeX "on H.5's documents": on the proxy, A + T1 + T2 is 25× on the format load, 46× on the
1,000-name run and ≈ 103× per name, so no kill on the proxy. **But H.5's documents cannot run in the
model before the PDF-side externals are modelled** (H.4's work). So E11's speed condition cannot
be decided on them by 2026-10-10. The owner must say what counts (question 1 below). The pass
line (≤ 60× per pass) is met by the load and the short run but not by the marginal cost (≈ 103×),
and no change that fits the box is in sight to close that 1.7×.

**Questions for the owner:**
1. **What does the 2026-10-10 verdict measure, given that H.5's documents cannot run?** (a) The
   meaning-dump proxy above. (b) H.5's three documents in DVI mode (`\pdfoutput=0`), if
   the font-file externals they need can be modelled in the box: typesetting without the PDF
   back end. (c) Defer the speed verdict to after H.4 and judge memory alone on 10-10.
   Recommendation: (b) if the TFM path runs by 10-09, otherwise (a). The report states which
   one was used.
2. **Does the trusted base accept realizers checked by a Coq-proved model plus review** (A's
   `Linparray`, as coq-core's `Parray` is today), and realizers whose obligations are existing
   Coq theorems (T1, T2)? If not, A's alternative is C, and T1's is to emit the IR's literals as
   `Z` (H.2's size measurement again); neither fits the box.

## 7. What this stage commits

- This document.
- [`h5/README.md`](h5/README.md), with the binary-side recipes. They start the engine outside
  `_oracle.py`, so as in H.1–H.3 they are documentation, not scripts.
- [`h5/tools/`](h5/tools/): `mkvariant.py` (the profiling variants, every replacement asserted),
  `parrayc.ml`, `prof.ml`, `zr.ml`, `build.sh`, `run.sh`, `cmp.sh`,
  `selfprof.py`, `callers.py`, `summarize.py`, `abtable.py`, `t1test.ml`. They run against the H.3
  checkpoint-2 extracted tree, with heavy data in `~/.cache/lp-spike-h1/h5/`.
- [`h5/evidence/`](h5/evidence/):
  - `runs.tsv`: every run's verdict, CPU, GC counters, array counters and comparison class;
  - `probes/`: every run's `PROBE` lines, verdict and footprint trace;
  - `compare/`: the `meancompare` JSON of each compared run;
  - `profile/`: the `sample` call trees, gzipped, their grouped summaries, and the `-dcmm`/`-dlambda`
    excerpts of §2.2;
  - `abtest.tsv`: the interleaved timing rounds of §3.2;
  - `t1test.txt`: the realizer test's result;
  - `commands/`: the exact command lines of every run, and the queue logs;
  - `binary-times.txt`: the pinned binary's CPU times;
  - `exe-sha256.txt`: the variants' hashes, with their provenance notes.
- `h3/tools/capped.sh`: caps and kills the whole process tree (C-144).
- `PROJECT_STATE.md`: C-142, C-143, C-144, and OPEN-123's state line. `H3-report.md`: the two
  sentences that C-142 and C-143 correct are marked in place.

Not committed: any change to the model. `h2/` is untouched, and the profiling variants are built
from the extracted tree under `~/.cache/`.
