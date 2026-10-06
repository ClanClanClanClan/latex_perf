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
5. **Speed against H.5: past the kill line on the proxy's marginal cost** [M on a proxy, I for
   H.5]. *(Restated 2026-10-06, C-145: the first version timed the binary with its log written
   to the macOS host through virtiofs, and mixed medians with minimums and name populations; it
   said 25× on the load and ≈ 103× per name.)* H.5's documents cannot run yet (the PDF path's
   externals are Stuck), so the meaning dump is the proxy. With A, T1 and T2, on interleaved
   medians with the binary on container-local storage (§3.2): **59× on the format load, 122× on
   the 1,000-name run, 818× on the whole dump, and ≈ 1,540× per name** (≈ 1,260× min against
   min). The pass line is ≤ 60× and the kill line > 200×. **No profile-guided fix to ≤ 200× is
   in sight** (§3.4): every further change measured or estimated (native int63 values, a mutable
   store, a shallow embedding, an I/O buffer, GC tuning) together gives ≈ 4× (≈ 10× at best),
   leaving ≈ 370× (≈ 150× at best), and only as a new verified execution model, which is H.5's
   fallback project.
6. **Platform:** the extracted OCaml tree is the same on the Linux runner and on macOS: all 93
   files, `72b2ea79…` on both [M]. The H.3 report says otherwise; that sentence is a
   transcription error (C-143). The only build output that differs is `ps.exe`, the native code
   of two hosts.
7. **Recommendation, for memory:** candidate A, an in-place `PArray` realizer that fails closed
   on a superseded version. It keeps the Coq term unchanged and adds to the trusted base a
   realizer whose model is proved in Coq. T1 and T2 ship with it, in the same `Extract.v`
   change. **Measured since (§5 B): B2**, the term restructuring that frees the fuel closures,
   also removes the growth with coq-core's arrays unchanged (full dump in 2.4 GB, IDENTICAL), and
   adds no realizer; but its memory property is tested only, and it is ≈ 1.4× slower than A.
   **B1** (flambda `-O3`) does not remove it. **For speed, neither changes the verdict**: on
   the proxy H.5's kill criterion fires on the marginal cost (§3.3, §3.4). Three owner questions
   remain (§6).
8. **Stage 2 (2026-10-06, §8): B2 is the model build, and H.3's meanings clause is MET on it**
   [M]. While question 2 is open, B2 was built alone, with no new realizer.
   - The interpreter's ten fuelled members were restructured at the source. Each is proved equal
     to its pre-B2 term by `reflexivity`, and so is `Main.run`. Nothing was added to the trusted
     base.
   - A standing retention check fails on the pre-B2 build (105 M words retained at the format
     load's first probe) and passes on B2 (−0.28 M). After review it covers every branch closure
     of the extraction (669, typed) and every `fun` passed as an argument (44), and probes at
     points fixed by the program, not by CPU time.
     Its dynamic half catches only 5 of 10 single-member reverts, so the static half is required
     (§8.2, C-150).
   - The INITEX evidence, the 178-input differential and the round trip are unchanged
     (`55629ae0…`).
   - The full 23,519-name dump finishes in 2,673 s of CPU and 2.5 GB, IDENTICAL to the binary,
     with digest `4879fa65…`.
   - On the runner's non-flambda OCaml, memory is flat too: 2.0 GB at 4,000 names, where the
     pre-B2 build was killed at ≈ 14.5 GB.

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
`ocamlopt` (here with flambda at its default level, as every local build was; without flambda on
the GitHub runner: C-146) keeps `fS` as a heap closure that captures every free variable of
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

**This section was restated on 2026-10-06 (C-145).** Its first version (commit `b9ea746c`) timed
the binary with its 7 MB `texput.log` written to a bind mount on the macOS host (virtiofs), which
inflated the binary's time 4–8× on the full dump. It also divided a model *median* by a binary
*minimum*, and compared the model's cost per name over the first 1,000 names with the binary's
average over all 23,519. All three made the model look better than it is. The numbers below
replace it.

**Method** ([`h5/tools/fairtime.sh`](h5/tools/fairtime.sh), [`h5/tools/bintime.sh`](h5/tools/bintime.sh),
table by [`h5/tools/fairtable.py`](h5/tools/fairtable.py); evidence in
[`h5/evidence/fair/`](h5/evidence/fair/)):
- **The binary** runs in a container on colima's native arm64 VM, and every file it writes goes
  to the container's own storage (`/tmp`, overlayfs on the VM's disk). Its input is copied there
  first. The clock shim fakes the wall clock, so user + sys CPU is read. Every run's `texput.log`
  is hashed: at all 23,519 names it is `335b024c…`, the same as the comparison run's. The script
  starts the engine outside `_oracle.py` on purpose; its header says why (E7's measurement entry
  point is being built on another branch).
- **The model** runs on the macOS host under `capped.sh` (4 GB cap). Its time is its own CPU time
  (`Sys.time`: user + sys) at the end of the run.
- **Interleaved rounds**: in each of 3 rounds, for each prefix in turn (0, 250, 1,000, all 23,519
  names), the binary 3 times, then each model variant once. Every round records the host's
  `uptime` and `memory_pressure` free percentage before each run, and the VM's load with each
  binary run.
- **Medians on both sides**, over the **same name populations**: the binary's 9 runs per
  prefix, each variant's 3 runs. The cost per name is (median at N names − median at 0) / N on
  each side, with the same N.
- Host load during the rounds: 8.6–38 (1-minute average; 8 cores), memory free 38–47 %. VM load
  during the binary's runs: 0.00–0.59 (1-minute average).

The variants (profiling builds, never model builds; §1, §5 B):
- **A** = `t2` in place (`PS_PARRAY=linear`): candidate A with T1 and T2, as in stage 1;
- **B2** = `b2sim`, persistent: coq-core's `Parray` algorithm unchanged, T1 and T2, and the fuel
  realizer beta-reduced (§5 B);
- **A + B2** = `b2sim` in place.

Median CPU seconds (the model's per-round values are in `h5/evidence/fair/fairtable.txt`):

| | 0 names (the format load) | 250 names | 1,000 names | 23,519 names |
|---|---|---|---|---|
| **pinned binary**, user + sys, median of 9 (min–max) | **0.112** (0.074–0.172) | **0.099** (0.075–0.123) | **0.091** (0.079–0.124) | **0.229** (0.211–0.365) |
| A (`t2`, in place) | 6.63 | 7.11 | 11.06 | 187.2 |
| A + B2 (`b2sim`, in place) | 5.26 | 6.18 | 15.32 | 190.4 |
| B2 (`b2sim`, persistent) | 8.93 | 9.36 | 19.34 | 267.7 |

The ratios, median against median:

| | A | A + B2 | B2 |
|---|---|---|---|
| the format load (0 names) | **59×** | 47× | 80× |
| the whole 250-name run | 72× | 62× | 95× |
| the whole 1,000-name run | **122×** | 168× | 213× |
| the whole dump (23,519 names) | **818×** | 831× | 1,169× |
| **per name**, over all 23,519 names: model (pall − p0) / 23,519 against the binary's (0.229 − 0.112) / 23,519 = **4.97 µs** | **7.68 ms ≈ 1,540×** | 7.87 ms ≈ 1,580× | 11.0 ms ≈ 2,210× |
| per name over the first 1,000 names | model 4.43 ms (A); **the binary's cannot be measured**: its p1000 − p0 difference (−21 ms) is inside its own run-to-run spread (0.07–0.17 s), because 1,000 names cost it about 5 ms | | |

How to read it:
- **The binary is fast enough that only the full dump resolves its per-name cost.** At 0, 250
  and 1,000 names it runs in 0.09–0.11 s, its start-up and format load, and the names are
  below its noise. So the per-name ratio is taken over all 23,519 names on both sides, never
  over a model prefix against a binary average.
- **The model's cost per name grows during the run**: 4.4 ms over the first 1,000 names, 7.7 ms
  over all of them. The work per name does not grow: 43 K array writes per name over the first
  1,000 names, 40 K over all of them (the `set` counter of the final `PROBE` lines of `fr1-A-*`),
  and 324 against 298 bytes of log per name. The model's *speed* drops: about 100 ns of CPU per
  array write over the first 1,000 names, about 180 ns over the whole dump. §3.4 measures why.
  Taking the first 1,000 names as the per-name rate understated the model's cost by 1.7×.
- **The machine's load moves both sides**, so only interleaved ratios are used. In stage 1, at a
  host load of 35–70, the same `t2` variant took 345 s on the full dump; here, at 9–17, 176–189 s
  (1.9× less). The binary took 0.645 s in the review's 7 rounds on container-local storage
  (median) against 0.229 s here (2.8× less). Pairing measurements taken at different times
  moves the ratio by more than either side's own spread.
- **Min against min**, as a bound on the noise: binary 0.074 / 0.211 s, A 4.92 / 176.6 s: per
  name 5.8 µs against 7.30 ms, ≈ 1,260×. So the per-name ratio is **≈ 1,260–1,540×** for A.
- **A + B2 is not faster than A**: per round and prefix, A + B2 / A is 0.79–1.39 (median 0.97,
  12 pairs). B2 halves the words allocated per array write (99 → 53, `PROBE` lines), and that
  buys about 3 %, within the noise. B2 alone, with the persistent arrays, is 1.28–1.75× slower
  than A (median 1.41, 12 pairs).

Against the first version of this table: the format load is **59×**, not 25×; the 1,000-name run
**122×**, not 46×; the cost per name **≈ 1,540×**, not ≈ 103×; the whole dump **818×**, not 112×.
The review's corrected figures (per name ≈ 675–945×, whole dump ≈ 430–535×, 1,000 names ≈ 80×,
load ≈ 35×) paired its own binary runs with stage 1's model medians, taken at other times and
loads; interleaved, on medians, the gap is larger still.

### 3.3 What this says about H.5 [M on the proxy; I for H.5's documents]

H.5's documents (the one-line document, the 12-page synthetic paper, a 40-page corpus paper)
**cannot be run in the model yet**: a `pdflatex` pass ships PDF through externals that are
Stuck (43 of 188 are modelled). The meaning dump is macro expansion and printing: the same
interpreter, arrays and arithmetic as typesetting, but none of the paragraph builder's or the
font machinery's mix. On that proxy, with A, T1 and T2 (A + B2 is within noise of it, §3.2;
the other variants are slower):
- **The format load is 59×**: at the pass line (≤ 60×), below the kill line.
- **The marginal cost, ≈ 1,540× per name** (≈ 1,260× min against min), is **7.7× over the kill
  line (200×) and 26× over the pass line (60×).** The whole dump is 818×.
- **A pass of a real document is the format load plus its typesetting** [I]. The one-line
  document is nearly all format load, so the proxy puts it near 60×. A 12- or 40-page paper
  spends most of the binary's time in typesetting, so if typesetting costs the model what macro
  expansion does per unit of the binary's work, its ratio is near the marginal one: of the order
  of 1,000×, past the kill line.
- So **on the proxy, H.5's kill criterion fires on the marginal cost**, unless a profile-guided
  fix is in sight. §3.4 asks whether one is.

What the proxy can and cannot stand for:
- It **can** stand for the cost of the machinery every pass uses: the interpreter, the `Z`
  arithmetic, the array representation, the allocation and the GC; and the format load itself,
  which every pass begins with.
- It **cannot** give the ratio of a document pass. The proxy's work per unit of the binary's
  time may differ from typesetting's in either direction: typesetting does more arithmetic per
  byte of output (glue, badness, `x_over_n`, `xn_over_d`), which is `Z` in the model and cheap
  machine arithmetic in the binary, and it does far less printing. Its I/O is DVI/PDF bytes
  rather than the log. It also reaches the paragraph builder's and the font loader's code, which
  the dump never runs. A per-name ratio of ≈ 1,540× is therefore an estimate of a document's
  ratio, not a measurement of it [I].
- It **cannot** say anything about the externals a PDF pass needs (H.4), which are Stuck today.

### 3.4 Speed headroom: where the remaining ≈ 1,540× goes, and what could remove it [M, I]

The profile of the fastest sound variant, A + B2 (in place, T1 and T2, the fuel realizer
beta-reduced; A alone is within noise of it, §3.2): `sample` at 1 ms over the first 1,000 names
(12 s from the start: the format load and the names), and three 20 s windows of the full dump at
20, 80 and 140 s ([`h5/tools/profrun.sh`](h5/tools/profrun.sh); samples and summaries in
`h5/evidence/profile/prof-AB2-*`). Grouped by **what a change of design would remove**
([`h5/tools/costclass.py`](h5/tools/costclass.py)), top-of-stack shares:

| class | first 1,000 names (8,728 samples) | full dump, 3 windows (43,895 samples) |
|---|---|---|
| **`Z` values**: zarith's code, the C-call trampoline into it and its TLS lookup, its boxed custom blocks, the extracted `BinInt`/`Uint63`/`Sint63` code and the T1/T2 realizers | **50.9 %** | **53.7 %** |
| – of which conversions `Uint63`/`Sint63`/`Int64` ↔ `Z` | | 18.2 % |
| – of which boxing (custom blocks: `Z` values ≥ 2^62 and `Int64`) | | 7.9 % |
| – of which the C-call trampoline and TLS | | 7.9 % |
| – of which arithmetic and comparison proper | | 19.7 % |
| **storage**: the arrays (`Parrayc`) and the heap model over them (`Values`: `bget`, `bset`, `load_cell`, `cell_at`, `hput`) | 20.2 % | 19.5 % |
| **interpreter** (`Interp`: dispatch on the IR, `has_label`/`goto_in` label search, argument lists) | 11.0 % | 16.7 % |
| **GC and allocation** (allocator slow path, minor and major GC, write barrier) | 16.5 % | 9.1 % |
| **I/O** (`Boundary`, where the I/O lists are read and extended) | 0.8 % | < 0.1 % |
| other | 0.7 % | 1.1 % |

The shares are the same in the three windows of the dump (Z 53.6–53.8 %, GC 8.8–9.3 %), so the
model's slow-down over the run (§3.2: ≈ 100 → ≈ 180 ns per array write) is not a class that
grows. GC tuning does not move it either: A + B2 at 1,000 names, 3 interleaved rounds each,
median CPU 15.8 s with OCaml's defaults, 15.9 s with a 4 M-word minor heap (`s=4M`: 949 minor
collections instead of 15,092), 16.5 s with `s=4M,o=200` (`h5/evidence/gc-sensitivity.txt`).
Inline allocation in OCaml code (the state records, result pairs and cells) is not visible as
its own frame: it is counted in the function that allocates, mostly `Interp` and `Values`.

**What each further change could gain, with its trusted-base cost.** Each estimate removes a
fraction of the class's share and applies Amdahl's law to the rest [I, from the shares above and
the micro-benchmark]:

| change | what it removes | evidence | speed-up alone | trusted base |
|---|---|---|---|---|
| **native int63 values** for C's `int` (and array indices), with overflow detection proved in Coq, in place of `Z` | all conversions, boxing and trampoline (34 % of samples), and arithmetic proper shrinks 1–5× ([`h5/tools/zbench.ml`](h5/tools/zbench.ml), this machine, 3 runs: `Z` add + `logand` 3.1–3.2 ns against 1.4–3.0 ns for the checked int version; compare + sub 4.4–4.7 against 0.85–0.99 ns; div/rem 4.7–5.6 against 1.7–2.0 ns; `h5/evidence/zbench.txt`) | the Z class is 54 %; after the change ≈ 8 % | **≈ 1.8×** (54 % → 8 %) | no new realizer: Coq's `PrimInt63` is already extracted to OCaml `int` by coq-core's `Uint63` (TB-1). But `Values.v`'s `KInt` changes type: a refinement proof that every operation on [−2^31, 2^31) agrees with the `Z` one (one lemma per C operator, plus the overflow cases), and the translator emits int63 literals. Days to weeks |
| **mutable store behind a proved interface** (candidate C) | the 3-level `heap → block → chunk` indirection, the state record rebuilt per write, version handling | storage 19.5 %; GC 9.1 % mostly follows allocation | ≈ 1.2–1.4× (removing ⅔ of storage and of GC) | C's refinement theorem; the monad's realizer by parametricity (§5 C). 6–10 days |
| **specialising the interpreter / shallow embedding** (candidate D) | IR dispatch, the linear label search of `goto`, argument lists, the per-node result wrappers | interp 16.7 % | ≈ 1.1–1.2× | per-procedure reflection lemmas; risks H.2's build kill criterion (§5 D). Weeks |
| **I/O as a mutable buffer** behind a proved interface | the 24 bytes of heap per byte of I/O (§2.5) | I/O < 0.1 % of time | none in time; memory only | one realizer row (a buffer with a list model) |
| GC tuning | — | measured above: no gain | none | none |

**All of them together** leave, of today's samples, about 8 % (Z) + 6.5 % (storage) + 5.6 %
(interpreter) + 3 % (GC) + 1.1 % (other) ≈ 24 %: **≈ 4.1×**, so ≈ 1,540× / 4.1 ≈ **370× per
name**. Under generous assumptions (Z to 4 %, every other class cut 10×) ≈ 9.6 % of today's
samples: ≈ 10× and ≈ **150×**. The
format load (59× today) would fall by a similar factor.

**The verdict on headroom:**
- **≤ 200× (the kill line): NOT in sight as a profile-guided fix.** The central estimate with
  every change above is ≈ 370× per name; only the generous one crosses 200×, and it needs all
  four changes at once: int63 values, a mutable store, a shallow embedding and a new I/O
  buffer. That is a new verified implementation of the engine's execution model, which is
  exactly H.5's fallback ("a verified-refinement fast interpreter becomes its own project"),
  weeks to months, not a fix within or near the box. No single change gets more than ≈ 1.8×.
- **≤ 60× (the pass line): NOT in sight.** It needs ≈ 26× on the marginal cost. No combination
  of the measured classes gives more than ≈ 10×, because every class would have to shrink by
  more than 25× at once. Only a different kind of artefact could: OCaml (or C) code generated
  from the IR with native integers and mutable memory, whose speed would be that of compiled
  code (an OCaml transliteration of C typically runs within a small factor of it [I]), with a
  verified compilation from the IR in place of the interpreter. That is a research project of
  its own, not a refinement of this one.
- The **format load** is the one place where the pass line holds today (59×). A one-line
  document is mostly format load, so it would pass on its own [I].

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
two instruction sets and two object formats, produced by OCaml 5.2.0 from the same 93 files and
linked with the same zarith 1.14 and coq-core 8.18.0 kernel library. **Not by the same compiler
configuration, though (C-146):** the macOS switch (`l0-testing`) is OCaml 5.2.0 with flambda, the
runner's is `ocaml-base-compiler` 5.2.0 with `ocaml-options-vanilla` (no flambda), so the two
builds also differ in the middle end. That compilation step is TB-1's "OCaml compiler and
runtime". Its per-host output is checked only by running it: the differential, the round trip
and the meaning prefixes, per architecture as E2 requires. The provenance does **not** record
the compiler's configuration (`ocamlopt -config`: `flambda`), the versions of GMP (under zarith)
or of the C toolchain that compiled the OCaml runtime and zarith's stubs; stage 2 adds them to
`provenance.json` (`ocamlopt -config`, `opam list`, `gmp` version), because all three are on the
trusted path of `ps.exe`.

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
flags instead of the term: flambda's `-O3`.

**Correction (C-146).** The first version of this section said that no opam switch here had
flambda with coq-core and zarith, and §2.2 said the retention came from "OCaml 5.2's `ocamlopt`,
without flambda". Both are wrong: the switch every local build used (`l0-testing`, the H.2
pipeline's default) is OCaml 5.2.0 **with** flambda (`ocamlopt -config`: `flambda: true`), at
its default optimisation level. The GitHub runner's switch is `ocaml-base-compiler` with
`ocaml-options-vanilla`, without flambda. The retention appears under both, so the finding of
§2.2 stands, but the two `ps.exe` builds differ by compiler configuration as well as by host
(§4), and `provenance.json` records only "5.2.0".

**(b) How B was measured** (profiling variants, never model builds):
- **B1**: the `t2` tree compiled with `-O3` (`OCFLAGS=-O3 h5/tools/build.sh`). Flambda then
  inlines 1 of the 14 fuel closures of `Interp` (`exec_list`'s); the other 13, including `exec`'s
  and `evale`'s, stay heap closures with the state captured: `-inline 10000` and
  `-inline-max-depth 10` change nothing (`-dcmm`: 13 `fS` functions, 26 allocation sites).
- **B2** (simulated): [`h5/tools/b2sim.py`](h5/tools/b2sim.py) beta-reduces, in the extracted
  OCaml, every application of `ExtrOcamlNatInt`'s realizer: `(fun fO fS n -> if n=0 then fO ()
  else fS (n-1)) (fun _ -> A) (fun f -> B) N` becomes `let n = N in if n = 0 then A else let f
  = n - 1 in B`. That is what B2's restructuring gives the compiled code: the successor branch
  is no longer a closure, and its variables get per-call-site liveness. 33 sites in 9 files,
  every one counted and asserted; `-dcmm` of `Interp` then has 0 `fS` closures. The arrays are
  `parrayc` in its persistent mode, which is coq-core 8.18.0's `Parray` algorithm unchanged
  (plus counters). T1 and T2 are included, as the task fixed.

**(c) Memory and speed, measured** (fair rounds of §3.2, 3 rounds; the deep probe run
`dB2o40-pall`):

| | 0 names | 250 names | 1,000 names | 23,519 names |
|---|---|---|---|---|
| current representation (stage 1, `prof`, persistent): top of the heap, peak footprint | — | 472 M words, 3,768 MB | 773 M words, 6,070 MB | out of memory (≈ 76 GB) |
| **B1** (`-O3`, persistent): top of the heap, peak footprint | — | 464 M words, 3,620 MB | **killed at the 4 GB cap** after 16 s | not run |
| **B2** (persistent): top of the heap, peak footprint | 176 M words, 1,510 MB | 200 M, 1,695 MB | 233 M, 1,860 MB | **307 M, 2,402 MB** |
| **A** (in place): top of the heap, peak footprint | 115 M, 991 MB | 118 M, 1,079 MB | 127 M, 1,088 MB | 267 M, 1,981 MB |
| A + B2 (in place) | 115 M, 990 MB | 116 M, 1,073 MB | 121 M, 1,105 MB | 236 M, 1,633 MB |
| B2, median CPU s (ratio to the binary) | 8.93 (80×) | 9.36 (95×) | 19.34 (213×) | 267.7 (1,169×) |
| A, median CPU s (ratio to the binary) | 6.63 (59×) | 7.11 (72×) | 11.06 (122×) | 187.2 (818×) |

- **B1 alone does not remove the retention**: at 250 names its heap is the current one's
  (464 M against 472 M words), and at 1,000 names it passes the 4 GB cap, as the current build
  does. Flambda does not inline the closures that matter.
- **B2 removes it.** The full dump finishes in 2.4 GB with coq-core's persistent algorithm,
  IDENTICAL to the pinned binary (`meancompare`: the same terminal output, `texput.log`
  `335b024c…`, clock readings, and `meanings_sha256` `4879fa65…`; also at 250 names). The deep
  probe (a forced full GC every 45 s, `o=40` so that the probe's own heap walk fits the cap; it
  still passed 4 GB during the sixth walk, at 244 s, so the run covers the first 46 % of the
  array writes):

  | CPU s | array sets | live words | reachable from the current state | reachable only from elsewhere | stdin bytes not yet read |
  |---|---|---|---|---|---|
  | 43.2 | 110,261,148 | 86,225,765 | 86,207,981 | −280,996 | 3,692,857 |
  | 80.5 | 198,761,202 | 87,174,389 | 87,156,609 | −281,000 | 3,365,408 |
  | 118.2 | 285,842,993 | 88,148,892 | 88,131,117 | −281,005 | 3,087,590 |
  | 154.5 | 370,267,605 | 89,091,099 | 89,073,311 | −280,992 | 2,824,270 |
  | 191.3 | 452,742,485 | 89,932,311 | 89,914,536 | −281,005 | 2,503,810 |

  Nothing is retained beyond the current state at any probe (−0.28 M is the program constants
  counted twice, as in §2.4). The live words grow by 3.7 M over 342 M writes: the output list.
  Unlike A (§2.5), where "reachable only from elsewhere" grew by 3 words per stdin byte
  consumed, B2 frees the consumed input too, because no frame holds an old state at all.
- **B2 is slower than A**: 1.3–1.6× per round on the full dump (persistent `Updated` nodes:
  417 M promoted words at 250 names, against 79 M in place), and its heap is larger (307 M
  against 267 M words at the end). **A + B2 is within noise of A** (§3.2).

**(d) Equivalence and risk.** B2: for each restructured function, a Coq lemma
`evale_new = evale` (by `reflexivity` or one `destruct fuel`). This is the best class: proved in
Coq, and no realizer is added. But **the memory property itself is "tested only"**: that old
versions are unreachable is a fact about compiled code and the GC, which no Coq statement
reaches. It can only be measured, with the probe of §2.1. One new closure capturing a state
anywhere, in an external, a helper or a future boundary model, brings the growth back silently.
*(Stage 2, §8.2: the standing check adds a typed static half over every closure the
extraction's realizers create, which catches such a closure without running it; the probe stays,
as the check of the compiled code.)*
The simulation also shows the property depends on the compiler: B2 must be measured on the
GitHub runner's non-flambda compiler too (stage 2), because the real B2 relies on the `fS`
closure's call being a tail call, and the simulation does not.

**(e) Effort.** B2: 1.5–2.5 days, depending on the guard checker, over about 15 functions, with
the same re-verification as A. B1: none to build (the switch exists), but it does not work.

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
the arrays' share (11 %), about 1.3–1.6× over A with T1 and T2. (Re-estimated on 2026-10-06 from
the class shares of §3.4, storage 19.5 % and GC 9.1 %: ≈ 1.2–1.4×.)

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

| | memory stops growing | how it is proved | trusted base added | speed (CPU, measured on profiling variants unless [I]) | fits the box |
|---|---|---|---|---|---|
| **A** in place, fail-closed | **yes**, by construction: a superseded version holds nothing, and a read of one stops the run | the term is unchanged; `LinArray.v` proves the realizer's model refines `PArray`; the OCaml module is checked against the model | one realizer row (≈ 60 lines), with a Coq-proved model | 1.09× over today alone; **10.2× with T1 + T2** at 250 names; with T1 + T2, ≈ 1,540× pdfTeX per name (§3.2) | yes (≈ 1.5 days) |
| **B2** persistent, fuel closures restructured | **yes, measured** (full dump in 2.4 GB, IDENTICAL), but only measured, and fragile: any closure that captures a state brings it back | Coq lemmas, by `reflexivity` | none | with T1 + T2, ≈ 1.4× slower than A (≈ 2,210× per name) | yes (1.5–2.5 days) |
| **B1** flambda `-O3` | **no** (measured: passes 4 GB at 1,000 names) | — | — | — | — |
| **C** state monad, mutable realizer | yes, by construction | a refinement theorem in Coq over the whole of `PS` | the monad's realizer (parametricity) | ≈ 1.2–1.4× over A + T1 + T2 [I, §3.4] | **no** (6–10 days) |
| **D** shallow embedding | no (needs A or C) | generated reflection lemmas | none beyond A or C | ≈ 1.1–1.2× over A + T1 + T2 [I, §3.4] | **no** (weeks) |

## 6. Recommendation and the stage-2 plan

*(Restated 2026-10-06 after the corrected timing, C-145, and the B measurements, §5 B.)*

**For memory, fund candidate A, with T1 and T2 in the same `Extract.v` change.**

1. It removes the growth **by construction**. B2 removes it too, measured on the full dump, with
   no new realizer, but only as a measured property that one new closure can silently undo, and
   at ≈ 1.4× the CPU. C removes it by construction too, but does not fit.
2. It keeps the Coq term byte-identical, so no theorem about `PS` and no translated line is
   touched. The trust it adds is one realizer whose model is **proved** in Coq to refine
   `PArray`, and its failure mode is a "no verdict", not a wrong verdict.
3. With T1 and T2, it is the change that moves speed by a **factor** over today (10.2× at 250
   names; the whole dump in 2.0 GB, IDENTICAL to the binary, on a profiling variant). T1 and T2
   are realizers of the same kind `ExtrOcamlZBigInt` already uses, and each one's obligation is
   an existing Coq theorem.
4. **If the owner does not accept the new realizer (question 2), B2 is the in-box alternative for
   memory** (it was C before B2 was measured). It needs no realizer, but stage 2 must then also
   commit the "reachable only from elsewhere" probe as a standing check, and measure B2 on the
   runner's non-flambda compiler.

**Memory is worth fixing whatever H.5's speed verdict is**: H.3's meanings clause (the full dump
on a 16 GB runner, IDENTICAL to `4879fa65…`) fails today on memory alone, and either A or B2
passes it on the measured profiling variants.

**Stage 2, 2026-10-07 → 2026-10-10:**

| day | work | done when |
|---|---|---|
| 10-07 | `Linparray` (OCaml) and `Superseded` in the driver; `Extract.v`: the `PArray` directives, then T1 and T2 as `Extract Constant` with no `Int64` boxing; `pipeline.sh` rebuild; `provenance.json` with `ocamlopt -config`, zarith, GMP and the C toolchain recorded | the build passes; `t1test` extended to T2 passes; the 50-name prefix is IDENTICAL to the committed one |
| 10-08 | `LinArray.v` (the store model, the trace semantics on `PArray`, the simulation theorem), compiled by `pipeline.sh`, `Print Assumptions` limited to the `PArray` axioms; H.2 re-verification: INITEX evidence, the 178-input differential (arm64 locally) | the theorem closed; no differential row changes class |
| 10-09 | H.3 re-verification: the round trip; E8's workflow re-run on a 16 GB runner, all 23,519 names (expected ≈ 2 GB from §2.5), with the native amd64 differential | the round trip = binary; the meanings clause compared against `4879fa65…` on the model build |
| 10-10 | H.5 speed on what can run (question 1), with `fairtime.sh` on a quiet machine or a CI runner, per E4; the report | the E11 verdict, written up either way |

(If question 2 is answered no: 10-07 and 10-08 become B2's restructuring of `Interp.v` and
`Boundary.v` with its `reflexivity` lemmas, and the standing retention probe.)

**Done on 2026-10-06, ahead of the plan (§8), while question 2 is still open.** B2 is now the
model build. Its reflexivity lemmas, the standing retention check and the H.2/H.3
re-verification are in place, and the full dump is IDENTICAL on the model build. `Boundary.v`
needed no change, because none of its fuelled functions holds a state across a call (§8.1).
If the owner accepts A and T1/T2 (question 2), they would come on top of B2 as a speed change;
memory no longer depends on them.

**The kill accounting, as E11 states it.**
- **Memory that does not grow with the work done:** A gives it (the live words are flat; only
  the I/O lists grow, at 24 bytes of heap per byte read or written, §2.5). B2 gives it as a
  measured property (§5 B).
- **Speed at or below 200× pdfTeX "on H.5's documents":** on the proxy, with A, T1 and T2, the
  format load is 59×, the 1,000-name run 122×, the whole dump 818×, and the marginal cost
  **≈ 1,540× per name** (§3.2). **On the proxy the kill criterion fires**: the marginal cost is
  7.7× past the kill line, and no profile-guided fix to ≤ 200× is in sight (§3.4: all the
  changes together, central estimate ≈ 370×, best case ≈ 150×, and only as a new verified
  execution model, which is the criterion's own fallback). The first version of this paragraph
  said "no kill on the proxy"; that rested on the inflated binary times (C-145).
- **But H.5's documents cannot run in the model before the PDF-side externals are modelled**
  (H.4's work), and the proxy is not a document (§3.3). So the speed condition *on H.5's
  documents* cannot be decided by 2026-10-10. The owner must say what counts (question 1).

**Questions for the owner:**
1. **What does the 2026-10-10 speed verdict measure, given that H.5's documents cannot run?**
   (a) The meaning-dump proxy: then **H.5's kill criterion fires** on the marginal cost
   (≈ 1,540×), and its fallback ("a verified-refinement fast interpreter becomes its own
   project") is what remains. (b) H.5's three documents in DVI mode (`\pdfoutput=0`), if the
   font-file externals they need can be modelled in the box: typesetting without the PDF back
   end. The one-line document would then be measured near its format load (59× on the proxy);
   the two papers would be measured for the first time, and the proxy predicts they fail [I].
   (c) Defer the speed verdict to after H.4 and judge memory alone on 10-10. Recommendation:
   (a) for the speed verdict, stated as on the proxy, because §3.4 finds no fix in sight that
   (b) could reveal; and (b) as evidence if the TFM path runs by 10-09.
2. **Does the trusted base accept realizers checked by a Coq-proved model plus review** (A's
   `Linparray`, as coq-core's `Parray` is today), and realizers whose obligations are existing
   Coq theorems (T1, T2)? If not: for memory, B2 (no realizer, measured property, in the box);
   for T1, emitting the IR's literals as `Z` (H.2's size measurement again) covers the largest
   part; T2 has no realizer-free alternative in the box, and without T1 and T2 the model is
   about 10× slower still.
3. **Given (1a), is the speed fallback wanted at all?** §3.4 sizes it: native int63 values, a
   mutable store and a shallow embedding together are estimated at ≈ 4× (≈ 10× at best) over
   today's best variant, still ≈ 6× short of the pass line (≈ 2.5× at best); reaching ≤ 60× needs compiled
   code generated from the IR with a verified compilation, a research project. Recommendation:
   finish stage 2 for memory (it is needed for H.3 either way), record H.5's speed kill on the
   proxy, and decide on the fallback as a separate funding question with §3.4 as its estimate.

## 7. What this stage commits

- This document.
- [`h5/README.md`](h5/README.md), with the binary-side recipes. They start the engine outside
  `_oracle.py`, so as in H.1–H.3 they are documentation, not scripts. (The 2026-10-06 correction
  commits one such script, `bintime.sh`, because the timing must be re-runnable; see below.)
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

**Added by the 2026-10-06 correction (C-145, C-146):**
- `h5/tools/bintime.sh` (the binary's CPU time on container-local storage; it starts the engine
  outside `_oracle.py`, and its header says why), `fairtime.sh` (the interleaved rounds),
  `fairtable.py` (their table), `b2sim.py` (the B2 simulation), `profrun.sh` (a capped run
  profiled by `sample`), `costclass.py` (the headroom classes), `zbench.ml` (`Z` against int).
- `h5/evidence/fair/`: the binary's runs with loads (`bin.txt`), the load log, the variants file,
  `fairtable.txt`, and in `runs/` the probes, verdicts, footprint traces and comparison classes
  of every run of the correction;
  `h5/evidence/b-variants.txt` (B1 and B2: build, `-dcmm` counts, the runs beyond the rounds,
  the comparisons); `gc-sensitivity.txt`; `zbench.txt`; `profile/prof-AB2-*` (samples, gzipped,
  and their class summaries).
- `scripts/tools/check_oracle_pin.py` (`SH_IN_IMAGE_ALLOW`) and
  `scripts/tools/check_oracle_infra_grading.py` (`OUTPUT_NAME_ALLOW`): `bintime.sh`'s one engine
  line and the timing harness's four log-naming lines, allow-listed by exact line, each with its
  reason; a new engine line, or a changed one, still fails (tested). `bintime.sh` reads the
  image from `_oracle.IMAGE`, so the pin has one source.
- In this document: §3.2 and §3.3 restated, §3.4 new, §5 B measured, §6 restated, the summary's
  items 5 and 7, and the compiler-configuration sentences of §2.2 and §4 (C-146).

Not committed: any change to the model. `h2/` is untouched, and the profiling variants are built
from the extracted tree under `~/.cache/`.

**Added by stage 2 (2026-10-06, §8), which DOES change the model:**
- `h2/coq/Interp.v` (B2), `h2/coq/RefInterp.v`, `h2/coq/B2Equiv.v`. `h2/pipeline.sh` compiles the
  two new files. `h2/provenance.py` records `ocamlopt -config` and zarith's version.
- The H.2 evidence, re-measured on the B2 build:
  - `h2/evidence/build/`;
  - `h2/evidence/inirun/` (`model-*.driver.out`, `run.json`);
  - `h2/diff/results-*.tsv`.
- The H.3 evidence:
  - `h3/evidence/roundtrip/roundtrip.json` (`h5_stage2_b2_rerun`);
  - `h3/evidence/meanings/run3-37397064131/` (E8's workflow on the B2 build).
- `h5/tools/b2gen.py`, `b2static.py`, `b2cmt.ml`, `b2static_kill.py`, `retprobe.ml`, `retention_probe.sh`.
- `h5/evidence/stage2/`:
  - `b2-proofs.txt`;
  - `retprobe/` (§8.2: the four runs and their `commands.sh`, the ten single-member reverts in
    `reverts/`, and the first version's runs, superseded, in `v1-cpu-period/`);
  - `static/` (§8.2: `b2static.py` on both trees, and the 19 kill-tests);
  - `fulldump/` (the local full dump: `compare.json`, the CPU and memory record, loads, the
    output hashes).
- On branch `ci/v27165-h3-meanings`: the workflow's run 3 (matrix `full`, `prefixes`).

## 8. Stage 2 (2026-10-06): B2 in the model build [M, R]

The owner has not yet said whether the trusted base accepts new realizers (§6, question 2: A's
`Linparray`, T1, T2). The memory fix is needed in every case, because H.3's meanings clause cannot
be checked without it. So stage 2 builds **B2 alone**: no change to `Extract.v`, no T1 or T2, and
coq-core's persistent arrays unchanged. Code: `h2/coq/` (the model) and `h5/tools/b2gen.py`,
`b2static.py`, `retprobe.ml`, `retention_probe.sh`; evidence: `h5/evidence/stage2/`.

### 8.1 The restructuring, and its proofs [M, R]

- **`Interp.v`** is generated by [`b2gen.py`](h5/tools/b2gen.py) from the pre-B2 file
  (`git 9c3315be`, sha256 `1ef36d75…`). Lines 1–178 (the types, the helpers, the section header,
  `truth_or`) are unchanged. For each of the ten members of the mutual block (`evale`, `evall`,
  `evalargs`, `evalx`, `callp`, `exec`, `for_loop`, `exec_list`, `goto_in`, `write_items`), the
  successor branch is moved **verbatim** into a `Definition NAME_body`, abstracted over the
  recursive functions it calls and the fuel `f`. The member itself becomes
  `match fuel with O => <its old O branch> | S f => NAME_body <recursive functions> f <arguments> end`.
- **The guard question of §5 B(a) is answered**: Coq 8.18 accepts the first form. The guard
  checker unfolds `NAME_body` when its arguments fail the check (the bare recursive functions), and
  then sees every recursive call applied to `f`.
- **`RefInterp.v`** is the pre-B2 section (lines 169–707), verbatim, under an import of
  `Interp`, so both blocks share the same types and helpers. `b2gen.py --check git ../../h2/coq`
  regenerates both files from the git object and compares them byte for byte (OK).
- **`B2Equiv.v`** proves `Interp.X = RefInterp.X` for each of the ten members, and
  `Main.run = fun fuel x => RefInterp.callp procs_array nglobals ext fuel P_mainbody [] (initial_state x)`
  (the program's semantics over the pre-B2 interpreter). **Every proof is `reflexivity`**: the
  kernel unfolds `NAME_body`, beta-reduces, and finds the same fixpoint bodies.
  - `Print Assumptions run_b2` lists only the kernel's primitive types and operations
    (`PrimInt63`, `PrimFloat`, `PArray`), which the statements' own terms use. There is no axiom.
  - A negative control in the file (`Fail reflexivity` against the pre-B2 block run with one more
    unit of fuel) shows that conversion does not identify everything.
  - A mutation control, outside the build: changing one branch of `exec_body` (`SLabel _ => SNorm st`
    to `SRet st`) makes `exec_b2` fail ("Unable to unify"). Appending one comment line to
    `RefInterp.v` makes `b2gen.py --check` fail.

  All of this is in `h5/evidence/stage2/b2-proofs.txt`.
- **Proof obligations**: these eleven equalities, nothing else. `pipeline.sh` compiles both new
  files on every build (`RefInterp.v` after `Interp.v`, `B2Equiv.v` after `Main.v`), so a
  change that breaks the equality breaks the build.

**In trusted-base terms: nothing new** [R]. `git diff 9c3315be` is empty for `Extract.v` (the
realizers), `driver.ml`, `Boundary.v`, `Values.v`, `Main.v` and the translator. The generated Coq
tree is unchanged (`e9ae7712…`). In the extracted tree, only `Interp.ml` and `Interp.mli` differ
(tree `72b2ea79…` → `dbace323…`). `RefInterp.v` and `B2Equiv.v` are proofs: `Extract.v` does not
import them, and nothing in the model depends on them. What B2 relies on that is not new:
- Coq's extraction, which was already in TB-1. It is used as before, with the same directives.
- ocamlopt, which was already trusted.

What B2 does **not** give is a theorem about memory. That no closure holds a state is a property
of the compiled code and the GC (§5 B(d)), and it is checked by test (§8.2), not proved.

**The extracted shape** [R]. Each member's successor closure is now a single call:
`fun f -> evale_body procs strings_base ext evale evall evalargs evalx callp0 f e st`. The closure's
environment is dead once the call starts. Inside `NAME_body`, the state is an ordinary parameter,
so `ocamlopt` frees it after its last use. Two things changed in how the extracted code calls:
- the bodies call the recursive functions through closure parameters, so those are now unknown
  calls instead of direct ones;
- `exec_body` takes 14 arguments.

Not restructured: the 23 other uses of the fuel realizer, and every use of the other realizers
that take one closure per branch (Z, N, positive, ascii). The first version of `b2static.py`
checked only the fuel realizer, and allowed those 23 sites by `(file, function)` with a reason
each. Since the review hardening (§8.2, C-150) it checks, by type, all 669 branch closures at the
241 realizer uses of the extracted tree, and also the 44 `fun`s of the source passed as
arguments. The 23 pass without an allow entry. Seven closures remain allowed, each by an
argument the tool checks: four in Coq's polymorphic `Pos.iter` and `Pos.iter_op`,
`ERealloc`'s, and the two callbacks the interpreter passes to the C boundary (§8.2).

### 8.2 The standing retention check, failing before B2 and passing after [M]

[`retention_probe.sh ML_DIR OUT_DIR INPUT_DIR [CAP_MB [TIMEOUT_S]]`](h5/tools/retention_probe.sh)
has two halves. Both always run, and **both are required for a PASS**: the dynamic half alone
never passes, and if the static half cannot run (no summary line) the verdict is INCONCLUSIVE
before the dynamic half starts. Two independent reviews of the first version (commit `953fe1eb`)
found it sound but weaker than stated; this is the hardened version (C-150).

1. **Static**: [`b2static.py`](h5/tools/b2static.py), with its typed half
   [`b2cmt.ml`](h5/tools/b2cmt.ml). It covers **every** branch closure that Coq's extraction
   creates, not only the fuel's: the realizers of `match` on nat (the fuel), Z, N, positive and
   ascii each take one closure per branch, and the Z realizer's closures have the same shape as
   the fuel's (`ERealloc`, below). On the B2 tree that is 669 closures at 241 realizer uses. It
   also checks every `fun` written in the source and passed as an argument (44), for which the
   callee matters too: unless the callee's typed body uses that parameter only as one call in
   tail position, the callee may keep the closure while it does other work.
   - **Coverage**: the realizer texts are read from the installed Coq's extraction library, and
     each file's count of each text must equal the number of typed sites found there. A realizer
     the check does not know fails it.
   - **Typed analysis**: the tree is typed with `-bin-annot`, and each closure is classified
     from the typed tree. A call is LEAF (a primitive, a library function, or a tree function
     that performs a bounded number of `Parray.set` fixed by its code), LOOP (a tree function
     that writes in a recursive loop over its data, such as `copy_cells` or `put_cells`), or RUN
     (a parameter, a local function, or anything that can run code it was given: these are the
     calls that can re-enter the interpreter). The classes come from a fixpoint over the call
     graph of the whole tree. A closure is **DEAD** when its environment is dead during every
     non-leaf call: the call is in tail position, or nothing that runs after it inside the
     closure reads a free variable. It is
     **STATEFREE** when no free variable's type can reach a state (a function, a type variable,
     a persistent array or an unknown type counts as able to). It is **LOOP** when the only
     non-leaf calls made with its environment live are LOOP calls. Otherwise it **HOLDS**: it may
     keep a state alive across a call that can re-enter the interpreter.
   - Why LOOP passes: an old version of a persistent array keeps alive one Diff node per update
     made after it. So a closure held across a write loop retains at most that loop's writes,
     and only until the loop returns. It cannot retain the rest of the run, which is what the
     211 M words were. Only a RUN call can do that.
   - **B2's structure**: `Interp.callp` must contain the ten members, each one fuel realizer
     whose successor closure is a single call of `NAME_body` on identifiers, and each DEAD.
   - **Allowed closures**: every HOLDS closure needs an entry keyed by (file, top-level
     function, realizer, closure index). The entry carries the exact number of HOLDS closures it
     covers, so a second site under the same key fails. It also carries a **check** that the
     tool runs on the tree, so the argument for the entry is checked, not only stated. The key
     is the typed top-level function, so a local `let` cannot stand in for it (the first version
     matched local bindings by regular expression).
2. **Dynamic**: [`retprobe.ml`](h5/tools/retprobe.ml) is linked into a copy of the tree, around
   the C boundary (one line of `Main0.ml` and two of `driver.ml`, each asserted to match once;
   coq-core's `Parray` unchanged). The copy is run under `capped.sh`.
   - **Where it probes is fixed by the program, not by the machine.** The first version probed
     every 5 s of CPU. A control run on the unmodified B2 build got only 3 probes in 42 s of CPU,
     a faster machine would get 2 (INCONCLUSIVE), and only one probe ever fell in the format
     load. Now the run is cut into phases by the external calls that open and close the format
     file: **init** (before the first `wopenin`), **load** (up to the `wclose` after it) and
     **dump** (after it). Within each phase it probes at the external calls whose ordinal is 1,
     4, 16, 64, …, once more at the `wclose` that ends the load, and once at the end of the run.
     The external-call sequence is the program's own, so every machine probes the same program
     points.
   - At each probe it forces a full major GC and computes `live − reach_state − static`: the
     words that are live but not reachable from the state the program is computing with.
   - Any probe above **1,000,000 words (8 MB)** stops the run with exit 6.
   - **PASS** needs a static PASS, the run to finish with exit 0, the end of the load reached,
     and at least **3 probes in the load and 3 in the dump**, every one under the limit.
     **FAIL** is a static failure or a probe over the limit. Anything else is **INCONCLUSIVE**.

The limit sits far from both sides of the measured gap. Before B2, the retained words were
105 M at the load's first probe and 211 M at its end (§2.1). After B2 they are −0.28 M, which is
the program constants counted twice. Under A, the consumed input reached 10 M words at most
(§2.5).

**The allowed closures, and what the tool checks for each** (`h5/evidence/stage2/static/`):
- Coq's `Pos.iter` and `Pos.iter_op` (4 closures): polymorphic library code whose closures hold a
  value of a type variable and a function across a call. The check: every use outside their own
  definitions instantiates them at state-free types and passes only global functions. `Pos.iter`
  has 0 uses; `Pos.iter_op` has 1, in `Pos.to_nat`, at `int` with `Nat.add`.
- `ERealloc`'s branch for a zero offset (1 closure, in `evale_body`): it holds `st1` across
  `evale f n st1`, a non-tail RUN call. The check:
  - (a) that is its only non-tail RUN call;
  - (b) all 5 `ERealloc` in the program have the size `n = ELoad (TI32, LGlob _)`;
  - (c) evaluating such an `n` is `evall` on an `LGlob`, which calls nothing, then `read_loc`,
    which is a leaf and writes nothing. The two branches are compared with the text this
    argument was made for.

  So no `Parray.set` happens while `st1` is held. The reviewers saw that this closure has the
  fuel closures' shape; the typed analysis also found that it holds `st1` across `copy_cells`
  and `new_block` after `evale` returns. Those two are LOOP calls, bounded by the cells copied
  (C-150).
- The two callbacks the interpreter gives the C boundary, `ext (fun p cs st' -> callp0 f p cs st')`
  in `evale_body` (`EExt`) and `exec_body` (`SExt`). `Boundary.ext` may keep them while it runs,
  and their environment, `callp0` (a function) and `f` (the fuel, typed by a type variable),
  cannot be cleared by type. The check:
  - (a) their free variables are exactly `callp0` and `f`;
  - (b) B2's structure holds, and each body is used once, by its member, so `f` is the
    successor closure's fuel and `callp0` is a member of `callp`'s `let rec`;
  - (c) `callp` is applied once, in `Main0`, as `callp procs_array nglobals ext fuel`, so that
    `let rec`'s environment is the program's constants.

  So they hold no state.
- The B2 tree has one LOOP closure, in `Boundary.wopenin`: it holds the state across
  `alloc_cells`, which writes the file name's bytes. It passes, and is listed in the output.
- The `truth_or` continuations of `EAnd` and `EOr` hold `st1` across `evale` on the right
  operand by type, but nothing after that call reads it, and `truth_or` calls its continuation
  once, in tail position: DEAD. An analysis that asked only for tail position would flag them;
  what clears them is that the environment is dead after the call.

**Scope** [R]. The static half covers the closures that the realizers create and the `fun`s
passed as arguments. It does not cover a function value bound by a local `let` and called later.
A call to such a function is RUN, so its callers are judged conservatively, but its own
environment is not analysed.

**Kill-tests** ([`b2static_kill.py`](h5/tools/b2static_kill.py); `h5/evidence/stage2/static/kill-tests.txt`):
**21 of 21** behave as expected:
- the unchanged B2 tree passes, and the pre-B2 tree fails (24 failures);
- for each of the ten members, a copy whose successor closure reads its state after its call
  fails both the structure check and the typed check, which reports that member's closure as
  HOLDS;
- a second HOLDS closure under the allowed key `(evale_body, Z, 0)` fails ("2 HOLDS closures,
  the entry allows exactly 1");
- an `ERealloc` whose size is not `ELoad (TI32, LGlob _)` fails (b);
- a changed `ELoad` branch fails (c);
- a new closure in `Boundary` that holds a state across a parameter call fails;
- `Pos.iter_op` instantiated at a state fails;
- a realizer text the typed half cannot see (in a comment) fails coverage;
- a closure that holds a state across a write loop passes as LOOP;
- an `EExt` callback that also captures the state fails (a);
- a source `fun` given to `List.map` that holds a state across a parameter call fails.

**Runs** (`h5/evidence/stage2/retprobe/`, exact commands in `commands.sh`; the one-minute load
average was 5.3–8.5 at the start and end of each run):

| tree | static | dynamic | verdict |
|---|---|---|---|
| pre-B2 (H.3 checkpoint 2, `72b2ea79…`), 250 names | 24 failures: the ten members' structure (10, and the summary line), the ten members' closures HOLDS (10), and three closures that before B2 sit in `callp`, not under their allowed keys (`ERealloc` and the two callbacks) | init 3 probes under the limit; **first load probe (external call 61): 104,881,953 words** live but not reachable from the current state (live 167.7 M, state 62.5 M); stopped with exit 6 | **FAIL** |
| pre-B2, 50 names | as above | the same probe, the same 104,881,953 words | **FAIL** |
| B2 (`dbace323…`), 250 names | 669 realizer closures: 663 DEAD, 1 LOOP, 5 HOLDS; 44 source `fun`s: 41 DEAD, 1 STATEFREE, 2 HOLDS; all 7 HOLDS allowed and checked; 10/10 members; 0 failing | **18 probes: init 3, load 9 (the end of the load included), dump 6**, every one between −292,702 and −281,017 words; finished, exit 0 | **PASS** |
| B2, 50 names | as above | **17 probes: init 3, load 9, dump 5**, the same range; finished, exit 0 | **PASS** (INCONCLUSIVE in the first version, with 2 probes) |

The init and load probes fall at the same external calls in all four runs (1, 4, 16, 61, 64,
76, 124, 316, 1,084, 4,156, 16,444, 24,254), and before B2 the retained count is the same to
the word at 50 and at 250 names. The first version's runs are kept, superseded, in
`retprobe/v1-cpu-period/`. Their p50 command line was never committed, and the scratch script's
20 s period does not match their probe spacing (C-150; `h5/evidence/stage2/retprobe/v1-cpu-period/NOTE.txt`).

**What the dynamic half catches, and what it does not** [M]. A reviewer reverted single members
in the Coq source and found that the first version's dynamic half caught only 3 of the 10
(`callp`, `exec_list`, `exec`), even at 1,000 names. The other seven do not retain on
meaning-dump workloads. Re-measured on the hardened probe
(`retprobe/reverts/`, `summary.tsv`): one copy per member of the B2 tree whose successor closure
reads its state after its call, 250 names.
- The dynamic half catches **5 of 10**:
  - `callp0`, `exec` and `exec_list`, with 104.9 M words at the load's first probe;
  - `evale`, with 14.6 M at the load's 4th external call;
  - `goto_in`, with 3.9 M at the dump's 64th.
- It does **not** catch `evall`, `evalargs`, `evalx`, `for_loop` or `write_items`. Each finished
  with exit 0 and 18 probes under the limit. Their closures do hold a state, but not across
  enough work on this input to show.
- The static half fails **all 10**.

A first attempt at these copies read the state with a plain `ignore st`. The compiler removed
that read, and none of the seven runs that finished retained anything. The static half
still flagged all ten: it reads the typed tree, not the compiled code [M, not kept as evidence].
**So the guarantee for those five members rests on the static half alone**, which is why it is
required, never optional. The dynamic half is the check that the static model of retention
matches the compiled code and the GC (§5 B(d)), not a second detector of every regression.

### 8.3 Fidelity, re-verified on the B2 build [M]

- **INITEX** (`h2/evidence/inirun/`): terminal output, standard error and `texput.log` are
  byte-identical to the previous build's, in both configurations. `verify_h2.py --reproduce
  model` is OK on `cae7a953…`, and `--reproduce translate` is OK as well.
- **The 178-input differential** (`h2/diff/results-*.tsv`), with the model side re-run in both
  configurations against the unchanged binary outputs: **no row changed**. Every column but the
  `ps.exe` prefix is the same as before, on all 178 rows in each configuration. The totals stay
  134 identical, 43 Stuck, 1 without a result and 0 divergent. The one without a result is
  `romn`, still killed by the 5,000 MB cap, so its memory is not this retention [I: the
  retention check was not run on it].
- **The round trip**: exit 0; terminal output and `texput.log` equal to the binary's; the format
  stream is `55629ae0…`, so model = binary (E6). 78.0 s user CPU, peak footprint 1,624 MB
  (checkpoint 2's build: 4,102 MB).
- **`verify_h2.py`**: pure, `--reproduce translate` and `--reproduce model` are all OK, against
  the new `provenance.json`. It records `ocamlopt -config` in full, which C-146 asked for.

### 8.4 The full meaning dump on the model build: H.3's meanings clause MET [M]

It ran locally, because its CPU time was under an hour, and also on E8's GitHub workflow, because
the runner's OCaml has no flambda (§5 B(d)).
- **Local** (macOS arm64, `capped.sh` with a 4,000 MB cap; `h5/evidence/stage2/fulldump/`):
  - exit 0; 2,672.6 s of CPU (2,564.9 s user and 107.7 s sys), 3,623 s wall;
  - peak footprint 2,463 MB;
  - the one-minute load average was 8.3–283 (median 171);
  - **IDENTICAL to the pinned binary, with `meanings_sha256` `4879fa65…`**. `texput.log` is
    `335b024c…`, the same as stage 1's profiling variants.

  The footprint grows from 2,120 MB at 2 minutes to 2,463 MB at the end, over 23,519 names. That
  is ≈ 15 kB per name, against ≈ 3.1 MB per name before B2. It is the I/O residual of §2.5: the
  output list, together with the GC's heap pacing.
- **GitHub runner, run 3** (37397064131; H3-report.md, "H.5 stage 2"; x86_64, OCaml 5.2.0
  **without flambda**, the same extracted tree `dbace323…`):
  - exit 0; 2,474.9 s of CPU; peak RSS 2.47 GB, under a 14.3 GB cap;
  - **IDENTICAL, `4879fa65…`**;
  - the prefixes job's peak RSS is 1.42 GB at 0 names and 2.02 GB at 4,000. The pre-B2 build
    reached 9.16 GB at 2,000 names on the same runner type and was killed at 4,000.

  So B2's property does not depend on flambda. This answers the open point of §5 B(d): the
  simulation relied on a beta-reduction, while the real B2 relies on the successor closure
  being dead once its single call starts. That should hold whether or not the call is compiled
  as a tail call, because nothing is read from the closure's environment after the call [I]. The
  runner's measurement is consistent with that; it does not show which way the call was compiled.

**Speed, for the record** (not E11's criterion here). B2 alone is the model build without T1 and
T2, so it keeps the cost of the integer conversions (§3.1).
- The local full dump took 2,673 s of CPU. The binary's median for the same run is 0.229 s
  (§3.2), so the ratio is ≈ 11,700×. This is a single run under a load of up to 283, not one
  of §3.2's interleaved rounds.
- The B2 profiling variant of §5 B, which has T1 and T2, took 267.7 s, 10× less. That matches
  §3.1: the integer conversions are where the time goes.

The pass and kill lines of H.5 are as in §3.3 and §6: on the proxy, the kill criterion fires
with or without B2.
