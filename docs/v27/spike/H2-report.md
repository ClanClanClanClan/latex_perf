# Foundation spike, step H.2: the translator and the Coq program

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123),
step H.2 of the ADR-014 draft §9. Code: [`h2/`](h2/README.md).
**Pass criterion (verbatim):** "100 % of procedures translated; Coq accepts the term; the extracted
binary runs INITEX to the `*` prompt".
**Kill criterion (verbatim):** "the Coq term or its extraction is intractable (> 2 h compile or
> 16 GB)". Fallback if it fires: "split the program into per-part modules, or emit a shallow
embedding with a generated reflection lemma".

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## Checkpoints

| # | date | what | against the criteria |
|---|---|---|---|
| 1 | 2026-09-30 | translator front end complete; the whole program emitted as a Coq term and accepted | procedures 603/603 translated [M]; Coq accepts the term [M]; kill criterion not approached |
| 2 | 2026-09-30 | `PS` as a fuelled interpreter in Coq, the C boundary INITEX needs, extraction, the INITEX run | **pass criterion met** [M]; kill criterion not approached |
| 3 | 2026-10-01 | review round 1: two adversarial reviews (fidelity; claims and trust), every finding reproduced and closed (§"Review round 1") | pass criterion still met on the rebuilt program [M]; kill criterion not approached |

**Verdict: H.2's pass criterion is met and its kill criterion did not fire.** The whole of the
tangled pdfTeX is a Coq program; Coq accepts it with its semantics; the extracted program runs
INITEX exactly as the binary does on the run the criterion names. What the criterion does not
ask, and H.2 does not show, is listed under "Open": the model is exact only where the C boundary
is modelled (23 of 189 externals), on the environment class it states.

The numbers below are those of the program as rebuilt at checkpoint 3, from a from-scratch
`pipeline.sh` run whose measurements and provenance are committed in
[`h2/evidence/build/`](h2/evidence/build/) (`measure.tsv`, `provenance.json`). A second
from-scratch build gave the same `ps.exe` byte for byte (sha256 `991ae9a5…`): the build is
deterministic, so every committed model output is bound to one program [M].

## Checkpoint 1: every procedure translated; Coq accepts the term [M]

- **Input.** `pdftex.p` of r78081 (tangle output; byte-identical in the aarch64 and x86_64 build
  trees; sha256 `d1a7d257…5910`) with web2c's four `.defines` files: 247,399 tokens, 603 procedures
  and functions (the ADR-014 draft guessed ≈ 1,400 [I]; TeX Live's program has no main block, its
  main program is the procedure `mainbody`), 690 globals, 63 constants, 35 types.
- **Translated: 603 of 603 procedures** (0 failures), 185,086 IR nodes (`manifest.json`; the
  report said 183,086 at checkpoints 1 and 2, a figure in no artefact, C-109; the count was
  185,084 before checkpoint 3 added web2c's unary-minus cast), 189 distinct externals (C
  functions and macros the program calls: the C boundary as the program sees it), 101 string
  literals.
- **Coq accepts the term.** `coqc` 8.18.0. Checkpoint 1's own figure (44 s, 456 MB for the syntax
  files) is not in any committed artefact; the committed measurement is checkpoint 3's below.

### What the translator decides, and from which source [R]

Every rule below changes what the binary computes, so each is taken from web2c's own code of the
pinned revision, not from Pascal's definition:

1. **Conditionals** (`ifdef('X')`): evaluated against the build's configuration: `STAT`, `INITEX`
   (`pdftexd.h`) and `IPC` (`c-auto.h`, and `ipcpage` is in the binary) defined; `TEXMF_DEBUG` not.
2. **Expression grouping is C's.** web2c writes an expression's tokens in source order and the C
   compiler re-parses them. Pascal (web2c's yacc precedences) puts `and`/`or` above the relational
   operators, C below. The two readings differ at **8 places**; e.g. `fixpdfdraftmode`'s
   `fixedpdfdraftmodeset and fixedpdfdraftmode>0` is `(set and mode) > 0` in Pascal and
   `set && (mode > 0)` in the binary. The IR follows the binary (`h2/translate/cprec.py`).
3. **C types.** web2c's subrange rule (`unsigned char`, `schar`, `short`, `unsigned short`, else
   `integer`; any symbolic bound gives `integer`), `integer` = int (32 bits), `longinteger` = off_t
   (64), `boolean` = int, `real`/`glueratio` = double, plain `char` = C char (signedness per
   architecture, H.1 §5.4). Integer literals above 32767 in magnitude carry web2c's `L` suffix and
   are 64-bit, so `65536L*texremainder` is a 64-bit product in the binary.
4. **Unary minus is `- (integer)`** (web2c-parser.y, `UNARY_OP: unary_minus_tok { my_output ("-
   (integer)"); }`; added at checkpoint 3, review A finding 3): the operand is converted to C
   `int` before it is negated, whatever its type. At the 4 sites whose operand is a `longinteger`
   the conversion narrows (outside `int`: Stuck, C's implementation-defined conversion); no
   operand is a `real`. Before checkpoint 3 the IR negated in the operand's own type.
5. **Union words** (`texmfmem.h`, little-endian): `hh.rh` and `cint` share bytes 4–7, `hh.b0` is a
   `short` at bytes 2–3, `qqqq.b0` the byte at 7, `gr` all 8 bytes.
6. **`goto 10` is `return`** in TeX mode except in `macrocall`, `hpack`, `vpackage`, `trybreak`
   (web2c-parser.y `doreturn`): 195 of the 747 gotos, in 102 procedures, are returns.
7. **Gotos into structured statements.** Two gotos jump into a sibling `case` arm
   (`prunepagetop`'s `goto 60`, `getnext`'s `goto 40`), which C allows. Every goto resolves to a
   label in an enclosing statement list or inside one of its elements, never through a `for`
   body (`h2/translate/gotos.py`, run on every translation, for the other 552 gotos); PS resumes
   inside the element by continuation.
8. **Writes** (`fixwrites.c`): each item is `%c`, `%s` or `%ld` by its first token; widths are
   dropped.

## Checkpoint 2: `PS`, the boundary, extraction, and INITEX to the `*` prompt [M]

**The run.** `pdftex -ini` in the pinned image, terminal input `\relax` then end of file, the run
identity of [`h2/diff/base.spec`](h2/diff/base.spec) (`SOURCE_DATE_EPOCH=1788076260`,
`FORCE_SOURCE_DATE=1`, the image's kpathsea values, and fixed clock readings given to the binary
by an `LD_PRELOAD` shim of `gettimeofday`, [`h2/diff/clockshim.c`](h2/diff/clockshim.c)):

```
This is pdfTeX, Version 3.141592653-2.6-1.40.29 (TeX Live 2026) (INITEX)
 restricted \write18 enabled.
**
*
! Emergency stop.
<*> 
    
No pages of output.
Transcript written on texput.log.
```

exit status 1. The extracted model, given the same run identity, writes **the same terminal
bytes, the same `texput.log` bytes, nothing on standard error, and exits 1**
([`h2/evidence/inirun/`](h2/evidence/inirun/), with `run.json` naming the `ps.exe` and every
file by sha256; re-checked by `verify_h2.py`). On the way it runs `mainbody`, `initialize`,
`initprim` (every primitive installed through the translated `primitive`), `loadpoolstrings`
(1,849 pool strings through the translated `makestring`), reads the first line at `**`, runs
`maincontrol`, opens the log, prompts `*`, meets end of file, and runs `fatalerror`, `jumpout`
and `closefilesandterminate`.

**Configurations: what "both architectures" means here** (corrected at checkpoint 3, review B
LOW-3; checkpoint 2 said "byte-identical to the pinned binary's on both architectures", C-109).
The model has two architecture parameters: plain `char` signedness (`charsigned`) and
contraction (fused multiply-add), which is **not modelled**: `PS` is always unfused. So:
- the **x86_64 configuration** (`charsigned 1`, unfused) is x86_64's on both parameters; it was
  compared with the pinned amd64 binary **run under qemu-user emulation** on an arm64 host (no
  native amd64 run: the owner approved one on 2026-09-30, and it needs a CI workflow the owner
  has not yet permitted);
- the **aarch64 configuration** (`charsigned 0`, unfused) is a hybrid: aarch64's `char` with
  x86_64's floating point. It was compared with the pinned arm64 binary, natively. Its agreement
  says nothing about aarch64's fused sites (H.1 §5.1) unless an input reaches one.
- Checkpoint 2 ran the model once, in the aarch64 configuration only, and compared it with both
  binaries. Checkpoint 3 runs both configurations, each against its own architecture's binary.

**Measured cost** (`h2/evidence/build/measure.tsv`, a from-scratch `pipeline.sh`; M-series Mac;
each row records the 1-minute load average at its start, which was between 155 and 304 during
this build: the machine was shared, so wall times are upper bounds; user times are given too):

| stage | files | wall | user | peak memory |
|---|---|---|---|---|
| translation (`emit_coq.py`) | 1 | 6.6 s | 4.8 s | 97 MB |
| `coqc` (syntax, semantics, globals, pool, 16 procedure files, boundary, C main, main) | 25 | coqc: 25 file(s), 51 s wall, peak 484 MB | 26.0 s | 484 MB (largest file 4.7 s) |
| extraction (`coqc Extract.v`, `Separate Extraction`) | 1 | extraction: 1 file(s), 8 s wall, peak 540 MB | 4.2 s | 540 MB |
| `ocamlopt` | 93 | ocamlopt: 93 file(s), 101 s wall, peak 503 MB | 41.5 s | 503 MB (one module) |

The kill criterion is > 2 h or > 16 GB. **Corrections to checkpoint 2's table** (review B LOW-1,
C-109): its "257 s" for `coqc` included the extraction's 33 s; its "largest file 13 s" was 19.2 s
(`Prog_14.v`); its 586 MB was the extraction's peak, Coq's own was 468 MB; its INITEX run
figure (49.8 s wall, 29.0 s user, 1.18 GB) was in no artefact. Those numbers were from a run at a
lower load average (57–114) that was ten times slower per file than the run above; the cause of
that difference was not isolated, which is why every figure now carries its load and its user
time. Two observations on the way remain: extracting everything into one OCaml file made
`ocamlopt` take 276 s and 4.9 GB, and Z literals extracted as big-integer arithmetic made the
file 39 MB (AST numbers are now primitive 63-bit integers); neither figure is in an artefact.

**Speed is not measured here** (review B LOW-2). Checkpoint 2 called the model "roughly 150–300
times slower" than pdfTeX. That ratio was wall time against wall time, under load, on a run
dominated by start-up (the model initialises every table and the pool before the first line).
Review B measured about 134× at the median (88–203×) and about 235× on a larger input. **None of
these is an H.5 measurement**, which is per pass on the documents H.5 names, on a quiet machine;
the owner funded no speed optimisation and asked for that measurement during H.3.

### What `PS` is (coq/Values.v, coq/Interp.v)

A deep embedding with a big-step interpreter. **Fuel** (corrected at checkpoint 3, review B
MEDIUM-3) is a bound on the *height* of the evaluation derivation, not on the number of steps:
every node of the derivation consumes one unit from its parent's fuel, and a loop's next
iteration and a statement list's next statement are evaluated with the fuel of the node that
started them, so a run of 10⁹ steps can finish with fuel 4·10⁹ and the number of steps is not
bounded by the fuel. What "every run ends" means: the interpreter is a Coq function defined by
structural recursion on the fuel, so for every program, input and fuel it returns: a result, an
exit status, or Stuck, "fuel exhausted" included (outside the tier). It is not a statement that
the program terminates. The extracted program can still fail outside that result type: an OCaml
stack overflow or out-of-memory is reported by the driver as "model resource limit (no
verdict)", exit status 3.

Values are C's: integers with their C type (after web2c's typing), doubles as Coq primitive
floats (IEEE binary64, round-to-nearest, unfused), pointers as (block, offset), union words as
bytes with a defined-byte mask. **The Stuck rule was accepted by the owner on 2026-09-30** (H.1
report §8; it was a proposal at checkpoint 2): signed overflow in `int` or `long`, division or
remainder by zero, `INT_MIN / -1`, a conversion out of range (C's implementation-defined or
undefined conversions), a read of a never-written scalar, an out-of-bounds access, use after
`free`, a NaN's bit pattern (its sign and payload are the architecture's), an unmodelled
external, fuel exhausted. **One exception, which follows the binary:** the 13 pointer-arithmetic
sites that form a pointer before the start of its array (`hash := yhash - hashoffset` and its
like) are ISO C undefined behaviour, and `PS` does not make them Stuck: it computes plain address
arithmetic and checks bounds at every access, because gcc compiled them so (a claim about the
binary not yet checked in its disassembly, "Open" below).

Plain `char` loads are the parameter `charsigned`. A double converted to an integer type on a
store or an argument (C11 6.3.1.4, implicit) is truncated toward zero, Stuck when the result is
outside the type (corrected at checkpoint 3: checkpoint 2 made every such store Stuck, which is
why `\pdfelapsedtime` was Stuck "by accident", in `getmicrointerval`'s
`((m - microseconds)/100) * 65536 / 10000`, a double assigned to the integer result; it is now
computed from the clock readings, review A finding 1).

### What the translator had to decide that checkpoint 1 had not [R]

1. **`mem` and `eqtb` are locals.** web2c's `pdftexcoerce.h` gives every procedure that uses them
   `register memoryword *mem=zmem, *eqtb=zeqtb;`: a copy taken on entry. A procedure that
   reallocates `zmem` does not change its callers' `mem`. The translator reads the header and
   gives each such procedure the two locals and their initialisation.
2. **The integer constant 0 assigned to a pointer is NULL** (C's null pointer constant):
   `pdffontmap[fontk] := 0`. Every other assignment or argument whose C type does not match is a
   translation error.
3. **Pointer arithmetic outside an object.** `hash := yhash - hashoffset` forms a pointer before
   the start of its array on every run, which ISO C makes undefined. PS follows the binary (above).
4. **Evaluation order** (`h2/translate/evalorder.py`). Effect summaries (globals and heap blocks read
   and written, transitively, var-parameter targets mapped to the actual argument) for every
   procedure; each modelled external declares its effects from its C source (and the translator
   refuses to run if that table and `Boundary.v` name different externals); an unmodelled
   external is Stuck anyway, so it has no effect on runs that are not Stuck. Of 45,742 unsequenced
   pairs checked, **29 of them** (in 18 procedures) may depend on the order; each is emitted as `EUnseq`/`SUnseq`,
   which is Stuck when reached. The analysis is path-insensitive, so a flagged site is not shown
   to be order-dependent: e.g. `objtab[b].int4 := pdfgetmem(5)` (`appendbead`) is flagged because
   `pdfgetmem`'s summary includes everything its overflow and error paths may write, `objtab`
   among them, although those paths end the run. Which of the 29 are truly order-dependent, and
   which order gcc chose at each, is open.

### The C boundary modelled so far (coq/Boundary.v)

23 of the 189 externals the program names, each with the C function it follows: the three
standard streams, `setupboundvariable`, `topenin`, `inputln` (terminal only), `loadpoolstrings`,
`makepdftexbanner` (with `maketexstring`), `dateandtime`, `secondsandmicros`, `initstarttime`,
`fflush`, `pdfinitmapfile`, `synctexinitcommand`, `synctexterminate`, `getjobname`,
`recorderchangefilename`, `stringcast`, `aopenout`, `aclose`, `libcfree`, `ISDIRSEP`, `uexit`.
Everything else is Stuck: 166 of 189 externals are Stuck.

**The environment is an explicit input** (checkpoint 3, review A finding 1; C-107). Checkpoint 2's
`secondsandmicros` was a stub returning `SOURCE_DATE_EPOCH` seconds and 0 microseconds. The real
`get_seconds_and_micros` (texmfmp.c) calls `gettimeofday`, which `FORCE_SOURCE_DATE` does not
affect, and `mainbody` seeds `randomseed := microseconds*1000 + epochseconds mod 1000000` from it
(pdftex.p:13123). So `\pdfrandomseed` gave 76260 in the model and 738174428, 749069517,
325234522 in three runs of the binary, and `\pdfuniformdeviate`, `\pdfnormaldeviate` and
everything after `\pdfresettimer` likewise gave outputs the binary never gives — and the model
did not report Stuck. That was the instance; the class is every modelled external that reads
something that is not the program's own state. `Boundary.v`'s header audits all 23 and gives
each such input one of two dispositions: an explicit input that is part of the run's identity
(the driver's SPEC: the command line, the environment as `getenv` sees it, kpathsea's values,
the `gettimeofday` readings in call order, the standard input, `charsigned`), or Stuck (the real
clock through `time(NULL)`, `localtime` and the time zone, a command line other than the one C
main was measured with, a file name other than one new component in an empty working
directory). None is now fixed to a value the real function would not produce. C's parsing of
environment strings is modelled, not done by the driver (review A finding 4): `STREQ (s, "1")`
for `FORCE_SOURCE_DATE` (so `01` is not `1`), glibc's `strtoull` with its `*endptr` / `errno`
test for `SOURCE_DATE_EPOCH` (an invalid value is the binary's `FATAL`, Stuck), glibc's `atoi`
(= `(int) strtol`) for kpathsea's values; `getenv` and `kpse_var_value` are separate inputs
(kpathsea reads the environment first, then texmf.cnf, then expands). `topenin` now writes
`last := first`, as texmfmp.c does when the command line has no arguments (review A finding 2).

What TeX Live's C `main` writes before `mainbody` is **measured**, not modelled: the unstripped
reference build under gdb, stopped at `mainbody` for this command line and environment
(`evidence/cmain/`): 9 globals are non-zero (`iniversion`, `parsefirstlinep`,
`interactionoption`, `formatdefaultlength`, `TEXformatdefault`, `shellenabledp`,
`restrictedshell`, `synctexoption`, `versionstring`) plus `dumpname`. That measurement holds for
the command line `pdftex -ini` and an environment that sets no kpathsea variable; the boundary
model is Stuck on any other command line.

## Checkpoint 3: review round 1 (2026-10-01)

Two independent adversarial reviews reproduced the pass criterion and both returned FIX. Every
finding was reproduced first, then closed.

### Review A (fidelity): the differential, committed and rerunnable

Review A ran 153 INITEX inputs through the model and the pinned binary (116 byte-identical, 33
Stuck, 4 divergent: the four `\pdfrandomseed`/deviate documents of finding 1). Its harness is now
committed as [`h2/diff/`](h2/diff/README.md), H.4's seed: 178 inputs (the review's inputs, its
two random-document generators with their seeds, the INITEX run, and 21 regression inputs for the
clock, the environment parsing and kpathsea's `atoi`), `diff.py` (the model side and the
comparison), the clock shim, and the per-input results `results-arm64.tsv` and
`results-amd64.tsv`. A row is IDENTICAL when the model exits with the binary's status and its
terminal output, standard error, every file it wrote and the number of clock readings it used are
byte-identical to the binary's; STUCK when the model is Stuck; DIVERGENT otherwise. Results, run
by the measured `ps.exe` (`991ae9a5…`):

- arm64: 178 inputs, 134 identical, 43 Stuck, 1 without a result, 0 divergent (the aarch64 configuration against the native arm64 binary);
- amd64: 178 inputs, 134 identical, 43 Stuck, 1 without a result, 0 divergent (the x86_64 configuration against the amd64 binary under qemu).

The same inputs fall in the same class on both. Of review A's 154 inputs (its 153 and the INITEX
run), 121 are now identical (116 before: the four `\pdfrandomseed`/deviate documents and
`\pdfelapsedtime`'s, which was Stuck by accident, are now exact), 32 Stuck, and one without a
result: `\romannumeral 2147483647` (`romn`) prints 2,147,483 letters and the model did not finish
in 900 s (review A's run had no result either). The 43 Stuck runs stop at an unmodelled external
(34: fonts, file input, shipout, `\pdf...` primitives, the real clock, the failure paths of the
environment), signed overflow (4), a conversion (3: `tv_sec` beyond 2038, a negative
`SOURCE_DATE_EPOCH`, a kpathsea value outside `int`), and a write to a non-file (2: `t205`,
`t208`, where `finiteshrink` prints to a log that is not open; the arm64 binary dies there with
SIGSEGV, rc 139, and the amd64 binary under qemu did not finish in 15 minutes and was killed, rc
137). One amd64 binary run (`xsct1`) first ended with rc 139 and no output; rerun three times it
gave rc 1 and output identical to the model's; it is recorded as a transient failure of the
emulation (review B saw one too, `jpgbig`), and the committed row is the rerun's. The 21
regressions behave as their C source says: `FORCE_SOURCE_DATE` = `01`, empty or unset and an
unset `SOURCE_DATE_EPOCH` are Stuck (the real clock); `SOURCE_DATE_EPOCH` = empty, ` 1788076260`,
`+1788076260`, `0000000000` and 2⁵⁵ are identical (strtoull), `1788076260x` and 20 nines are Stuck
(the binary's FATAL, rc 1), `-1` is Stuck (unsigned to `time_t`); `atoi` of `70abc` and `  20` is
identical, of `-5` and `99999999999` Stuck; the clock regressions are identical except a clock
with too few readings (the binary's shim exits 97, the model is Stuck) and `tv_sec` = 2³¹ (Stuck).
The model's wall time per input is in each run's `run.json` under `~/.cache/lp-spike-h1/h2/diff/`
(not a speed measurement: four runs in parallel on a shared machine).

| finding | reproduced | resolution |
|---|---|---|
| **HIGH 1** the clock stub | yes: `\message{\the\pdfrandomseed}` gives 76260 in the checkpoint-2 model, 123532260 in the binary with the shim's reading | the class audit above; the clock is the input `io_clock`; the review's four inputs and the 21 new clock, environment and `atoi` regressions are IDENTICAL or STUCK on both configurations, as their C source says; `\pdfelapsedtime` is computed (it was Stuck only through the double-to-int store rule, now C's) |
| LOW 2 `topenin` does not write `last` | yes (texmfmp.c) | `last := first` |
| LOW 3 no `- (integer)` cast | yes (web2c-parser.y; 4 `longinteger` sites) | translator rule 4 |
| LOW 4 the driver's `int_of_string` | yes: `FORCE_SOURCE_DATE=01` was 1 | the driver passes bytes; C's parsing in `Boundary.v`; separate `getenv` and kpathsea inputs |
| LOW 5 stale IR-node count | yes (183,086 vs 185,084) | the manifest's number, checked by `verify_h2.py` |

### Review B (claims and trust)

**MEDIUM-1: `verify_h2.py` compared stored files with stored files.** Reproduced: a mutation of
the translator, the manifest, `Interp.v`, the C-main values, or of all outputs together left it OK.
Now:
- `pipeline.sh` writes `provenance.json` (sha256 of every input, every committed source, every
  generated Coq file, every extracted OCaml file, and `ps.exe`) and `measure.tsv`; both are
  committed in `evidence/build/`;
- every committed model output names the `ps.exe` it came from (`h2/evidence/inirun/run.json`, the
  `ps_exe_sha256_16` column of `diff/results-*.tsv`);
- **pure mode says what it is:** "pure (consistency of the committed evidence; nothing re-run)".
  It fails when a committed source no longer hashes as the measured build's (the evidence is
  then STALE), when an output was not made by the measured `ps.exe`, or when a recorded hash does
  not match;
- `--reproduce translate` re-runs `emit_coq.py` and `gen_cmain.py` on the pinned inputs and
  compares every generated file with `provenance.json`; `--reproduce model` re-runs the measured
  `ps.exe` on the INITEX run in both configurations and compares every output byte;
- the binary side cannot be re-run by a committed executable: this repository's
  `check_oracle_pin.py` allows a TeX engine to be started only inside `_oracle.py`, and
  `_oracle.py` has no terminal input, no architecture choice and no clock shim. The reference
  runs are therefore committed as an exact recipe, quoted with its sha256, in
  [`h2/diff/README.md`](h2/diff/README.md), as H.1 did (`h1/recipes.md`). An oracle entry point
  for measurement runs is an owner decision (below).

Mutation tests (each applied to a copy of `h2/` and the report, `verify_h2.py` run in the mode shown, the copy discarded; the harness is not committed, its table is):

| mutation | mode | result |
|---|---|---|
| none | pure / `--reproduce translate` / `--reproduce model` | OK / OK / OK |
| translator: unary minus without its cast (`lower.py`) | pure | **FAIL** (stale source) |
| the same | `--reproduce translate` | **FAIL** (6 generated files differ) |
| `manifest.json`: `ir_nodes` + 1 | pure | **FAIL** |
| `Interp.v`: negation never overflows | pure | **FAIL** (stale source) |
| a C-main value (`interactionoption`) | pure | **FAIL** |
| every INITEX output edited consistently, `run.json` hashes updated | pure | OK: **pure mode cannot see consistent forgery** |
| the same | `--reproduce model` | **FAIL** |
| translator edit with `provenance.json` forged to match | pure | OK: **cannot see it** |
| the same | `--reproduce translate` | **FAIL** |
| a results row reclassified DIVERGENT | pure | **FAIL** |
| a results row's `ps.exe` hash changed | pure | **FAIL** |
| the report says "24 of the 189 externals" | pure | **FAIL** |
| a different `ps.exe` given to `--reproduce model` | `--reproduce model` | **FAIL** |

A forgery of the binary's outputs together with the model's is caught only by re-running the
binary (the recipe).

**MEDIUM-2 (H.1 step A, C-106): DIVERGES was still hand-attributed.** Closed with evidence, not
rewording: every probe and control of H.1's DIVERGES rows was run under gdb on the unstripped
reference builds of both architectures (aarch64 natively; x86_64 through qemu-user's gdbstub),
with a breakpoint on every division and conversion instruction of the 18 candidate sites and the
operands recorded at each hit ([`h1/archsem/reach_trace/`](h1/archsem/reach_trace/RUN.md)).
`classify.py` now requires, for DIVERGES, that the probe executes the site's own instruction with
the diverging operand on every architecture where the site has an instruction, and
`verify_h1.py` re-derives that from the committed trace (moving `snapy0` to another site now
FAILS it, mutations M1–M5 in `RUN.md`). Reaching alone is not evidence: the controls reach the
same sites. The trace refuted 3 of round 3's 18 attributions: `pdftex0.c:1365` and
`writejpg.c:222` are never executed by their probe, and `writejpg.c:237` is executed only with an
in-range source. **DIVERGES is now 15** (8 translated, 7 boundary), PS-STUCK 77, OPEN 220
(C-110). For the five value-divergence probes the trace shows the diverging operand at the site;
that this value causes the recorded difference is [I]. Six sites have an instruction on one
architecture only and are evidenced there only. Also fixed: `reach.out` is now `reach.py`'s
literal output, the `rel/` paths in the README, and `reach.py`'s usage text.

**MEDIUM-3: the trusted base.** Enumerated below.

**LOW-1, LOW-2, LOW-3:** the measurement corrections, the speed label and the configurations,
above.

## Re-measured on H.3's model (H.3 checkpoint 2, 2026-10-05) [M]

H.3 changed the model (`h3/model.patch`: the format-file externals, the evaluation-order
refinement, the memory fixes, the driver's diagnostics). At H.3 checkpoint 2 that patch is
merged into this directory, so the committed evidence of this report is re-measured on the new
build and `verify_h2.py` now checks THAT build (`h2/evidence/build/provenance.json`, `ps.exe`
`e41941bf…`, the same bytes as H.3 checkpoint 1's memory-fixed build). The numbers above are
H.2's build; the current ones:
- the translation: 603 of 603 procedures, 185,086 IR nodes (unchanged), 188 distinct externals
  (`TEXMFENGINENAME` is now web2c's string literal, not an external); 45,756 unsequenced pairs
  checked, 25 of them Stuck (H.2: 45,742 and 29);
- the boundary: 43 of the 188 externals are modelled, so 145 of 188 externals are Stuck;
- the build (load 6.6–7.8, `pipeline.sh` now also runs on Linux): coqc: 25 file(s), 14 s wall,
  peak 537 MB; extraction: 1 file(s), 2 s wall, peak 638 MB; ocamlopt: 93 file(s), 22 s wall,
  peak 545 MB;
- the INITEX run (`h2/evidence/inirun/`): the model's terminal output, standard error and
  `texput.log` are byte-identical to H.2's in both configurations, so to the binary's; only the
  driver's `TIME:` line changed;
- the differential (`diff/results-*.tsv`, the binary side unchanged, so not re-run): the same
  totals in both configurations, and no row that was IDENTICAL changed. Two rows changed:
  `dump1` (an INITEX `\dump`) stays STUCK, but its reason moved from the then unmodelled
  `wopenout` to "read of an uninitialised value" inside `storefmtfile` (`wopenout` is modelled
  now; that the read is of memory-word halves INITEX never wrote, which C's `malloc` leaves
  unspecified, is inferred [I], not located); `romn` stays without a result, but now because the
  run was capped at 5,000 MB (`diff.py model --cap-mb`, new), where H.2's run hit the 900 s
  time-out (a re-run of `romn` alone under a 12,000 MB cap was killed by the cap too, after 325 s: its memory, not its time, is the limit now; an H.5 matter). Totals: arm64: 178 inputs, 134 identical, 43 Stuck, 1 without a result, 0
  divergent; amd64 the same. The amd64 binary side is still the qemu run (C-113 on PR #630:
  `t205`, `t208`).

## The trusted base of H.2's claim

The claim is: on a run whose identity (SPEC, standard input) lies in the environment class, the
extracted `ps.exe` produces the binary's terminal output, standard error, files and exit status,
or reports Stuck. It rests on, mapped to the ADR-014 draft's TB rows:

| what | TB row | what checks it today |
|---|---|---|
| the Coq kernel (it accepts the term; nothing is proved about `PS` yet) | TB-1 | Coq 8.18.0 |
| **extraction and its realizers**: `ExtrOcamlNatInt` (fuel as an OCaml `int`), `ExtrOcamlZBigInt` (Z as zarith), `ExtrOCamlInt63`, `ExtrOCamlFloats` (PrimFloat as OCaml floats), the `PArray` directives in `Extract.v` (`Parray` of coq-core's kernel), `ExtrOcamlString`, `ExtrOcamlBasic` | TB-1 | nothing beyond their use in Coq's own kernel; the differential below |
| ~~the textual `sed` patch of the extracted OCaml~~ **removed** at checkpoint 3: Coq 8.18's `ExtrOCamlPArray` printed a nested array type as `cell 'a Parray.t 'a Parray.t`; `Extract.v` now states the same realizers without its `Extraction Inline`, and the extracted code compiles as Coq wrote it | — | the build |
| the OCaml compiler and runtime (OCaml 5.2.0, zarith), and the driver `driver.ml` (reads SPEC and standard input into the initial `io` with no parsing of values, writes the output handles; catches stack overflow and out-of-memory as "no verdict") | TB-1 | review |
| the source pin: r78081's tangled `pdftex.p`, the four `.defines`, `pdftexcoerce.h`, `pdftex.pool` | TB-2 | H.1 (the rebuild reproduces the pinned binaries); `provenance.json` hashes |
| the Python translator (`lexer.py`, `parser.py`, `lower.py`, `emit_coq.py`, `gotos.py`, `evalorder.py`, `cprec.py`) and its rules (above), each taken from web2c's source | TB-3 | review; the differential; not yet translation validation (re-emitting C) |
| `PS`: `Values.v`, `Interp.v` | TB-4 | review; the differential |
| the C boundary: the 23 externals of `Boundary.v`, each from its C source, with the environment audit | TB-5 | review; the differential; the H.1 C-boundary work list applies to each |
| C main: `gen_cmain.py` and the one gdb measurement of `pdftex -ini` at `mainbody` (`evidence/cmain/`) | TB-5 | one command line, one environment class |
| the environment class (an empty writable working directory, no signals, the clock and environment as given) and the nondeterminism inventory of the audit | TB-8 | the audit in `Boundary.v`; the clock and environment regressions of `diff/` |
| fuel's meaning (derivation height, not steps) | TB-9 | — (the draft's TB-9 wants a step budget calibrated against the binary; not done) |

## Open (none of it is in H.2's criteria; all of it is in the tier's)

- **The C boundary.** 166 of 189 externals are Stuck. H.3 needs the format-file externals; H.4
  needs file input, kpathsea lookups, fonts, `\write`. The C-boundary work list from H.1 (the 227
  boundary division and conversion sites, 220 OPEN and 7 DIVERGES, and the 649 boundary functions
  that change under `-fwrapv` or `-fsigned-char`) applies to each external as it is modelled.
- **C main** is a measurement for one command line; a model of `maininit`/`parse_options` is open.
- **Claims about the binary not yet checked in its disassembly:** the 13 pointer-arithmetic sites
  are plain address arithmetic; the 29 order-dependent sites (which gcc order was chosen).
- **Contraction** as an aarch64 parameter of PS (the fused sites of H.1 §5.1).
- **Native amd64**: approved by the owner on 2026-09-30, not run (it needs a CI workflow the owner
  has not yet permitted). Every amd64 comparison here is emulated.
- **Speed**: H.5 (measured on a quiet machine during H.3).
- **Attestation beyond these inputs**: H.4 and H.6.

## Owner decisions this checkpoint needs

- **An oracle entry point for measurement runs.** The differential's binary side (terminal input,
  a chosen architecture, the `gettimeofday` shim) cannot go through `_oracle.py`, so it is a
  committed recipe, not an executable; H.4 and H.6 will need the same at scale. Either
  `_oracle.py` grows such an entry point (ADR-012 decision 7 governs the oracle), or spike
  instruments stay recipes.
