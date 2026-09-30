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
| 1 | 2026-09-30 | translator front end complete; the whole program emitted as a Coq term and accepted | procedures 603/603 translated [M]; Coq accepts the term: 44 s, peak 456 MB [M]; kill criterion not approached |
| 2 | 2026-09-30 | `PS` as a fuelled interpreter in Coq, the C boundary INITEX needs, extraction, the INITEX run | **pass criterion met** [M]: 603/603; Coq accepts the term and the semantics (26 files, 257 s, peak 586 MB); extraction 33 s, 586 MB; OCaml 225 s, peak 543 MB per module; the extracted program runs `pdftex -ini` through the `*` prompt to the end, its terminal output, `texput.log` and exit status byte-identical to the pinned binary's on both architectures. Kill criterion not approached |

**Verdict at checkpoint 2: H.2's pass criterion is met and its kill criterion did not fire.** The
whole of the tangled pdfTeX is a Coq program; Coq accepts it with its semantics in minutes and
under 0.6 GB; the extracted program runs INITEX exactly as the binary does on the one run the
criterion names. What the criterion does not ask, and this checkpoint does not show, is listed
under "open" below: in particular, the model is exact only where the C boundary is modelled (23 of
189 externals), and it is about 200 times slower than pdfTeX (H.5's question).

## Checkpoint 1: every procedure translated; Coq accepts the term [M]

- **Input.** `pdftex.p` of r78081 (tangle output; byte-identical in the aarch64 and x86_64 build
  trees; sha256 `d1a7d257…5910`) with web2c's four `.defines` files: 247,399 tokens, 603 procedures
  and functions (the ADR-014 draft guessed ≈ 1,400 [I]; TeX Live's program has no main block, its
  main program is the procedure `mainbody`), 690 globals, 63 constants, 35 types.
- **Translated: 603 of 603 procedures** (0 failures), 183,086 IR nodes, 189 distinct externals
  (C functions and macros the program calls: the C boundary as the program sees it), 101 string
  literals.
- **Coq accepts the term.** `coqc` 8.18.0 on the 19 files (Syntax, globals, 16 files of 40
  procedures, the procedure table): **44 s wall in total, peak resident set 456 MB** for one file
  (M-series Mac, one core, `/usr/bin/time -l`). The kill criterion is 2 h or 16 GB.
- This measures the *syntax* term only. The semantics (`PS` as a fuelled interpreter), its
  extraction and the INITEX run are the next checkpoints; the kill criterion applies to them too.

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
4. **Union words** (`texmfmem.h`, little-endian): `hh.rh` and `cint` share bytes 4–7, `hh.b0` is a
   `short` at bytes 2–3, `qqqq.b0` the byte at 7, `gr` all 8 bytes.
5. **`goto 10` is `return`** in TeX mode except in `macrocall`, `hpack`, `vpackage`, `trybreak`
   (web2c-parser.y `doreturn`): 195 of the 747 gotos, in 102 procedures, are returns.
6. **Gotos into structured statements.** Two gotos jump into a sibling `case` arm
   (`prunepagetop`'s `goto 60`, `getnext`'s `goto 40`), which C allows. Every goto resolves to a
   label in an enclosing statement list or inside one of its elements, never through a `for`
   body (`h2/translate/gotos.py`, run on every translation, for the other 552 gotos); PS resumes
   inside the element by continuation.
7. **Writes** (`fixwrites.c`): each item is `%c`, `%s` or `%ld` by its first token; widths are
   dropped.

### Open items recorded at checkpoint 1 (both closed at checkpoint 2)

- C's unspecified evaluation order: now checked site by site (checkpoint 2, item 4).
- The semantics, the boundary INITEX needs, extraction and the INITEX run: checkpoint 2.

## Checkpoint 2: `PS`, the boundary, extraction, and INITEX to the `*` prompt [M]

**The run.** `pdftex -ini` in the pinned image (both architectures), terminal input `\relax` then
end of file, `SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`, the image's texmf.cnf values:

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

exit status 1. The extracted model, given the same terminal input and texmf.cnf values, writes
**the same terminal bytes, the same `texput.log` bytes, and exits 1** (`h2/evidence/inirun/`,
re-checked by `python3 docs/v27/spike/h2/verify_h2.py`; the two architectures' binaries agree with
each other too). On the way it runs `mainbody`, `initialize`, `initprim` (every primitive
installed through the translated `primitive`), `loadpoolstrings` (1,849 pool strings through the
translated `makestring`), reads the first line at `**`, runs `maincontrol`, opens the log, prompts
`*`, meets end of file, and runs `fatalerror`, `jumpout` and `closefilesandterminate`.

**Measured cost** (M-series Mac under a load average of 57-114 from other work, so wall times are
upper bounds; `/usr/bin/time -l`; a from-scratch `pipeline.sh` in an empty directory):

| stage | time | peak memory |
|---|---|---|
| translation (`emit_coq.py`) | ≈ 5 s | — |
| `coqc`, 26 files (syntax, semantics, 16 procedure files, globals, pool, boundary, C main, main) | 257 s total, largest file 13 s | 586 MB |
| extraction (`Separate Extraction`) | 33 s | 586 MB |
| `ocamlopt`, 95 modules (7.1 MB of OCaml) | 225 s | 543 MB (one module) |
| the INITEX run | 49.8 s wall, 29.0 s user | 1.18 GB |

The kill criterion is > 2 h or > 16 GB. Two measurements on the way matter for H.5 and later
steps: extracting everything into one OCaml file made `ocamlopt` take 276 s and **4.9 GB**; Z
literals extracted as big-integer arithmetic made the file 39 MB (AST numbers are now primitive
63-bit integers, 7 MB). pdfTeX itself does this run in 0.16-0.29 s in the container, so the model
is roughly 150-300 times slower here, unoptimised (Z arithmetic via zarith, a chunked persistent
heap, fuel on every node). H.5's kill line is > 200× with no profile-guided fix in sight; that
is H.5's question, not H.2's, and it is flagged here so it is not a surprise.

### What `PS` is (coq/Values.v, coq/Interp.v)

A deep embedding with a big-step, fuelled interpreter; fuel decreases at every node, so every run
ends in a result, an exit status, or **Stuck** (outside the tier). Values are C's: integers with
their C type (after web2c's typing), doubles as Coq primitive floats (IEEE binary64,
round-to-nearest, unfused), pointers as (block, offset), union words as bytes with a
defined-byte mask. Stuck, per the proposed rule (H.1 §5.4, **still pending the owner**): signed
overflow in `int` or `long`, division or remainder by zero, `INT_MIN / -1`, a conversion out of
range (C's implementation-defined or undefined conversions), a read of a never-written scalar,
an out-of-bounds access, use after `free`, a NaN's bit pattern (its sign and payload are the
architecture's), an unmodelled external, fuel exhausted. Plain `char` loads are a parameter
(`io_char_signed`; the run above uses aarch64's unsigned). Contraction (FMA) is not modelled: PS
is unfused, which is x86_64's code; aarch64's fused sites (H.1 §5.1) are a parameter still to add.

### What the translator had to decide that checkpoint 1 had not [R]

1. **`mem` and `eqtb` are locals.** web2c's `pdftexcoerce.h` gives every procedure that uses them
   `register memoryword *mem=zmem, *eqtb=zeqtb;`: a copy taken on entry. A procedure that
   reallocates `zmem` does not change its callers' `mem`. The translator reads the header and
   gives each such procedure the two locals and their initialisation.
2. **The integer constant 0 assigned to a pointer is NULL** (C's null pointer constant):
   `pdffontmap[fontk] := 0`. Every other assignment or argument whose C type does not match is a
   translation error.
3. **Pointer arithmetic outside an object.** `hash := yhash - hashoffset` forms a pointer before
   the start of its array on every run, which ISO C makes undefined. PS follows the binary: plain
   address arithmetic, bounds checked at every access. That gcc compiled each of the 13
   pointer-arithmetic sites as plain address arithmetic is a claim about the binary, open below.
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
   which order gcc chose at each, is open (checkpoint 2 first stated one as a real use after free;
   that was not checked and is withdrawn).

### The C boundary modelled so far (coq/Boundary.v)

23 of the 189 externals the program names, each with the C function it follows: the three
standard streams, `setupboundvariable`, `topenin`, `inputln` (terminal only), `loadpoolstrings`,
`makepdftexbanner` (with `maketexstring`), `dateandtime` (with `FORCE_SOURCE_DATE=1` only; the
real clock is O-5), `secondsandmicros` (**a spike stub**: the fixed epoch, as the draft allows
for H.2), `initstarttime`, `fflush`, `pdfinitmapfile`, `synctexinitcommand`,
`synctexterminate`, `getjobname`, `recorderchangefilename`, `stringcast`, `aopenout`, `aclose`,
`libcfree`, `ISDIRSEP`, `uexit`. Everything else is Stuck. What TeX Live's C `main` writes before
`mainbody` is **measured**, not modelled: the unstripped reference build under gdb, stopped at
`mainbody` for this command line and environment (`evidence/cmain/`): 9 globals are non-zero
(`iniversion`, `parsefirstlinep`, `interactionoption`, `formatdefaultlength`,
`TEXformatdefault`, `shellenabledp`, `restrictedshell`, `synctexoption`, `versionstring`) plus
`dumpname`. That measurement holds for this command line only.

### Open after checkpoint 2 (none of it is in H.2's criteria; all of it is in the tier's)

- **The C boundary.** 166 of 189 externals are Stuck. H.3 needs the format-file externals
  (`undumpthings` and friends, gzip); H.4 needs file input, kpathsea lookups, fonts, `\write`.
  The C-boundary work list from H.1 (227 division/conversion sites, 649 overflow- or
  char-sensitive functions) applies to each external as it is modelled.
- **C main** is a measurement for one command line; a model of `maininit`/`parse_options` is open.
- **Claims about the binary not yet checked in its disassembly:** the 13 pointer-arithmetic sites
  are plain address arithmetic; the 29 order-dependent sites (which gcc order was chosen).
- **Contraction** as an aarch64 parameter of PS (the fused sites of H.1 §5.1).
- **The PS rule itself** is the owner's pending decision (H.1 report §8); H.2 implements the
  proposal, and changing it touches `Values.v`'s arithmetic and conversions only.
- **Speed**: ≈ 200× on this run (H.5).
- **Attestation beyond one run**: the INITEX run is one execution; H.4 and H.6 are where PS is
  tested against the binary at scale.
