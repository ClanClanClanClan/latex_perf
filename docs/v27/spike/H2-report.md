# Foundation spike, step H.2: the translator and the Coq program (in progress)

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
   operators, C below. The two readings differ at **8** places; e.g. `fixpdfdraftmode`'s
   `fixedpdfdraftmodeset and fixedpdfdraftmode>0` is `(set and mode) > 0` in Pascal and
   `set && (mode > 0)` in the binary. The IR follows the binary (`translate/cprec.py`).
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
   body (`translate/gotos.py`, run on every translation, for the other 552 gotos); PS resumes
   inside the element by continuation.
7. **Writes** (`fixwrites.c`): each item is `%c`, `%s` or `%ld` by its first token; widths are
   dropped.

### Open items recorded at checkpoint 1

- **C's unspecified evaluation order.** C leaves the order of an operator's operands, a call's
  arguments and an assignment's two sides unspecified; PS evaluates left to right. 19 expressions
  have two or more calls in such positions, and 1,369 assignments have a call on the right. Each
  must be shown order-independent by an effect analysis (what each call may write against what
  the other side reads), or evaluated both ways with disagreement Stuck. Not yet done.
- The semantics (`PS`), the C-boundary stubs INITEX needs, extraction, and the INITEX run.
