# Spike H.2: the translator from the tangled pdfTeX into a Coq program

Step H.2 of the foundation spike ([ADR-015](../../adr/ADR-015-static-proven-tier-on-translated-engine.md),
ADR-014 draft §9, ledger OPEN-123). Progress and measurements are in
[`../H2-report.md`](../H2-report.md). This directory holds the code; generated Coq and builds
live in `~/.cache/lp-spike-h1/h2/` (not committed: they are regenerated from the pinned source).

**Criteria (ADR-014 draft §9, verbatim).** Pass: "100 % of procedures translated; Coq accepts
the term; the extracted binary runs INITEX to the `*` prompt". Kill: "the Coq term or its
extraction is intractable (> 2 h compile or > 16 GB)".

| path | what it is |
|---|---|
| `translate/lexer.py` | web2c-lexer.l's rules that change meaning: `ifdef`/`endif` evaluated against the pinned build's configuration (STAT, INITEX, IPC defined; TEXMF_DEBUG not), `packed ` as whitespace, `-` folded into a negative literal after a non-operand, `forward` declarations dropped |
| `translate/parser.py` | web2c-parser.y's grammar; expressions grouped by **C's** precedences, because the binary is what the C compiler made of web2c's in-order token output (`cprec.py` lists the 8 places where the Pascal grouping differs) |
| `translate/lower.py` | name resolution, C typing (web2c's subrange-to-C-type rule, the `L` suffix on literals > 32767, the usual arithmetic conversions), storage layout (texmfmem.h's little-endian union words), web2c's TeX-mode `goto 10` = `return`, fixwrites.c's `%c`/`%s`/`%ld` classification of write items |
| `translate/emit_coq.py` | writes the IR as Coq terms over `coq/Syntax.v`: one `Definition` per procedure, 40 per file, plus global shapes, string literals and name tables |
| `translate/gotos.py` | every goto resolved statically (a label in an enclosing list, or inside one of its elements, never through a `for` body) |
| `translate/evalorder.py` | C's unspecified evaluation order: effect summaries per procedure and per modelled external; every unsequenced pair checked; a conflicting site is emitted as `EUnseq`/`SUnseq` (Stuck) |
| `translate/cprec.py` | the places where C's and Pascal's grouping of an expression differ (the IR follows C) |
| `translate/gen_cmain.py` | `CMain.v` from the gdb measurement of what TeX Live's C main wrote before `mainbody` (`evidence/cmain/`) |
| `coq/Syntax.v` | the IR's Coq syntax |
| `coq/Values.v` | cells, values, the chunked heap, C's conversions, IEEE-754 bit patterns, integer arithmetic with Stuck on undefined behaviour |
| `coq/Interp.v` | `PS`: the fuelled big-step interpreter (gotos by continuation, web2c's `for`, C's `switch`, calls with frames) |
| `coq/Boundary.v` | the C-boundary model: each modelled external with the C function it follows; everything else Stuck |
| `coq/Main.v`, `coq/Extract.v`, `coq/driver.ml` | initial state (C static storage + C main's writes), extraction to OCaml, the command-line driver |
| `pipeline.sh`, `relink.sh` | translate, compile every Coq file under `/usr/bin/time -l`, extract, compile OCaml incrementally, link `ps.exe` |
| `coq/build.sh` | checkpoint 1's syntax-only build |
| `evidence/` | `manifest.json` (the translation's counts), `cmain/` (the gdb measurement), `inirun/` (the model's and the binary's INITEX outputs); `verify_h2.py` re-checks them |

Inputs: `Work/texk/web2c/pdftex.p` (tangle's output, identical in the aarch64 and x86_64 build
trees, sha256 `d1a7d257…`) and the four `.defines` files web2c's `convert` prepends
(`common`, `texmf`, `synctex`, `pdftex`), all from the H.1 rebuild of r78081.

Inputs besides these: `pdftexcoerce.h` (web2c's own output: which procedures copy `zmem`/`zeqtb`
into the register locals `mem`/`eqtb`) and `pdftex.pool` (the pool strings `loadpoolstrings`
copies). Build and run (writes only under `~/.cache/lp-spike-h1/h2/`):

```sh
./pipeline.sh            # translate, Coq, extract, OCaml -> ~/.cache/lp-spike-h1/h2/run/build/ps.exe
cd ~/.cache/lp-spike-h1/h2/run/build
PS_DUMPDIR=dump PS_PROCNAMES=../procnames.txt ./ps.exe 4000000000 <path to evidence/inirun/env.txt> '\relax'
```

The C main measurement (`evidence/cmain/`) was taken with `dump.py`/`dump2.py` under gdb, in a
container of the pinned image with gdb added (`lp-spike-gdb:arm64` = the pinned image plus
Debian's `gdb` and `binutils`; only for measurement), running the unstripped reference build
(sha256 `b23c26d6…`, whose stripped form is the pinned binary) mounted at
`/usr/local/texlive/2026/bin/ref` as `pdftex -ini`, `SOURCE_DATE_EPOCH=1788076260
FORCE_SOURCE_DATE=1`, stopped at `mainbody`.
