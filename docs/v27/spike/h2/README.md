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
| `coq/Syntax.v` | the IR's Coq syntax |
| `coq/build.sh` | compiles the generated files one by one under `/usr/bin/time -l` (wall time, peak RSS) |

Inputs: `Work/texk/web2c/pdftex.p` (tangle's output, identical in the aarch64 and x86_64 build
trees, sha256 `d1a7d257…`) and the four `.defines` files web2c's `convert` prepends
(`common`, `texmf`, `synctex`, `pdftex`), all from the H.1 rebuild of r78081.

Regenerate (from this directory):

```sh
W=~/.cache/lp-spike-h1/b-arm64/repo/texk/web2c
python3 translate/emit_coq.py ~/.cache/lp-spike-h1/b-arm64/repo/Work/texk/web2c/pdftex.p \
  $W/web2c/common.defines $W/web2c/texmf.defines $W/synctexdir/synctex.defines \
  $W/pdftexdir/pdftex.defines --out ~/.cache/lp-spike-h1/h2/gen
```
