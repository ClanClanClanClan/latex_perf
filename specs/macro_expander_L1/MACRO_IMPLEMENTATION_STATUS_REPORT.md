# L1 Macro Implementation Status Report

**Last Audited**: 2026-02-22 (verified against running code)
**Total Production Macros**: 520 (441 symbols + 79 argsafe)
**Implementation Status**: Complete for L1 scope

## Current Production State

### What IS Implemented (verified `dune runtest`, 192 test cases passing)

#### Macro Catalogue (`src/macro_catalogue.ml`, 487 lines)
- **441 symbol macros** (v25r2 format + 58 expansions beyond original 383)
- **79 argsafe macros** (62 base + 17 added in Phase 5d / PR #158)
- **Full type system**: `TText`, `TOp`, `TDelim` token types
- **Mode-aware expansion**: Math / Text / Any / Both contexts
- **Epsilon-safe templates**: Inline string substitution + Builtin handlers
- **Multi-argument support**: Positional args with `$1`, `$2` placeholders
- **Hash-table lookup**: O(1) per macro name

#### Argsafe Categories (79 macros)
- Text formatting (10): `\textbf`, `\textit`, `\texttt`, `\textsf`, `\textsc`, etc.
- Math formatting (6): `\mathrm`, `\mathbf`, `\mathit`, `\mathsf`, `\mathtt`, `\mathnormal`
- Special builtins (7): `\emph`, `\mbox`, `\verb`, `\verb*`, `\textsuperscript`, `\textsubscript`, `\ensuremath`
- Math operators with args (17, Phase 5d): `\frac`, `\binom`, `\overset`, `\underset`, `\stackrel`, `\sqrt`, `\overline`, `\underline`, `\hat`, `\bar`, `\tilde`, `\vec`, `\dot`, `\ddot`, `\widehat`, `\widetilde`, `\overrightarrow`
- Additional argsafe macros (39): Various text/math formatting extensions

#### Integration Points
- `rest_simple_expander.ml`: Expands macros before L1 validation
- `rest_api_server.ml`: REST endpoint exposes expansion
- Golden test corpus: 236 cases test full pipeline (raw + expanded)
- Macro catalogue tests: 192 dedicated test cases

### What Is NOT in L1 Scope (by design)

These are L2+ features and are intentionally excluded from the L1 macro catalogue:

1. **Document structure**: `\section`, `\chapter`, `\usepackage` — requires L2 AST
2. **Cross-references**: `\ref`, `\label`, `\cite` — requires document-wide state
3. **Environments**: `\begin`/`\end` — requires stateful tracking
4. **Math with limits**: `\sum_{i=1}^{n}`, `\int_{a}^{b}` — limit syntax is L2 parsing
5. **Spacing/breaks**: `\\`, `\hspace`, `\vspace` — layout-level, not expansion
6. **Counters**: `\setcounter`, `\stepcounter` — mutable state
7. **Conditionals**: `\if...\fi` — Turing-complete, out of scope for L1

## Testing Coverage (verified 2026-02-22)

- **192 macro catalogue tests** (`test_macro_catalogue.ml`) — all passing
- **76 L1 integration tests** (`test_validators_l1.ml`) — all passing
- **236 golden corpus tests** — full pipeline with expansion
- Symbol expansion, argumentful expansion, epsilon safety, mode awareness all tested

## Performance

Measured locally 2026-02-22:
- **A+B p95 (1.1MB)**: 3.25 ms (target ≤ 20 ms) — includes macro expansion
- **Hash-table lookup**: O(1) per macro, negligible overhead
- **520 macros loaded**: No measurable impact on startup

## History

- Phase 5d / PR #158: Added multi-arg support + 17 argsafe macros
- Original v25r2: 383 symbol macros
- Expanded to 441 symbols via additional Unicode coverage
- Argsafe grew from 23 → 62 → 79 (base + Phase 5d additions)
