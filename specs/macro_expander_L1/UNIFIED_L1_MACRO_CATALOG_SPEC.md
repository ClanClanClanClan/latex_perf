# Unified L1 Macro Catalog Specification

**Created**: 2025-08-12
**Last Audited**: 2026-02-22 (verified against running code)
**Status**: Complete — 520 macros in production
**Version**: v25-R2 (with epsilon-safe argumentful extensions)

## Executive Summary

The LaTeX Perfectionist L1 Macro Expander uses two complementary macro catalogs, both fully integrated into the production runtime (`macro_catalogue.ml`, 487 lines):

1. **Symbol Catalog**: 441 zero-arity symbol macros (383 base v25r2 + 58 expansions)
2. **Argsafe Catalog**: 79 argumentful macros (62 base + 17 Phase 5d additions)

Combined, these provide **520 macros** for L1 expansion. All are loaded at startup via hash-table lookup (O(1) per macro). Verified with 192 dedicated test cases.

## Catalog Breakdown

### 1. Symbol Macros — 441 Total

**Mode Distribution**:
- Math mode: ~280 macros
- Text mode: ~130 macros
- Any mode: ~31 macros

**Categories**:
- **Math symbols**: Greek letters, operators, arrows, relations, delimiters
- **Text symbols**: Currency, typography, special characters
- **Unicode expansions**: Extended coverage beyond base v25r2

**Key Properties**:
- All arity=0 (no arguments)
- All safety="pure" (no side effects)
- Single token expansions (TText, TOp, or TDelim)
- O(1) hash-table lookup

### 2. Argsafe Macros — 79 Total

**Text Style Macros** (10):
```
\textbf{...}   → {\bfseries ...}
\textit{...}   → {\itshape ...}
\texttt{...}   → {\ttfamily ...}
\textsf{...}   → {\sffamily ...}
\textsc{...}   → {\scshape ...}
\textmd{...}   → {\mdseries ...}
\textnormal{...} → {\normalfont ...}
\textrm{...}   → {\rmfamily ...}
\textsl{...}   → {\slshape ...}
\textup{...}   → {\upshape ...}
```

**Math Style Macros** (6):
```
\mathrm{...}   → {\mathrm{...}}
\mathbf{...}   → {\mathbf{...}}
\mathsf{...}   → {\mathsf{...}}
\mathtt{...}   → {\mathtt{...}}
\mathit{...}   → {\mathit{...}}
\mathnormal{...} → {\mathnormal{...}}
```

**Special Builtins** (7):
```
\emph{...}              → {\itshape ...}
\mbox{...}              → [builtin:mbox]
\verb|...|              → [builtin:verb]
\verb*|...|             → [builtin:verb_star]
\textsuperscript{...}   → [builtin:textsuperscript]
\textsubscript{...}     → [builtin:textsubscript]
\ensuremath{...}        → [builtin:ensuremath]
```

**Multi-Arg Math Operators** (17, added Phase 5d / PR #158):
```
\frac{num}{den}         → fraction template
\binom{n}{k}            → binomial template
\overset{top}{base}     → overset template
\underset{bot}{base}    → underset template
\stackrel{top}{base}    → stackrel template
\sqrt{arg}              → sqrt template
\overline{arg}          → overline template
\underline{arg}         → underline template
\hat{arg}, \bar{arg}, \tilde{arg}, \vec{arg}
\dot{arg}, \ddot{arg}
\widehat{arg}, \widetilde{arg}, \overrightarrow{arg}
```

**Additional argsafe macros** (39): Various text/math formatting extensions.

## Implementation Status — COMPLETE

### Production Integration (verified 2026-02-22)

**Production file**: `latex-parse/src/macro_catalogue.ml` (487 lines)
- ✅ 441 symbol macros loaded from v25r2 JSON + expansions
- ✅ 79 argsafe macros with epsilon-safe templates
- ✅ Multi-argument support ($1, $2 positional placeholders)
- ✅ Mode-aware expansion (Math / Text / Any / Both)
- ✅ Inline + Builtin template types
- ✅ Hash-table O(1) lookup
- ✅ 192 test cases passing (`test_macro_catalogue.ml`)

**Integration points**:
- `rest_simple_expander.ml`: Expands macros before L1 validation
- `rest_api_server.ml`: REST endpoint exposes expansion
- Golden test corpus: 236 cases test full pipeline

### Not in L1 Scope (by design)

These are L2+ features, intentionally excluded:
- Document structure (`\section`, `\chapter`, `\usepackage`) — requires L2 AST
- Cross-references (`\ref`, `\label`, `\cite`) — requires document-wide state
- Environments (`\begin`/`\end`) — requires stateful tracking
- Counters, conditionals — mutable state / Turing-complete

## Epsilon Safety Policy

**Allowed in Templates**:
- Pure grouping: `{...}`
- NFSS switches: `\bfseries`, `\itshape`, `\ttfamily`, etc.
- Math font switches: `\mathrm`, `\mathbf`, etc.
- Placeholders: `$1`, `$2`, `$3`

**Forbidden**:
- I/O operations, file access
- Catcode manipulation, assignments/counters
- Box measurements, package-dependent effects

## Performance

Measured locally 2026-02-22 (includes macro expansion in pipeline):
- **A+B p95 (1.1MB)**: 3.25 ms (target ≤ 20 ms)
- **Hash-table lookup**: O(1) per macro, negligible overhead
- **520 macros loaded**: No measurable impact on startup

## Summary Statistics

**Total Macros**: 520
- Zero-arity symbols: 441 (85%)
- Argumentful macros: 79 (15%)

**Safety**:
- 100% pure (no side effects)
- 100% deterministic
- 100% epsilon-safe for argumentful macros
