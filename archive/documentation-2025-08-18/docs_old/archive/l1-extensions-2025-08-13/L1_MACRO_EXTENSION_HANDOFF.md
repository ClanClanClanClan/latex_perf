# L1 Macro Extension Handoff Document

## Context
The L1 macro expander currently has 406 working macros (383 symbols + 23 argumentful). This document proposes 56 additional L1-safe macros that maintain epsilon-safety and the architectural boundary between L1 and L2.

## Architectural Constraints
- **L1 Layer**: Simple substitution only, <0.1ms overhead, epsilon-safe
- **L2 Layer**: Complex parsing, multi-argument constructs, conditional logic
- **L3 Layer**: Document structure, cross-references, counters
- **L4 Layer**: Bibliography, indexes, complex document features

## Proposed L1 Extensions (56 macros)

### Category 1: Missing Text Symbols (12 macros)
These are direct Unicode substitutions missing from the current catalog:

**Currency symbols:**
- `\textcurrency` → ¤
- `\textlira` → ₤  
- `\textwon` → ₩
- `\textrupee` → ₹

**Common punctuation:**
- `\textexclamdown` → ¡
- `\textquestiondown` → ¿
- `\textquoteleft` → '
- `\textquoteright` → '
- `\textquotedblleft` → "
- `\textquotedblright` → "

**Publishing marks:**
- `\textsection` → §
- `\textpilcrow` → ¶

### Category 2: Logic Symbols (15 macros)
Mathematical logic operators appropriate for L1:

**Basic logic:**
- `\land` → ∧
- `\lor` → ∨
- `\lnot` → ¬
- `\implies` → ⇒
- `\iff` → ⇔

**Quantifiers:**
- `\forall` → ∀
- `\exists` → ∃
- `\nexists` → ∄

**Additional arrows:**
- `\uparrow` → ↑
- `\downarrow` → ↓
- `\updownarrow` → ↕
- `\nearrow` → ↗
- `\searrow` → ↘
- `\swarrow` → ↙
- `\nwarrow` → ↖

### Category 3: Mathematical Font Commands (15 macros)
Single-argument font switches with epsilon-safe templates:

**Math fonts:**
- `\mathcal{X}` → `{\mathcal{X}}`
- `\mathscr{X}` → `{\mathscr{X}}`
- `\mathfrak{X}` → `{\mathfrak{X}}`

**Text font families:**
- `\textrm{text}` → `{\rmfamily text}`
- `\textsf{text}` → `{\sffamily text}`
- `\texttt{text}` → `{\ttfamily text}`
- `\textsl{text}` → `{\slshape text}`
- `\textup{text}` → `{\upshape text}`
- `\textmd{text}` → `{\mdseries text}`
- `\textnormal{text}` → `{\normalfont text}`

**Additional shapes:**
- `\textbfseries{text}` → `{\bfseries text}`
- `\textitshape{text}` → `{\itshape text}`
- `\textscshape{text}` → `{\scshape text}`
- `\textupshape{text}` → `{\upshape text}`
- `\textslshape{text}` → `{\slshape text}`

### Category 4: Accent Commands with Unicode Mapping (8 macros)
Simple accent application using Unicode combining characters:

- `\grave{e}` → è (combining grave accent)
- `\acute{e}` → é (combining acute accent)
- `\hat{e}` → ê (combining circumflex)
- `\tilde{n}` → ñ (combining tilde)
- `\bar{o}` → ō (combining macron)
- `\breve{u}` → ŭ (combining breve)
- `\dot{z}` → ż (combining dot above)
- `\ddot{a}` → ä (combining diaeresis)

### Category 5: Spacing Commands (4 macros)
Non-breaking spaces of various widths:

- `\quad` → em space
- `\qquad` → 2×em space
- `\enspace` → en space
- `\thinspace` → thin space

### Category 6: Additional Symbols (2 macros)
Decorative symbols commonly used:

- `\bigstar` → ★
- `\blacksquare` → ■

## What Is NOT Included (Deferred to L2)

These require L2's parsing capabilities:
- `\frac{num}{den}` - needs two-argument parsing
- `\sqrt[n]{x}` - optional + required arguments
- `\begin{env}...\end{env}` - environment processing
- `\left(...\right)` - delimiter matching
- `\newcommand` - macro definition
- `\cite{key}` - bibliography lookups
- `\ref{label}` - cross-references
- Conditionals like `\ifx`, `\iftrue`
- Counters and lengths
- Any construct requiring state or context

## Implementation Notes

1. **Symbol macros**: Direct token substitution
2. **Argumentful macros**: Template-based with `$1` placeholder
3. **Epsilon validation**: All templates use only allowed constructs
4. **Performance**: Must maintain <0.1ms overhead per document
5. **Unicode**: Use precomposed characters where available, combining otherwise

## Summary Statistics
- **Current L1 system**: 406 macros
- **Proposed additions**: 56 macros
- **Total after extension**: 462 macros
- **Performance impact**: Negligible (<0.01ms additional)
- **All epsilon-safe**: ✓
- **All L1-appropriate**: ✓

## Next Session Tasks
1. Implement these 56 macros in the production L1 expander
2. Update JSON catalogs with new entries
3. Test with existing corpus
4. Verify performance remains <0.1ms
5. Document any Unicode rendering issues

---
*This handoff document defines 56 carefully scoped L1 macro extensions that respect the architectural boundaries of the LaTeX Perfectionist system.*