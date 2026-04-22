# ADR-006: CST structured subset — what's in, what's Unparsed

- **Status:** Accepted (2026-04-22)
- **Context owner:** v26.2 architectural decisions (plan §2.6)

## Context

ADR-005 promises "structure-lossless for the declared subset". This
ADR declares the subset.

## Decision

### IN scope for structured CST

- **UTF-8 source** (multi-byte codepoints allowed).
- **Standard catcode regime** — no mid-document `\catcode` in body.
- **Balanced groups, environments, math modes** (inline `$...$`, display
  `\[...\]`, `equation`, `align`, etc.).
- **Comments** (full-line starting with `%`, end-of-line `%foo`) — body
  preserved byte-exact.
- **Whitespace** preserved byte-exact (including CRLF vs LF).
- **Macro definitions** via `\newcommand` / `\renewcommand` /
  `\providecommand` with standard arity specs `[N][default]`.
- **Cross-references** — `\label`, `\ref`, `\pageref`, `\eqref`, etc.

### OUT of scope — falls back to `Unparsed`

- `\verb` / `\verb*` / `\lstlisting` / `fancyvrb` blocks — verbatim
  bodies change the catcode regime locally.
- `\begin{comment}` ... `\end{comment}` (comment package) — verbatim-family.
- Arbitrary `\def` with non-standard catcode specs (`\def\foo##1{...}`
  with implicit catcode changes).
- `\catcode` declarations in document body.
- `\newenvironment` custom environments — body becomes `Unparsed`
  (v26.2 doesn't track user-env body semantics).
- BOM handling — `Cst.of_source` on a BOM-prefixed input rejects with
  `Error BadEncoding`.
- Mixed encodings (non-UTF-8) — same as above.

### `\input` / `\include` behavior

CST does **NOT** inline included files. `\input{sub}` is preserved as a
structured token pointing at `sub`; cross-file analysis happens in the
`project_model` layer, not the CST layer. Rationale: CST preserves
source of a *single file*; multi-file semantics are orthogonal.

## Consequences

- `Unparsed` regions are common in real documents that use `\verb` or
  `\lstlisting`. Users see `(Unparsed "...")` nodes in their CST.
- `CSTRoundTrip.v` subset proof covers only IN-scope constructs. OUT-
  scope constructs survive the byte-lossless theorem but not the
  structure-lossless one.
- Future subset extensions (adding `\verb` support, etc.) are
  backward-compatible: today's `Unparsed` verbatim becomes tomorrow's
  typed `Verbatim` node, with no change in byte-level semantics.
- `docs/CST_ROUNDTRIP_SCOPE.md` (created in B2) documents this subset
  with worked examples.
