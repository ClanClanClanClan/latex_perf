# Appendix L — Road-map & De-scoped Ideas

Per v25 master plan §15, Table L (5 pages).

## L.1 De-scoped from v25

| Feature | Reason | Target |
|---------|--------|--------|
| Full catcode reassignment | Turing-complete; violates epsilon-safety | v27+ |
| `\newcommand` expansion | Requires document-wide state; out of L1 scope | v26 |
| Beamer frame structure | No validators in v25 rule catalogue | v26 |
| Algorithm env deep parsing | No validators beyond float detection | v26 |
| PDF output analysis | Requires LaTeX compilation; L3 true-semantic | v26 |
| Compile-log parsing (full) | 55 rules need `.log` file; partial in v25 | v26 |
| GPU TikZ rasterisation | Experimental L5; needs A100 access | v26 |

## L.2 v26 Forward-looking

- **L3 Compile-Log Integration**: Parse `.log` files for overfull/underfull boxes, widow/orphan penalties, page layout violations. Enables the remaining 55 unimplemented rules (LAY, PAGE families).
- **User Macro Registry**: Parse `\newcommand`/`\renewcommand` from preamble into a per-document macro table. Feed into L1 expander as document-scoped catalogue extension.
- **Multi-file Linting**: Resolve `\input`/`\include` chains. Build a file dependency graph. Run validators across the full document tree.
- **Beamer Support**: Detect `\documentclass{beamer}`, parse `frame` environments, validate slide structure.

## L.3 v27 Research Items

- **Full Catcode Support**: Track `\catcode` assignments through document. Requires a catcode-state machine per chunk boundary.
- **Conditional Expansion**: Limited `\ifx`/`\iftrue` support for common patterns (package detection, engine detection). Not full Turing-complete expansion.
- **Interactive IDE Protocol**: LSP-compatible incremental analysis. Real-time diagnostics with sub-10ms latency on keystroke.
- **Formal PEG Verification**: Prove the PEG grammar in `l2_parser_peg_grammar.peg` is unambiguous and complete for the LaTeX-epsilon subset.

## L.4 Gated Features (v25)

These features exist in v25 but are gated behind environment variables or feature flags:

| Feature | Gate | Status |
|---------|------|--------|
| TYPO rules | `L0_VALIDATORS=pilot` | Active in CI |
| SIMD catcode scanner | Runtime CPU detection | AVX2/NEON auto-selected |
| Lock-free event bus | Always on (OCaml 5.x Atomic) | Production |
| ML byte classifier | Requires trained model checkpoint | Blocked on A100 |
