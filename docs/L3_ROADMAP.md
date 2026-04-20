# L3 Semantic Derivation — Roadmap

> Written in response to memo §15.5:
> > "Document honestly that current L3 is partly source-regex-derived, then plan migration toward AST/project semantics."

## Current state (v26.1)

The L3 layer — `latex-parse/src/validators_l3_file.ml` + `latex-parse/src/semantic_state.ml` + `latex-parse/src/validators_project.ml` — has two kinds of rules:

1. **File-based (20 rules, Formal Conservative)** — PNG/JPEG/PDF/font/TIKZ binary readers. These consult extracted binary metadata via `File_context.get_file_context`. Formal soundness is vacuous (Coq `check = false`) because there's no string model to mirror.
   - FIG-004, FIG-006, FIG-016, FIG-021, FIG-023
   - COL-001, COL-002, COL-003, COL-004, COL-005, COL-007
   - PDF-006, PDF-007, PDF-008, PDF-009, PDF-011, PDF-012
   - TIKZ-002, TIKZ-008, CJK-007

2. **Source-regex-derived semantic context (rest of L3)** — Label/ref tracking, duplicate detection, undefined-ref identification. The current implementation extracts `\label{...}` / `\ref{...}` / `\cite{...}` via regex scans over the raw source, not via AST traversal. Similarly for project graph construction (`\input`, `\include`, `\includeonly`).

This is **honest but not yet rigorous**: a `\label` hidden in a comment, inside a verbatim, or behind a macro that expands to the command still fires the regex. The formal proofs for these rules (`LabelsUnique.v`, `InterpLocality.v`) abstract over the exact derivation; they hold *given* the extracted label set, but don't prove the extractor matches the AST semantics.

## Why it ships this way in v26

- Source regex extraction is cheap on the keystroke-critical path (p95 ≈ 2.8ms for 1MB documents vs. a full AST walk ~ 10-40ms).
- The failure modes (comment-hidden labels, macro-expanded references) are rare in practice and don't produce false negatives that matter for the v26 LP-Core tier (no shell-escape, no custom catcodes, bounded macro subset).
- The L2 parser + partial-CST machinery are recent additions (PR #231); the L3 migration is a substantial refactor best done when the CST layer stabilises.

## Migration plan (v26.2 → v27)

### v26.2 (deferred from v26.1)

1. **Lossless CST substrate** (memo §7, already scoped for v26.2):
   - `core/l2_parser/cst.ml`, `cst_builder.ml`, `stable_spans.ml`
   - Round-trip preservation (`CSTRoundTrip.v`)

2. **AST-derived label/ref extraction**:
   - New module `latex-parse/src/ast_semantic_state.ml` that walks the CST instead of regex-scanning source.
   - Label/ref rules (LAB-*, REF-*) switch to this when profile = LP-Core AND CST is available.

3. **Regex-vs-AST parity gate**:
   - CI smoke test: run both extractors on the golden corpus; results must match on clean documents. Diverge-cases documented as expected (macros, comments).

### v27.0 (if platform scope admits)

4. **Full project semantic projection** (memo §8):
   - `core/project/project_semantics.ml`
   - Cross-file label/ref resolution via the include graph instead of flat source scans.
   - Proof: `ProjectSemantics.v`.

5. **Deprecate source-regex path**:
   - Once AST-derived extraction has shipped for 2 releases with the parity gate green, the regex path becomes the fallback (triggered only when CST construction fails).

## What users can expect today

- **LP-Core documents**: regex extraction is correct. No known false positives or false negatives within the supported subset.
- **LP-Extended documents**: some macros may produce surprises (e.g. `\def\mylabel{\label{...}}` then `\mylabel{foo}` — the regex won't match; the AST walk would).
- **LP-Foreign**: all bets are off; the classifier surfaces this explicitly.

See also:
- `docs/PROOF_CLASSES.md` — where L3 conservative proofs sit in the taxonomy
- `docs/BUILD_LOG_CONTRACT.md` — L3 rules that consume compile-log context
- `specs/v26/language_contract.md` — tier boundaries that bound the claim
