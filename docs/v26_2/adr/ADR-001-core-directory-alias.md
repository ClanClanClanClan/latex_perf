# ADR-001: core/l2_parser/ alias pattern instead of directory migration

- **Status:** Accepted (2026-04-22)
- **Context owner:** v26.2 architectural decisions (plan §2.1)

## Context

Memo `REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §§5.5, 16.3 prescribes
new modules under `core/l2_parser/` (e.g. `core/l2_parser/cst.ml`,
`core/l2_parser/partial_cst.ml`). The repo does not have a `core/`
directory — every OCaml module lives under `latex-parse/src/`. We've
already aliased three memo-prescribed paths (P1.6 `macro_subset.ml`,
P1.7 `invalidation_engine.ml` and `log_context.ml`).

## Decision

**Ship v26.2 modules under `latex-parse/src/` with thin alias modules at
memo-prescribed paths** (e.g. `core/l2_parser/cst.ml` re-exports
`Latex_parse_lib.Cst`). Continue the pattern established in P1.6/P1.7.

## Alternatives considered

- **Option A: Migrate to `core/l2_parser/` as a real dune library.**
  Would require splitting `latex_parse_lib` into multiple libraries,
  editing every dune file, and likely breaking downstream consumers.
  Estimated 1 full day of build-system work for zero user-visible gain.
  Rejected.
- **Option B: Ignore the memo path, don't alias.**
  Leaves `check_memo_files.py` failing on memo-prescribed paths. Rejected
  — drift is unacceptable per audit discipline.

## Consequences

- Memo paths remain "canonical prose, aliased runtime". Future readers
  see both the memo ref and the real path side-by-side.
- `check_memo_files.py` PATH_ALIASES grows by ~4 entries in v26.2.
- Technical debt flag: if v27 decides to reorganize the source tree
  (e.g. for `core/project/`, `core/l1_expander/`, etc.), this alias
  pattern becomes part of the migration cleanup scope.
- No impact on v26.2 user-facing API.
