Unit Tests
==========

This repository includes focused unit/property tests for two critical utilities:

1) Math Stripping Heuristic
- File: latex-parse/src/test_strip_math.ml
- Purpose: Verify that strip_math_segments removes inline and environment math segments while preserving text outside math.
- Coverage:
  - Inline math: $...$, \( ... \), \[ ... \]
  - Math environments: equation, equation*, align, align*, gather, gather*, multline, multline*, eqnarray, math, displaymath
  - Escaped dollars \$ do not toggle math mode
  - Simple nested content inside \[ ... \] via \text{...}
- Run locally:
  - Build: opam exec -- dune build latex-parse/src/test_strip_math.exe
  - Execute: ./_build/default/latex-parse/src/test_strip_math.exe

2) Tokenizer Properties
- File: latex-parse/src/test_tokenizer_props.ml
- Purpose: Guard span invariants and round‑trip reconstruction for Tokenizer_lite.
- Checks:
  - Non‑overlapping tokens with monotone ‘e’ offsets, all within [0, len]
  - Reconstructing the source by concatenating token substrings matches the original
- Run locally:
  - Build: opam exec -- dune build latex-parse/src/test_tokenizer_props.exe
  - Execute: ./_build/default/latex-parse/src/test_tokenizer_props.exe

CI Integration
--------------

- Unit Tests workflow: .github/workflows/unit-tests.yml
  - Builds and runs both executables; fails on any test failure.
- Unit Tests badge: .github/workflows/unit-tests-badge.yml
  - Publishes public-badges/unit_tests.json to gh‑pages and a shield is embedded in README.

Adding More Tests
-----------------

- For utility or property tests:
  - Place OCaml test files under latex-parse/src/, name them test_*.ml
  - Add a test stanza to latex-parse/src/dune, e.g.:
    (test (name test_my_feature) (modules test_my_feature) (libraries latex_parse_lib))
  - Build and run locally, then add to unit-tests.yml if you want it in CI.
- For validators:
  - Prefer golden corpora + smokes (scripts/smoke_rules_*.sh) to validate IDs and messages end‑to‑end.
  - Add new inputs under corpora/lint/… and expected mappings in specs/rules/*.yaml.

