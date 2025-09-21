# Proofs Overview (v25_R1)

This document summarizes the current formal model and lemmas implemented for the L0 SoA lexer and related components. All proofs compile with zero admits and zero axioms.

## Files

- `proofs/CoreProofs.v`: Baseline zero‑admit compliance theorem.
- `proofs/Catcode.v`: Catcode enumeration and helpers.
- `proofs/Arena_safe.v`: Safety lemmas for arena usage (from archive, restored).
- `proofs/LexerFaithfulStep.v`: Simple faithful small‑step (byte→token) with determinism and progress.
- `proofs/LexerSoA.v`: SoA‑shaped model with ASCII→catcode mapping and full locality/composition.
- `proofs/LexerDeterminism.v`: Determinism for faithful step.
- `proofs/LexerTotality.v`: Progress/totality on nonempty inputs for faithful step.

## L0 SoA Highlights (LexerSoA.v)

- Kind classifier: `classify_kind b = catcode_to_kind (Catcode.classify_ascii b)` (0..15 with bound proof).
- Big‑step functional semantics: `run_from`, `run` (produces kinds/offs/codes arrays).
- Composition: `run_app` for kinds/codes/offs across concatenation.
- Locality (mid window):
  - `kinds_window_mid`, `codes_window_mid`, `offs_window_mid`, `issues_window_mid`.
  - Normalized offsets: `offs_window_mid_normalized` yields `seq 0..len(mid)-1`.
- Stability under edits outside the window:
  - `kinds_window_stability`, `codes_window_stability`, `offs_window_stability_normalized`.
- Prefix/suffix invariance and a combined equivalence: `window_equivalence` and `window_equivalence_stability`.
- General `edit_locality_corollary` using window slices (offset/length) without explicit concatenation.

## CI Gate

- `.github/workflows/proof-gate.yml` builds proofs via dune and enforces zero admits/axioms.

Run locally:

```bash
OPAMSWITCH=l0-testing opam exec -- dune build @coq
```

## Incremental Lexer (LexerIncremental.v)

- Executable model: `tokenize : list byte -> list token` with identity mapping for staging.
- Window lemmas:
  - `tokenize_window_equivalence`: slice `pre++mid++suf` equals `tokenize mid`.
  - `window_locality_under_prefix_change`: mid tokens invariant under prefix/suffix changes.
- Offsets and normalization:
  - `offsets_of bs = seq 0 (length (tokenize bs))`.
  - `offsets_window_equivalence`: offsets slice equals `seq (|pre|) (|mid|)`.
  - `normalized_offsets_window`: normalized offsets of the mid slice equal `seq 0 (|mid|)`.
- Edits outside the window:
  - Smallstep `step_outside` and closure `steps_outside` preserve mid tokens and normalized offsets.
- Edits inside the window:
  - Head edits: `mid_edit` (insert/delete at head) with normalized offsets preserved.
  - Arbitrary index edits: `mid_edit_at` (insert/delete at split `l ++ r`).
  - Token alignment: `tokenize_insert_at_split`, `tokenize_delete_at_split`, and `mid_edit_at_tokenize_alignment`.
  - Offset composition/mapping:
    - `normalized_offsets_split`, `normalized_offsets_insert_at_split`, `normalized_offsets_delete_at_split`.
    - Map-based shifts: `map_shift_insert_seq`, `map_shift_delete_seq` and contextual forms under `pre`/`suf`.

All lemmas are admit-free and form a foundation to swap in the faithful small‑step lexer semantics while retaining window locality and edit stability proofs.
