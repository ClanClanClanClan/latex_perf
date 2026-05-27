# Archived: Coq proof fix-pack handoff (fix-math-strip branch)

These files document a one-time expert consultation that resolved three
blocking proof errors on the (now-deleted) `fix-math-strip` branch:

- `coq-proof-handoff.md` — initial question (build errors in
  `L0SmallstepControl.v`, `L0Smallstep.v`, `LexerIncremental.v`).
- `coq-proof-handoff-answer.md` — Fix Pack v1 (boolean/byte
  precedence + `firstn`/`skipn` rewrite stabilisation).
- `coq-proof-current-status.md` — follow-up question after partial
  application of Fix Pack v1.
- `coq-proof-current-status-answer.md` — Fix Pack v2 (specialised
  `firstn_length_append_token` wrappers + determinism-based
  `rrun_nf_unique`).
- `coq-proof-handoff-superseded.md` — a parallel handoff doc (formerly
  `docs/coq-proof-handoff.md`) marked itself superseded by
  `coq-proof-current-status.md`; archived here for completeness.

The fixes were applied long ago. The proof tree currently builds clean
under `opam exec -- dune build proofs` with **1,400 theorems / 0
admits / 0 axioms** across 170 `.v` files (see
`governance/project_facts.yaml` for the live count).

Archived in v27.0.60 because the live docs at `docs/expert/` had become
fossils: they referenced a branch that no longer exists and a build
error class that has been resolved for many releases.
