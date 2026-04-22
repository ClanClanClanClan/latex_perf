# v26.2 user personas

Decisions about new features (`--apply-fixes`, CST API, compile_contract)
hinge on who's using the tool. Three personas anchor scope:

## P1 — Academic researcher

- Writes ~20-page papers in LaTeX, re-runs latexmk on save.
- Cares: compile errors caught early; pretty output.
- Doesn't care: CLI flags beyond `--apply-fixes`; CST API; fix customisation.
- Runs on: laptop; no CI.
- **v26.2 wins:** `--apply-fixes` auto-fixes typography, compile_contract
  tells them "missing reference, no rerun needed" before latexmk.
- **Scope call:** UX priority for CLI output; no API-facing demands.

## P2 — Industrial technical writer

- Multi-file documentation trees; builds into CI pipeline.
- Cares: reproducible builds; zero false positives; sensible exit codes.
- Doesn't care: Coq proofs; formal guarantees.
- Runs on: Docker CI runners; Jenkins or GitHub Actions.
- **v26.2 wins:** compile_contract gives CI a pre-compile predicate
  (fail-fast without running latexmk); differential-test gate prevents
  silent regressions.
- **Scope call:** CLI stability matters more than Coq; docker image
  continuity required.

## P3 — Compiler/linting researcher integrating our library

- Embeds `latex_parse_lib` in their own tool.
- Cares: API stability; typed public interface; CST for structural analysis.
- Doesn't care: CLI UX.
- Runs on: their own OCaml project.
- **v26.2 wins:** CST with stable IDs makes structural analysis tractable;
  rewrite engine is a building block for their own pass.
- **Scope call:** strict API stability commitment (§8 of plan) matters most.

## Non-personas (out of v26.2 scope)

- Real-time editor plugins (v27 WS10 collaboration — IDE integration).
- Cloud-hosted service with SLA (v27 WS11 platform).
- Non-LaTeX ingesters (v27 WS12 extension plane).

## What this implies for contested design decisions

- `--apply-fixes-for RULE-ID` granularity: deferred (P1/P2 want all-or-nothing;
  P3 will wrap the library directly).
- CST streaming API: deferred (P3 use cases we've heard work fine with
  whole-document CST; streaming is v27 if demanded).
- Fix-suggestion localization: deferred (P1 academic writers are
  English-speaking majority; v27 if international adoption grows).
- Undo safety for `--apply-fixes`: **MUST ship in v26.2**. P2 CI users
  cannot tolerate silent source corruption. See
  [ROLLBACK_DRILL.md](ROLLBACK_DRILL.md).
