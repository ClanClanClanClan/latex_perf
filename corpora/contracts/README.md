# Configuration contracts (ADR-012, milestone M1)

Generated data. Nothing here is written by hand and nothing reads it yet: the
first consumer is milestone M2 (`docs/v27/STRICT_TIER_DESIGN.md` §F).

| file | what |
|---|---|
| `<name>.json` | one configuration contract (schema `lp-configuration-contract/1`), written by `scripts/tools/gen_contract.py generate` |
| `kernel/<arch>-<fmt sha256 prefix>.json` | the kernel closed world for that `pdflatex.fmt`: every name defined in format state, with its meaning kind, and the evidence that the set is complete (`coverage`: TeX's own hash-table count finds 0 names outside the candidates; `primitives`: the engine's primitives, counted against TeX's own count) |
| `probes/<name>.json` | a probe-harness demonstration report (schema `lp-probe-report/1`), written by `gen_contract.py probes` |
| `parser_fixtures/` | excerpts of real generator logs, the fixtures of `scripts/tools/check_gen_contract_parsers.py` (required `spec-drift`), which also checks the committed kernel file and contracts for completeness |

Every TeX job ran inside the pinned image named by `TEX_IMAGE` in
`.github/workflows/tex-oracle.yml` (ADR-012 decision 7), never the laptop TeX
Live. The contracts record the image's architecture (`pin.arch`, arm64 here).
The digest is a multi-arch index, so another architecture runs a separately
built image; whether its `pdflatex.fmt` is byte-identical is not measured.

Regenerate and diff (needs docker and the image; local or nightly only):

    python3 scripts/tools/check_contracts_reproducible.py --all

To add a configuration:

    python3 scripts/tools/gen_contract.py generate --class article \
        --package amsmath --package 'hyperref[colorlinks]' --name my-config

## parser_fixtures

Cut from the logs of real runs of the generator under the pinned image, not
synthesised:

- `trace_excerpt.log`: the pass-1 trace of article + amsmath, amssymb, amsthm,
  graphicx, hyperref (load markers, a record printed mid-line after a
  file-open parenthesis, the class-loading window where `\escapechar=-1`,
  a control symbol named `=`, a name that holds line feeds, register
  assignments).
- `trace_fatal_excerpt.log`, `load_fatal_excerpt.log`: the trace and the load
  run of article + cleveref + hyperref, which stops at `\begin{document}`.
- `dump_excerpt.log`, `selfcheck_excerpt.log`: the body-start meaning dump and
  the closure self-check of the same five-package configuration, including a
  meaning that holds raw line feeds and the text `! LaTeX Error`.
- `load.fls`: the `-recorder` file of that configuration's load run.
- `kernel_meanings_excerpt.json`: a few format-state meanings from the kernel
  dump, one per meaning kind.
- `trace_nullcs_excerpt.log`, `trace_eqname_excerpt.log`,
  `trace_setin_excerpt.log`: the pass-1 traces of the three definer repros of
  the 2026-09-27 reviews (the null control sequence, printed both as
  `\csname\endcsname` and as `csnameendcsname`; a name holding `=`, with the
  kernel's own `\__file_name=<file>` records; a group-local `\def` undone at
  a group end), cut to the relevant records and markers.
- `trace_resetsame_excerpt.log`: the markers and the `\WriteBookmarks`
  records of the five-package trace: hyperref sets it to `0`, a
  begin-document group re-sets the same value and a group end restores it
  (the re-review's LOW item a; its `set_in` is `package:hyperref`).
- `trace_tilde_excerpt.log`: records of the five-package trace where the
  active `~`, printed under `\escapechar=-1`, reads like the control symbol
  `\~`.
- `review_missing_names.json`: the 24 names the 2026-09-27 reviews measured
  as defined in format state and missing from the first kernel file; the
  completeness check requires every one in the kernel file.
