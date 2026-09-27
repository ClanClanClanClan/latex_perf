# Configuration contracts (ADR-012, milestone M1)

Generated data. Nothing here is written by hand and nothing reads it yet: the
first consumer is milestone M2 (`docs/v27/STRICT_TIER_DESIGN.md` §F).

| file | what |
|---|---|
| `<name>.json` | one configuration contract (schema `lp-configuration-contract/1`), written by `scripts/tools/gen_contract.py generate` |
| `kernel/<arch>-<fmt sha256 prefix>.json` | the kernel closed world for that `pdflatex.fmt`: every name the format defines, with its meaning kind |
| `probes/<name>.json` | a probe-harness demonstration report (schema `lp-probe-report/1`), written by `gen_contract.py probes` |
| `parser_fixtures/` | excerpts of real generator logs, the fixtures of `scripts/tools/selftest_gen_contract.py` |

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
