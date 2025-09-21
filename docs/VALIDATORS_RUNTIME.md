# Validators Runtime (Pilot)

This document explains how runtime validators are wired into the current service and how to enable the pilot rules.

## Location
- Source: `latex-parse/src/validators.ml`
- REST integration:
  - `/expand` calls `Validators.run_all` directly (no SIMD service required)
  - `/tokenize` calls SIMD service, then augments the JSON with validator summaries

## Feature Flag
- Env var: `L0_VALIDATORS`
  - Values enabling the pilot: `pilot`, `1`, `true`, `PILOT`
  - Unset/other values: run the minimal baseline rules only
- Enable for REST:
  ```bash
  L0_VALIDATORS=pilot make rest-run
  # or
  export L0_VALIDATORS=1 && make rest-run
  ```

## Rule Sets
- Baseline (minimal): `rules_basic`
  - Includes `no_tabs`, `require_documentclass`, `unmatched_braces`, `missing_section_title`
- Pilot (L0 subset): `rules_pilot`
  - IDs aligned with `specs/rules/rules_v3.yaml`
  - Implemented string-level: `TYPO-001`…`TYPO-010`
  - See `specs/rules/pilot_v1.yaml` for the enumerated pilot list

## L1 Modernization & Post‑Expansion Checks

- L1 rules run when layer=l1 is specified (e.g., `/expand?layer=l1`), and include:
  - EXP‑001: Incomplete expansion — catalogue commands remain post‑expansion
  - MOD‑001: Legacy font commands present (e.g., `\bf`, `\it`, `\tt`, `\rm`, `\sf`, `\sl`)
  - MOD‑002: Mixed legacy/modern bold in same paragraph (`\bf` vs `\textbf`)
  - MOD‑003: Mixed legacy/modern italic (`\it` vs `\emph`/`\textit`)
  - MOD‑004: Mixed legacy/modern roman (`\rm` vs `\textrm`)
  - MOD‑005: Mixed legacy/modern typewriter (`\tt` vs `\texttt`)
  - MOD‑006: Mixed legacy/modern sans‑serif (`\sf` vs `\textsf`)
  - MOD‑007: Mixed legacy/modern small‑caps (`\sc` vs `\textsc`)

- Implementation details:
  - REST exposes a lightweight expander for `/expand` that returns the post‑expansion text.
  - REST and the CLI annotate a per‑request “post summary” of command spans; the validators consume this via a thread‑local context to perform paragraph‑aware checks with precise spans.
  - See `docs/REST_API.md` (L0_DEBUG_L1) for the post_summary schema.

## Severity
- Internal type: `type severity = Error | Warning`
- For the pilot, Info-level catalogue rules are surfaced as `Warning` to keep the type simple. This can be widened later if needed.

## Results
- `Validators.run_all : string -> result list`
  - `result = { id; severity; message; count }`
- REST shapes:
  - `/expand`: returns `validators` as a JSON list of `{id,severity,message,count}`
  - `/tokenize`: wraps into `.validators.results` and includes counters `.applied`, `.errors`

## Smokes & Golden Tests
- Golden corpora: `corpora/lint/pilot_v1/*.tex`
- Expected IDs: `specs/rules/pilot_v1_golden.yaml`
- Smokes (REST):
  ```bash
  # Start REST with pilot
  L0_VALIDATORS=pilot make rest-run

  # Execute golden expectations via /expand
  bash scripts/smoke_rules_pilot.sh

  # Optional: latency smoke and gate summary on /expand (no SIMD service)
  bash scripts/latency_smoke_expand.sh 200
  ```

### False‑Positive Scan (CLI)

Run the pilot rules over a directory of `.tex` files and produce a simple CSV of hit counts per rule ID:

```bash
L0_VALIDATORS=pilot bash scripts/pilot_fp_scan.sh corpora/perf
# Summary printed and CSV at /tmp/pilot_fp_summary.csv
```

## Token‑Aware Mode (FP Reduction)

Enable token‑aware variants of spacing/adjacency rules to reduce false positives on real corpora:

- Flag: `L0_TOKEN_AWARE=1` (or `true`/`on`)
- Coverage (examples): TYPO‑007/8/10/11/12/13/15/18/19/21/22/25/27/28/29; also refined detection for TYPO‑020/026.
- Implementation: `tokenizer_lite` produces a minimal token stream (Word/Space/Newline/Command/Bracket/Quote/Symbol) used by those rules.
- Fallback: If the flag is not set, byte/string‑level detection remains in effect.

## Timing & Duration (Optional)

Add aggregate and per‑rule timing metrics to the `.validators` object in REST responses:

- `L0_INCLUDE_VALIDATORS_DURATION=1` — include `.validators.duration_ms` (total runtime for all validators on the request).
- `L0_INCLUDE_VALIDATORS_TIMINGS=1` — include `.validators.timings` array with per‑rule timing objects `{ id, duration_ms }` in execution order.

These flags are off by default to keep response payloads minimal. See docs/REST_API.md for a JSON example.

## Math‑Aware Heuristics

To reduce false positives from content inside inline math, several Unicode and quote rules ignore segments delimited by math markers:

- Supported delimiters: `$ ... $`, `\( ... \)`, `\[ ... \]`.
- Affected rules: `TYPO-014` (mixed quotes), `TYPO-031` (mixed dashes), `TYPO-032` (prefer Unicode dashes), `TYPO-033` (mixed ellipsis), `TYPO-001` (ASCII quotes), `TYPO-005` (ASCII ellipsis).

Note: This is a heuristic pass and does not parse nested math environments. Future work may expand this to `\begin{...} ... \end{...}` environments.

## Token Debugging

To inspect how the tokenizer splits your input (useful when tuning spacing/adjacency rules), enable the debug endpoint and post your LaTeX source:

```bash
L0_DEBUG_TOKENS=1 make rest-run
curl -s -X POST http://127.0.0.1:8080/tokens \
  -H 'Content-Type: application/json' \
  -d '{"latex":"A -- \\bf test..."}' | jq .
```

Disable `L0_DEBUG_TOKENS` in production. The endpoint returns 403 when the flag is unset.

Notes
- REST requires the main service to be available (Unix socket `/tmp/l0_lex_svc.sock`) and the ability to bind a local TCP port (default 8080). `make rest-run` builds the REST binary and starts it bound to 8080; `make service-run` starts the main service if needed.
- If you prefer a non-REST path, build the simple CLI and run validators directly on files:
  ```bash
  # Build the CLI
  OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/src/validators_cli.exe
  # Run on a single file
  L0_VALIDATORS=pilot ./_build/default/latex-parse/src/validators_cli.exe corpora/lint/pilot_v1/TYPO-001_quotes.tex
  ```

## Extending the Pilot
- Add a rule in `validators.ml` following the `rule` record pattern
- Append to `rules_pilot` and to `specs/rules/pilot_v1.yaml`
- Add a golden input under `corpora/lint/pilot_v1/`
- Update `docs/RULES_PILOT_TODO.md` checklist as needed
