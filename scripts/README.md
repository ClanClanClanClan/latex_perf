# Scripts

## CI-referenced (run by GitHub Actions workflows)

| Script | Workflow |
|--------|----------|
| `perf_gate.sh` | `perf-nightly.yml`, `performance-gate.yml` |
| `perf_summary.sh` | `perf-nightly.yml` |
| `rest_smoke.sh` | `rest-smoke.yml` |
| `smoke_rules_pilot.sh` | `validators-pilot-smoke.yml` |
| `smoke_rules_pilot_cli.sh` | `validators-pilot-smoke-cli.yml` |
| `latency_smoke_expand.sh` | `latency-nightly.yml` |
| `proxy_smoke.py` | `rust-proxy-smoke.yml` |
| `validate_catalogue.sh` | `catalogue-compliance.yml` |
| `validate_messages.sh` | `messages-validate.yml` |

## Makefile targets

| Script | Make target |
|--------|-------------|
| `ab_compare.sh` | `make soak` |
| `perf_gate.sh` | `make gate`, `make verify_r1` |
| `prom_smoke.sh` | `make prom-smoke` |
| `run_all_gates.sh` | `make ci` |
| `build_simd.sh` | `make build-simd` |

## Local/manual use

Development helpers, benchmarking, and cleanup utilities not tied to CI.
