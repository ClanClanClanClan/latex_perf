# Build System Guide

Complete guide to building, testing, and running LaTeX Perfectionist v25.

## Prerequisites

### Required Dependencies
- **OCaml**: >= 5.1.1
- **Dune**: >= 3.10  
- **OPAM**: Package manager with switch `l0-testing`
- **Coq**: = 8.18.0 (for formal verification)

### Optional Dependencies
- **Coq Core**: = 8.18.0
- **External Libraries**: yojson, ppx_deriving, angstrom, uutf

### Platform Support
- **Primary**: macOS Apple Silicon (ARM64) with NEON SIMD
- **Secondary**: Linux x86_64 with AVX2 support
- **Build System**: Dune 3.10+ with C foreign function interface

## Quick Start

### Initial Setup
```bash
# Ensure OPAM switch is active
opam switch list
eval $(opam env --switch=l0-testing)

# One-shot environment setup (creates l0-testing and installs deps)
./scripts/setup_env.sh

# Validate environment versions match (OCaml 5.1.1, Coq 8.18, dune ≥ 3.10)
./scripts/check_env.sh

# Build entire project
make build

# Run comprehensive verification
make verify FILE=corpora/perf/perf_smoke_big.tex
```


### Core Build Commands

#### Primary Builds
```bash
# Build all components
OPAMSWITCH=l0-testing opam exec -- dune build @all

# Build SIMD service
OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/src/main_service.exe

# Build benchmarking tools
OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/ab_microbench.exe
OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/run_service_bench_concurrent.exe
```

#### Formatting
```bash
# Format OCaml sources using ocamlformat via dune
make fmt
```

#### Verification Tools
```bash
# Build verification suite
OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/time_selftest.exe
OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/ipc_propcheck.exe
```

If you see a "yojson.cmi … older OCaml" error:
```bash
opam reinstall -y yojson dune
# Or resolve via lockfile:
opam install -y . --deps-only --locked
```

## Makefile Targets

### Development Workflow
```bash
# Complete build (parallel, 8 jobs)
make build

# Clean build artifacts
make clean

# Full verification suite
make verify FILE=/path/to/test.tex

# Service management
make service-run    # Start SIMD service
make service-stop   # Stop service

# Format OCaml source
make fmt
```

### Testing and Validation
```bash
# Comprehensive CI testing (100K iterations)
make ci FILE=corpora/perf/perf_smoke_big.tex THREADS=4

# Performance gate validation
make gate OUT=/path/to/output.txt

# Long-running soak test (1 hour)
make soak FILE=corpora/perf/perf_smoke_big.tex
```

### Makefile Configuration Variables
```bash
FILE ?= /tmp/perf_smoke_big.tex     # Test input file
J ?= 8                              # Parallel build jobs  
THREADS ?= 4                        # Test thread count
NREQ ?= 100000                      # Number of requests for CI
HEDGE ?= 10                         # Hedge timeout (ms)
AB_ITERS ?= 100000                  # A+B benchmark iterations
AB_WARMUP ?= 512                    # Warmup iterations
```

## Project Structure

### Source Hierarchy
```
latex-parse/
├── src/                     # Active SIMD service runtime
│   └── *.ml / *.c            # Hedge broker, worker pool, SIMD stubs
├── bench/                   # Performance harnesses
└── dune                     # Build configuration
```

### Supporting Components
```
core/                        # Legacy prototypes; L0 builds via core/l0_lexer/dune (others keep dune.disabled backup)
proofs/                      # CoreProofs.v + archive/
data/                        # Shared token/location types
corpora/                     # Test datasets (perf_smoke_big, edit_window_4kb, etc.)
specs/                       # Technical specifications
docs/                        # Documentation
```

## Performance Testing

Bench CLI recap:
- `ab_microbench FILE ITERS [--warmup N] [--csv PATH]`
- Defaults: warmup 512 iterations; use `--csv` to emit a summary row (label,min,p50,p95,p99,p999,max).

### Quick Validation
```bash
# 10K iteration test (2-3 minutes)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 10000 --csv /tmp/ab_microbench.csv
```

### Production Validation  
```bash
# 100K iteration test (30-45 minutes)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 100000 --csv /tmp/ab_microbench.csv
```

### Comprehensive Testing
```bash
# 1M iteration test (1-2 hours)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 1000000 --csv /tmp/ab_microbench.csv
```

### Edit-window Benchmark (4 KB)
```bash
# 5K iteration edit-window run (~seconds)
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/edit_window_bench.exe \
  corpora/perf/edit_window_4kb.tex 5000 --csv /tmp/edit_window_bench.csv

# Gate: ensures p95 ≤ 1.2 ms
OPAMSWITCH=l0-testing opam exec -- \
  bash scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000
```

### Incremental Edit Replay (4 KB window)
```bash
# 2K edit replay (inserts/deletes) with per-edit window processing
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/edit_replay_bench.exe \
  corpora/perf/edit_window_4kb.tex 2000 --window 4096 --csv /tmp/edit_replay_2k.csv
```

### A/B Comparison (Direct vs Service Keepalive)
```bash
OPAMSWITCH=l0-testing opam exec -- bash scripts/ab_compare.sh corpora/perf/perf_smoke_big.tex 10000
```

### L1 Expander (opt-in, feature branch)
```bash
# Enable L1 locally (copies dune.disabled → dune)
OPAMSWITCH=l0-testing opam exec -- bash scripts/enable_l1.sh

# Build L1 and the test scaffold
OPAMSWITCH=l0-testing opam exec -- dune build core/l1_expander

# Run the L1 A/B test scaffold (placeholder)
./_build/default/core/l1_expander/l1_ab_test.exe corpora/perf/edit_window_4kb.tex
```

## Service Deployment

### Manual Service Control
```bash
# Start with TCP Prometheus (default 127.0.0.1:9109)
L0_PROM=1 L0_PROM_ADDR=127.0.0.1:9109 L0_POOL_CORES=0,1,2,3 \
  ./_build/default/latex-parse/src/main_service.exe &

# Service listens on Unix socket
ls -la /tmp/l0_lex_svc.sock

# Stop service
pkill -f main_service
```

### REST Façade (optional)
```bash
# Start REST server (requires service on /tmp/l0_lex_svc.sock)
make rest-run

# Smoke test (POST /tokenize)
make rest-smoke

# Stop REST server
make rest-stop
```

### Environment Variables
- `L0_PROM=1`: Enable Prometheus metrics
- `L0_PROM_ADDR=HOST:PORT`: Bind address (default `127.0.0.1:9109`)
- `L0_PROM_UDS=/tmp/l0_prom.sock`: Serve metrics over a Unix domain socket (restricted environments)
- `L0_POOL_CORES=0,1,2,3`: CPU core affinity for workers
- Service socket: `/tmp/l0_lex_svc.sock`

## Troubleshooting

### Common Build Issues
```bash
# OPAM switch not active
eval $(opam env --switch=l0-testing)

# Missing dependencies
opam install --deps-only ./latex-perfectionist.opam

# Stale build artifacts
make clean && make build
```

### Performance Issues
```bash
# Verify SIMD support
./_build/default/latex-parse/bench/time_selftest.exe

# Check service health
./_build/default/latex-parse/bench/ipc_propcheck.exe

# Monitor service telemetry
tail -f /tmp/l0_service_tail.csv
```

### Test Data Issues
```bash
# Verify test file exists
ls -la corpora/perf/perf_smoke_big.tex

# File size check
wc -c corpora/perf/perf_smoke_big.tex
# Expected: ~1.1MB LaTeX content
```

## Integration Testing

### Automated Testing Pipeline
```bash
# Full verification suite (as used in CI)
make verify FILE=corpora/perf/perf_smoke_big.tex

# Expected output:
# [verify] time selftest: PASS
# [verify] IPC propcheck: PASS  
# [verify] A+B microbench: PASS
# [verify] Service 10K: PASS
# [verify] Service 4K concurrent: PASS
```

### Performance Gates
The build system includes automated performance gates:
- P50 latency ≤ 20ms
- P99 latency ≤ 20ms
- Error rate = 0%
- Service startup < 1s

## Development Workflow

### Recommended Development Cycle
1. **Code Changes**: Edit source files
2. **Build**: `make build` 
3. **Quick Test**: 10K iteration validation
4. **Service Test**: `make verify`
5. **Production Test**: 100K iteration validation
6. **Commit**: When all tests pass

### Hot Reloading
```bash
# Watch for changes and rebuild
find latex-parse/ -name "*.ml" -o -name "*.c" | \
  entr -c make build
```

This build system provides comprehensive coverage from development through production deployment with automated performance validation and service management.
#### SIMD xxHash (optional)
```bash
# Enable AVX2 lane (if supported)
make hash-bench-avx2   # uses CFLAGS="-DENABLE_XXH_AVX2 -mavx2" and L0_USE_SIMD_XXH=1

# Enable NEON lane (if supported)
make hash-bench-neon   # uses CFLAGS="-DENABLE_XXH_NEON" and L0_USE_SIMD_XXH=1

# Optional gates (non-blocking by default)
make hash-gate ENABLE_HASH_GATE=1 THRESH_MBPS=500.0 \
               ENABLE_HASH_GATE_XXH=1 THRESH_MBPS_XXH=1000.0 L0_USE_SIMD_XXH=1
```
