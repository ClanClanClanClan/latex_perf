# Architecture Overview

## Two-Project Structure

This repository contains two separate Dune projects sharing a single git repository:

| Project | Root | Package Name | Coq Dependency |
|---------|------|-------------|----------------|
| `latex-perfectionist` | `/` | `latex-perfectionist` | Yes (8.18.0) |
| `latex_parse` | `/latex-parse/` | `latex_parse` | No |

**Why two projects?** The `latex_parse` package is the lightweight runtime —
tokenizer, validators, REST API server, benchmarks. It has no Coq dependency,
making it fast to install and suitable for deployment. The root
`latex-perfectionist` package includes Coq proofs, the L1 expander, and the
formal verification infrastructure.

## Shared Modules (Drift Risk)

The following modules exist in **both** `core/l0_lexer/` and `latex-parse/src/`,
because `latex_parse` cannot depend on `l0_lexer` (which pulls in Coq via the
root dune-project):

```
arena.ml        barrier.ml      broker.ml       catcode.ml
clock.ml        config.ml       fast_hash.ml    fault_injection.ml
gc_prep.ml      hedge_timer.ml  ipc.ml          meminfo.ml
metrics_prometheus.ml  mlock.ml  pretouch.ml    real_processor.ml
service_bracket.ml     simd_guard.ml  worker.ml
```

**⚠ `catcode.ml` has diverged** — the `core/l0_lexer` version delegates to
`Data.Types.Catcode`, while `latex-parse/src` has a standalone implementation.
All other modules are currently identical.

### Keeping them in sync

Until these are consolidated into a shared library (planned architectural work),
any change to a shared module must be applied to both copies. The canonical copy
is `latex-parse/src/` — it is the one that ships in the runtime and is exercised
by all CI tests and benchmarks.

## Layer Architecture

```
L4 (Style)       → core/l4_style/        [Stub — Phase 4]
L3 (Semantics)   → core/l3_semantics/    [Stub — Phase 3]
L2 (Parser)      → latex-parse/src/parser_l2.ml  [Active]
L1 (Expander)    → core/l1_expander/     [Active, proofs QED]
L0 (Lexer)       → core/l0_lexer/ + latex-parse/src/  [Active, proofs QED]
```

## Proof Infrastructure

All formal proofs live in `proofs/` and are built via `(coq.theory)` in
`proofs/dune`. The proof suite enforces zero admits and zero axioms via CI
(`proof-ci` workflow). Archived/superseded proofs are in `proofs/archive/` with
`.disabled` extensions and excluded from the build.

## Build & Test

```bash
# Build everything (both projects + proofs)
dune build @all

# Run all tests
dune runtest

# Build latex-parse only (fast, no Coq)
cd latex-parse && dune build

# Service
dune exec latex-parse/src/main_service.exe

# REST API
dune exec latex-parse/src/rest_api_server.exe
```
