# LaTeX Perfectionist v25

**Week 1 Foundation** - Formally verified LaTeX style validator with 0 admits achieved.

LaTeX Perfectionist v25 is a comprehensive LaTeX document analysis and style validation system built using formal verification techniques. We're currently in Week 1 of the 156-week development timeline (started July 28, 2025).

## Current Status (Week 1)

- **Formal Verification**: ✅ 0 admits achieved (Week 1 target)
- **Architecture**: 5-layer VSNA processing + validation framework
- **Performance**: 🔄 L0 lexer optimization needed (14.07ms current, targets: 4ms/2ms/1ms)
- **Validators**: 80/623 implemented (foundation phase)

## Quick Start

```bash
# Build system
make build                    # OCaml components via dune
make build-direct            # Direct compilation (avoids dune Thread issue)
make coq                     # Coq proofs and verification

# Performance testing
make test-perf               # Run L0 lexer performance tests
```

## Architecture

- **src/core/**: L0 lexer, L1 expander, validation framework
- **src/data/**: Token types, data structures, location tracking  
- **proofs/**: Formal verification proofs (0 admits)
- **specs/**: Technical specifications and project timeline

## Documentation

- **CLAUDE.md**: Project instructions and current status
- **docs/current/**: Week 1 handoff documents
- **specs/PLANNER.yaml**: 156-week project timeline

This repository represents the foundational work for a production-ready LaTeX validation system with formal correctness guarantees.