# LaTeX Perfectionist v25 - Project Organization

*Updated: August 8, 2025 - Comprehensive Reorganization Complete*

## 📂 Directory Structure

```
latex-perfectionist-v25/
├── src/                    # Source code
│   ├── core/              # Core OCaml implementation
│   │   ├── l0_lexer_track_a_arena.ml  # L0 lexer (8.36ms median, 12.92ms P95)
│   │   ├── l1_expander.ml             # L1 macro expander
│   │   ├── l2_parser.ml               # L2 parser
│   │   └── lexer/                     # Coq lexer proofs
│   └── data/              # Shared data types
├── test/                  # Test suite (ORGANIZED)
│   ├── README.md         # Test documentation
│   ├── unit/             # Unit tests
│   ├── integration/      # Integration tests
│   ├── performance/      # Performance benchmarks
│   ├── correctness/      # Correctness tests
│   └── scripts/          # Test runners
│       └── FOOLPROOF_PERFORMANCE_TEST.sh  # Official perf test
├── docs/                  # Documentation (ORGANIZED)
│   ├── INDEX.md          # Master documentation index
│   ├── current/          # Active documentation
│   │   ├── build/        # Build guides
│   │   ├── performance/  # Performance guides
│   │   └── testing/      # Testing guides
│   ├── reports/          # Project reports
│   └── archive/          # Historical docs
│       └── performance-investigation-2025-08/  # Aug 2025 perf work
├── scripts/               # Build and utility scripts
│   ├── build/            # Build scripts
│   │   ├── DUNE_ALTERNATIVE_BUILD.sh  # Working build system
│   │   └── BUILD_SUCCESS_VERIFICATION.sh
│   └── cleanup/          # Maintenance scripts
├── specs/                 # Specifications
│   ├── v25_master.md     # Master specification
│   ├── L0_LEXER_SPEC.md  # L0 spec (≤20ms target)
│   └── PLANNER.yaml      # 156-week timeline
├── proofs/               # Coq proofs
├── archive/              # Historical/obsolete files
└── corpora/              # Test corpora
    └── perf/             # Performance test files
        └── perf_smoke_big.tex  # 1.1MB test file
```

## 🗑️ What Got Cleaned Up

### Before (Chaos)
- **Root directory**: 20+ performance reports, 60+ test files
- **Documentation**: Contradictory claims about performance
- **Test files**: Scattered across root and subdirectories
- **Build artifacts**: Mixed with source files

### After (Organized)
- **Root directory**: Only essential files (README, CLAUDE, Makefile)
- **Documentation**: Clear hierarchy, single source of truth
- **Test files**: Organized in `test/` with clear categories
- **Scripts**: Organized by purpose in `scripts/`

## 📍 Where to Find Things

### Essential Files
| What | Where | Purpose |
|------|-------|---------|
| Performance test | `test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh` | Official L0 performance verification |
| Build guide | `docs/current/build/BUILD_REQUIREMENTS.md` | Flambda2 requirements |
| Performance truth | `docs/archive/performance-investigation-2025-08/SINGLE_SOURCE_OF_TRUTH_PERFORMANCE.md` | Official numbers |
| Project status | `CLAUDE.md` | Current Week 1 status |
| Documentation index | `docs/INDEX.md` | Master list of all docs |

### Performance Investigation (Aug 2025)
All performance investigation reports moved to:
`docs/archive/performance-investigation-2025-08/`

Including:
- All HONEST/TRUTH/REALITY reports
- All AUDIT/STATUS reports
- All performance test results
- Investigation conclusions

## 🚀 Quick Commands

```bash
# Run official performance test (MUST USE THIS)
./test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh

# Build with alternative system (bypasses dune issues)
./scripts/build/DUNE_ALTERNATIVE_BUILD.sh

# Run all tests
make test

# Check documentation
cat docs/INDEX.md
```

## 🔑 Key Facts (Don't Forget!)

### L0 Lexer Performance
- **Target**: ≤20ms on 1.1MB file
- **Standard OCaml**: 39.28ms ❌
- **Flambda2 + GC tuning**: 8.36ms median, 12.92ms P95 ✅
- **Critical**: MUST use Flambda2 compiler!

### Build Requirements
```bash
# Create Flambda2 switch (REQUIRED)
opam switch create flambda2-lexer ocaml-variants.5.1.1+flambda2

# Compile with ALL flags
OPAMSWITCH=flambda2-lexer opam exec -- ocamlopt \
  -O3 -inline 100 -unbox-closures -rounds 4 -unsafe \
  -o lexer unix.cmxa l0_lexer_track_a_arena.ml
```

## 🧹 Maintenance Guidelines

### Adding New Files
- **Tests**: Place in appropriate `test/` subdirectory
- **Docs**: Active docs in `docs/current/`, old ones in `docs/archive/`
- **Scripts**: `scripts/build/` or `scripts/cleanup/`
- **Never**: Place test executables or reports in root

### Archive Policy
- Move investigation reports to `docs/archive/[topic]-[date]/`
- Keep only current, accurate documentation in `docs/current/`
- Delete truly obsolete files after backing up

### .gitignore Updated
Now excludes:
- Build artifacts in root (`/test_*`, `/debug_*`, `/*.o`)
- Test executables
- Temporary files

---

## 📋 Summary

The project is now properly organized with:
- ✅ Clean root directory
- ✅ Organized test suite
- ✅ Clear documentation hierarchy
- ✅ Consistent performance claims
- ✅ Working build system
- ✅ Proper .gitignore

All performance investigation work from August 2025 has been archived but preserved for reference.

*Organization completed: August 8, 2025*