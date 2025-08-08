# LaTeX Perfectionist v25 - Documentation Index

## 📚 Essential Documentation

### Getting Started
- [`README.md`](../README.md) - Project overview and quick start
- [`CLAUDE.md`](../CLAUDE.md) - AI assistant session instructions
- [`PROJECT_ORGANIZATION.md`](../PROJECT_ORGANIZATION.md) - Directory structure guide

### Build & Performance
- [`docs/current/build/BUILD_REQUIREMENTS.md`](current/build/BUILD_REQUIREMENTS.md) - **CRITICAL**: Flambda2 compiler requirements
- [`docs/archive/performance-investigation-2025-08/SINGLE_SOURCE_OF_TRUTH_PERFORMANCE.md`](archive/performance-investigation-2025-08/SINGLE_SOURCE_OF_TRUTH_PERFORMANCE.md) - Official performance numbers
- [`test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh`](../test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh) - Performance verification script

### Architecture & Design
- [`specs/v25_master.md`](../specs/v25_master.md) - v25 master specification
- [`specs/L0_LEXER_SPEC.md`](../specs/L0_LEXER_SPEC.md) - L0 lexer specification (≤20ms target)
- [`specs/PLANNER.yaml`](../specs/PLANNER.yaml) - Project timeline (156 weeks)

## 📂 Documentation Structure

### `/docs/current/` - Active Documentation
- **build/** - Build guides and requirements
- **performance/** - Performance guides and benchmarks
- **testing/** - Testing guides and procedures
- **architecture/** - System design documentation

### `/docs/reports/` - Project Reports
- **build-system/** - Build system analysis
- **performance/** - Performance analysis reports
- **project-status/** - Status updates and audits

### `/docs/archive/` - Historical Documentation
- **performance-investigation-2025-08/** - Performance investigation (August 2025)
- **historical/** - Older project documentation
- **obsolete_reports/** - Superseded reports

## 🧪 Test Documentation

### Test Structure
```
test/
├── README.md           # Test overview
├── unit/              # Unit tests
├── integration/       # Integration tests
├── performance/       # Performance benchmarks
├── correctness/       # Correctness verification
└── scripts/           # Test runner scripts
```

### Key Test Scripts
- `test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh` - Official L0 performance test
- `test/scripts/run_performance_tests.sh` - General performance suite

## 🔑 Key Facts

### L0 Lexer Performance
- **Target**: ≤20ms on 1.1MB file
- **Standard OCaml**: 31.40ms ❌
- **With Flambda2**: 17-18ms ✅
- **Critical**: MUST use Flambda2 compiler

### Project Status (Week 1)
- **Timeline**: Week 1 of 156 (started July 28, 2025)
- **Admits**: 0 (goal achieved)
- **Validators**: 80/623 implemented
- **Performance**: Target achievable with Flambda2

### Build Requirements
```bash
# Create Flambda2 switch (REQUIRED)
opam switch create flambda2-lexer ocaml-variants.5.1.1+flambda2

# Compile with optimization flags
OPAMSWITCH=flambda2-lexer opam exec -- ocamlopt \
  -O3 -inline 100 -unbox-closures -rounds 4 -unsafe \
  -o lexer unix.cmxa l0_lexer_track_a_arena.ml
```

## 🗂️ Archive Policy

Documents are archived when:
- They contain outdated information
- They've been superseded by newer documents
- They're investigation/debug reports
- They're from previous project versions

Always check `/docs/current/` first for the latest information.

## 📋 Quick Reference

### Need to...
- **Build the project?** → See [`BUILD_REQUIREMENTS.md`](current/build/BUILD_REQUIREMENTS.md)
- **Test performance?** → Run [`FOOLPROOF_PERFORMANCE_TEST.sh`](../test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh)
- **Understand architecture?** → Read [`v25_master.md`](../specs/v25_master.md)
- **Check timeline?** → See [`PLANNER.yaml`](../specs/PLANNER.yaml)

---

*Last updated: August 8, 2025*