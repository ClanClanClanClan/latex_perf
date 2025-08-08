# COMPREHENSIVE CLEANUP PLAN

## 🚨 CRITICAL ISSUES IDENTIFIED

### 1. Documentation Chaos
- **20+ performance reports** in root directory with overlapping content
- **80+ total reports** across the project
- Multiple versions of the same information
- Contradictory claims in different files

### 2. Test File Explosion
- **60+ test files** scattered across directories
- Many appear to test the same thing
- No clear organization or naming convention
- Mix of obsolete and current tests

### 3. Directory Structure Issues
- Important files mixed with temporary tests in root
- No clear separation of concerns
- Archive folders contain mix of obsolete and potentially useful content

## 📋 CLEANUP ACTIONS

### Phase 1: Documentation Consolidation

#### Keep These (Authoritative):
1. `CLAUDE.md` - Session instructions
2. `README.md` - Project overview  
3. `SINGLE_SOURCE_OF_TRUTH_PERFORMANCE.md` - Performance reference
4. `CRYSTAL_CLEAR_BUILD_REQUIREMENTS.md` - Build guide
5. `FOOLPROOF_PERFORMANCE_TEST.sh` - Official test script
6. `PROJECT_ORGANIZATION.md` - Directory structure guide

#### Archive These (Historical/Redundant):
All other reports, audits, and status files should move to archive with clear categorization.

### Phase 2: Test File Organization

#### Create Clear Test Structure:
```
test/
├── unit/           # Unit tests for individual components
├── integration/    # Integration tests (L0→L1→L2)
├── performance/    # Performance benchmarks
├── correctness/    # Correctness verification
└── scripts/        # Test runner scripts
```

#### Official Test Files:
- `test/performance/benchmark_l0_arena.ml` - Official L0 benchmark
- `test/integration/test_pipeline.ml` - Official pipeline test
- `test/correctness/verify_tokenization.ml` - Correctness test

### Phase 3: Root Directory Cleanup

#### Move to `docs/`:
- All analysis reports
- All audit documents
- All status updates

#### Move to `archive/performance-investigation-2025-08/`:
- All experimental test files
- All temporary performance tests
- All investigation reports

### Phase 4: Create Master Documentation Index

`docs/INDEX.md` with:
- Current authoritative documents
- Historical documents (archived)
- Test documentation
- Build documentation

## 🎯 END GOAL

### Root Directory Should Contain Only:
- `README.md` - Project overview
- `CLAUDE.md` - AI session instructions
- `Makefile` - Build commands
- `dune-project` - Build configuration
- Essential scripts (setup, build)
- Source directories (src/, test/, docs/, etc.)

### Documentation Structure:
```
docs/
├── INDEX.md                    # Master index
├── current/                    # Current project docs
│   ├── BUILD_GUIDE.md
│   ├── PERFORMANCE_GUIDE.md
│   └── TESTING_GUIDE.md
├── architecture/               # Design docs
├── api/                       # API documentation
└── archive/                   # Historical docs (organized by date/topic)
```

### Test Structure:
```
test/
├── README.md                   # Test overview
├── run_all_tests.sh           # Master test runner
├── unit/
├── integration/
├── performance/
│   ├── benchmark_suite.ml
│   └── results/
└── correctness/
```

## 🚀 IMMEDIATE ACTIONS

1. Create backup: `tar -czf backup-before-cleanup-$(date +%Y%m%d).tar.gz .`
2. Create new directory structure
3. Move files according to plan
4. Update all references in remaining docs
5. Create master INDEX.md
6. Update .gitignore to prevent future mess

## ⚠️ CAUTION

- Preserve all Git history
- Don't delete anything, only move/organize
- Update all internal references
- Test build system after reorganization