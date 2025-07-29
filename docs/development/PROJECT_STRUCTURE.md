# 📁 PROJECT STRUCTURE
## LaTeX Perfectionist v24-R3: File Organization

### 📋 Overview

This document maps out the complete project structure for the checkpoint-based incremental lexer, showing where existing files should be moved and what new files need to be created.

---

## 🗂️ Directory Structure

```
latex-perfectionist-v24-r3/
│
├── README.md                           # Master project overview
├── TECHNICAL_SPECIFICATION.md          # Consolidated technical spec
├── IMPLEMENTATION_CHECKLIST.md         # Step-by-step tasks
├── PERFORMANCE_BENCHMARKS.md           # Performance data & analysis
├── PROJECT_STRUCTURE.md                # This file
├── LICENSE                             # Project license
│
├── docs/                               # Documentation
│   ├── architecture/
│   │   ├── checkpoint-architecture.md  # Core checkpoint algorithm
│   │   ├── formal-verification.md      # Verification preservation
│   │   ├── python-ffi-bridge.md        # OCaml-Python integration
│   │   └── performance-model.md        # Performance analysis
│   │
│   ├── testing/
│   │   ├── testing-strategy.md         # Test plan
│   │   ├── fuzzing-guide.md            # Equivalence testing
│   │   └── benchmark-guide.md          # Performance testing
│   │
│   ├── api/
│   │   ├── coq-api.md                  # Coq theorem reference
│   │   ├── ocaml-api.md                # OCaml function reference
│   │   └── python-api.md               # Python API reference
│   │
│   └── legacy/                         # Historical documentation
│       ├── failed-optimization.md      # Analysis of wrong approach
│       └── original-specification.md   # User's checkpoint spec
│
├── src/                                # Source code
│   ├── coq/
│   │   └── lexer/
│   │       ├── CoreLexer.v            # [EXISTING] Original verified lexer
│   │       ├── _CoqProject            # [UPDATE] Build configuration
│   │       └── incremental/           # New checkpoint extensions
│   │           ├── StreamChunk.v      # [NEW] Streaming interface
│   │           ├── StateCodec.v       # [NEW] State serialization
│   │           ├── CheckpointTheory.v # [NEW] Checkpoint proofs
│   │           └── IncrementalCorrect.v # [NEW] Main theorem
│   │
│   ├── ocaml/
│   │   ├── extraction/                # Coq extractions
│   │   │   └── .gitkeep
│   │   │
│   │   └── runtime/
│   │       ├── incremental_lexer.ml   # [NEW] Core implementation
│   │       ├── incremental_lexer.mli  # [NEW] Interface
│   │       ├── incremental_ffi.ml     # [NEW] FFI exports
│   │       ├── incremental_ffi.c      # [NEW] C wrapper
│   │       ├── Makefile               # [NEW] Build system
│   │       └── dune                   # [NEW] Dune build file
│   │
│   ├── python/
│   │   ├── validators/                # Existing validators
│   │   │   ├── __init__.py
│   │   │   ├── enhanced_corpus_validator.py  # [MOVE] From root
│   │   │   └── production_validator.py       # [MOVE] From root
│   │   │
│   │   ├── bridge/                    # New Python bridge
│   │   │   ├── __init__.py           # [NEW]
│   │   │   ├── incr_bridge.py        # [NEW] FFI bridge
│   │   │   └── editor_integration.py  # [NEW] High-level API
│   │   │
│   │   ├── analysis/                  # Performance analysis
│   │   │   ├── __init__.py
│   │   │   └── realtime_analysis.py  # [MOVE] From integration/
│   │   │
│   │   ├── setup.py                   # [NEW] Package setup
│   │   └── requirements.txt           # [NEW] Dependencies
│   │
│   └── integration/                   # Integration examples
│       └── examples/
│           ├── simple_example.py      # [NEW] Basic usage
│           └── editor_example.py      # [NEW] Editor integration
│
├── tests/                             # Test suites
│   ├── coq/
│   │   ├── test_checkpoint.v         # [NEW] Coq proof tests
│   │   └── test_serialization.v      # [NEW] Codec tests
│   │
│   ├── ocaml/
│   │   ├── test_incremental.ml       # [NEW] OCaml unit tests
│   │   ├── test_performance.ml       # [NEW] Micro benchmarks
│   │   └── simple_incremental_test.ml # [MOVE] From integration/
│   │
│   ├── python/
│   │   ├── __init__.py
│   │   ├── test_ffi_bridge.py        # [NEW] FFI tests
│   │   ├── test_integration.py       # [NEW] Integration tests
│   │   ├── test_equivalence.py       # [NEW] Fuzzing tests
│   │   ├── benchmark_performance.py  # [NEW] Performance tests
│   │   └── conftest.py               # [NEW] Pytest config
│   │
│   └── fixtures/                      # Test data
│       ├── small.tex                  # Small test file
│       ├── medium.tex                 # 1MB test file
│       └── large.tex                  # 3MB test file
│
├── corpus/                            # Corpus testing system
│   ├── README.md                      # [EXISTING] Corpus documentation
│   ├── build_corpus.py                # [EXISTING] arXiv paper downloader
│   ├── test_corpus.py                 # [EXISTING] Corpus test runner
│   ├── run_corpus_tests.py            # [EXISTING] End-to-end pipeline
│   ├── papers/                        # Downloaded test papers
│   │   └── */                         # Individual paper directories
│   ├── test_results/                  # Test results and benchmarks
│   │   ├── corpus_test_results_*.json
│   │   ├── corpus_benchmark_*.json
│   │   └── corpus_quality_report.json
│   ├── logs/                          # Download and processing logs
│   ├── corpus_metadata.db             # SQLite metadata database
│   └── corpus_stats.json              # Overall corpus statistics
│
├── ci/                                # CI/CD configuration
│   ├── workflows/
│   │   └── incremental-lexer.yml     # [NEW] GitHub Actions
│   │
│   ├── scripts/
│   │   ├── test_coq_proofs.sh        # [NEW] Coq verification
│   │   ├── benchmark.sh               # [NEW] Performance tests
│   │   └── fuzz.sh                    # [NEW] Equivalence testing
│   │
│   └── monitoring/
│       └── performance_dashboard.py   # [NEW] Metrics tracking
│
├── archive/                           # Historical/deprecated files
│   ├── failed_experiments/
│   │   └── lexer_optimized.ml        # [MOVE] Failed O(n) attempt
│   │
│   ├── original_documents/           # Original analysis docs
│   │   ├── REAL_OPTIMIZATION_RESULTS.md      # [MOVE]
│   │   ├── ENTERPRISE_CRISIS_ANALYSIS.json   # [MOVE]
│   │   ├── FORMAL_VERIFICATION_HANDOFF.md    # [MOVE]
│   │   ├── HONEST_COMPREHENSIVE_AUDIT_REPORT.md # [EXISTING]
│   │   └── HONEST_OPTIMIZATION_STATUS_REPORT.md # [EXISTING]
│   │
│   └── phase_summaries/             # Phase completion docs
│       ├── PHASE1_SUCCESS_VALIDATION.py      # [EXISTING]
│       ├── PHASE2_VALIDATION_SUMMARY.md      # [EXISTING]
│       └── PHASE3_PRODUCTION_SUMMARY.md      # [EXISTING]
│
└── tools/                            # Development tools
    ├── setup_dev_env.sh             # [NEW] Development setup
    ├── run_benchmarks.py            # [NEW] Benchmark runner
    └── memory_profiler.py           # [NEW] Memory analysis
```

---

## 🚀 FILE MIGRATION PLAN

### Files to Move

1. **From Root to `archive/original_documents/`**:
   - REAL_OPTIMIZATION_RESULTS.md
   - ENTERPRISE_CRISIS_ANALYSIS.json
   - FORMAL_VERIFICATION_HANDOFF.md
   - COQ_EXTENSIONS_PLAN.md (keep copy for reference)
   - PYTHON_BRIDGE_INTEGRATION.md (keep copy for reference)
   - COMPREHENSIVE_TESTING_CI_STRATEGY.md (keep copy for reference)

2. **From Root to `src/python/validators/`**:
   - enhanced_corpus_validator.py
   - production_validator.py

3. **From `src/integration/python-ocaml/` to appropriate locations**:
   - realtime_analysis.py → `src/python/analysis/`
   - simple_incremental_test.ml → `tests/ocaml/`

4. **Archive Failed Attempts**:
   - lexer_optimized.ml → `archive/failed_experiments/`

### Files to Create

1. **Documentation** (`docs/architecture/`):
   - checkpoint-architecture.md (extract from TECHNICAL_SPECIFICATION.md)
   - formal-verification.md (extract from FORMAL_VERIFICATION_PRESERVATION.md)
   - python-ffi-bridge.md (extract from PYTHON_BRIDGE_INTEGRATION.md)

2. **Build Files**:
   - src/coq/lexer/_CoqProject (update)
   - src/ocaml/runtime/Makefile
   - src/ocaml/runtime/dune
   - src/python/setup.py

3. **Test Infrastructure**:
   - All files in tests/ directory
   - CI workflow files

---

## 📝 DOCUMENTATION CONSOLIDATION

### Master Documents (Root Level)

1. **README.md** - Project overview, quick start, navigation
2. **TECHNICAL_SPECIFICATION.md** - Complete technical design
3. **IMPLEMENTATION_CHECKLIST.md** - Task tracking
4. **PERFORMANCE_BENCHMARKS.md** - All performance data

### Detailed Documentation (`docs/`)

Extract and organize content from original documents:

- **checkpoint-architecture.md**: Core algorithm details
- **formal-verification.md**: Proof strategy and theorems
- **python-ffi-bridge.md**: FFI implementation details
- **testing-strategy.md**: Comprehensive test plan

### API Documentation (`docs/api/`)

Generate from source code:
- Coq theorems and definitions
- OCaml function signatures
- Python class/method documentation

---

## 🔧 BUILD SYSTEM ORGANIZATION

### Coq Build
```
src/coq/lexer/_CoqProject:
-R . LaTeXPerfectionist
CoreLexer.v
incremental/StreamChunk.v
incremental/StateCodec.v
incremental/CheckpointTheory.v
incremental/IncrementalCorrect.v
```

### OCaml Build
```
src/ocaml/runtime/dune:
(library
 (name incremental_lexer)
 (public_name latex-perfectionist.incremental)
 (foreign_stubs
  (language c)
  (names incremental_ffi)))
```

### Python Build
```
src/python/setup.py:
setup(
    name="latex_perfectionist_incremental",
    packages=find_packages(),
    package_data={'': ['*.so']},
)
```

---

## 🎯 NEXT STEPS

1. **Create directory structure**:
   ```bash
   mkdir -p docs/{architecture,testing,api,legacy}
   mkdir -p src/{coq/lexer/incremental,ocaml/{extraction,runtime},python/{validators,bridge,analysis}}
   mkdir -p tests/{coq,ocaml,python,fixtures}
   mkdir -p ci/{workflows,scripts,monitoring}
   mkdir -p archive/{failed_experiments,original_documents,phase_summaries}
   mkdir -p tools
   ```

2. **Move existing files** according to migration plan

3. **Extract documentation** into organized structure

4. **Create placeholder files** for new components

5. **Update imports/references** in moved files

---

## ✅ BENEFITS OF THIS STRUCTURE

1. **Clear separation** of concerns (Coq/OCaml/Python)
2. **Preserves history** in archive/
3. **Organized documentation** by topic
4. **Standard project layout** for each language
5. **Easy navigation** for new developers
6. **CI/CD ready** structure

---

**📁 This structure provides a clean, organized foundation for implementing the checkpoint-based incremental lexer while preserving all historical work.**