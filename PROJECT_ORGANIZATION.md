# LaTeX Perfectionist v25 - Project Organization

*Updated: August 7, 2025 - Post Comprehensive Cleanup*

## 📁 Core Directory Structure

```
├── src/                          # Source code
│   ├── core/                     # Core lexer implementations  
│   │   ├── l0_lexer*.ml         # L0 lexer variants (Enhanced, Perfect, Ultra)
│   │   ├── lexer/               # Lexer components and proofs
│   │   ├── expander/            # L1 expansion components
│   │   ├── performance/         # Performance integration
│   │   ├── validation/          # Validation rules
│   │   └── track_b/             # C/SIMD implementation
│   ├── data/                     # Data structures and types
│   └── proofs/                   # Formal verification
├── test/                         # All tests
│   ├── performance/              # Performance benchmarks
│   └── *.ml                     # Unit and integration tests
├── specs/                        # Specifications and requirements
├── docs/                         # Documentation
├── corpora/                      # Test corpus files
└── archive/                      # Historical files and artifacts
```

## 🎯 Key Components

### Performance Testing
- `test/performance/BULLETPROOF_1MB_TEST.ml` - Reliable 1.1MB performance test
- `test/performance/COMPREHENSIVE_PERFORMANCE_TEST.ml` - Multi-size analysis
- `run_performance_tests.sh` - Automated performance testing

### Build System
- `build_clean.sh` - Clean build script with environment setup
- `dune-project` - Main dune configuration
- Individual `dune` files in each directory

### Core Implementations
- `src/core/l0_lexer_track_a_enhanced.ml` - Advanced optimizations
- `src/core/l0_lexer_track_a_perfect.ml` - Baseline optimizations  
- `src/core/l0_lexer.ml` - Main interface

## ✅ Cleanup Completed

- ✅ Build artifacts cleaned and organized
- ✅ Performance tests consolidated  
- ✅ Archive structure simplified
- ✅ Dune configuration validated
- ✅ Build scripts created
- ✅ Project structure standardized

## 🚀 Quick Start

```bash
# Build everything
./build_clean.sh

# Run performance tests  
./run_performance_tests.sh

# Build specific components
dune build src/core/
dune build test/
```
