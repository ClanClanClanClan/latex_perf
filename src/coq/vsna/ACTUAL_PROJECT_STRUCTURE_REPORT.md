# Actual Project Structure Report
Generated: 2025-07-20

## Executive Summary

This report documents the ACTUAL state of the LaTeX Validator v24 project structure, focusing on what truly exists versus what documentation claims.

## 1. Core Directory Structure

### Working Directory
- **Location**: `/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/src/coq/vsna/`
- **Git Status**: On branch `dfa-prototype`, files untracked

### Actual Directory Layout
```
/Scripts/
├── src/
│   ├── coq/
│   │   ├── vsna/           # Current working directory
│   │   ├── dfa/           # DFA experiments
│   │   └── extraction/    # Coq extraction
│   ├── core/              # Core components
│   │   ├── expander/
│   │   ├── lexer/
│   │   └── validation/
│   ├── rules/             # Rule definitions
│   ├── ocaml/             # OCaml implementation
│   ├── migration/         # Migration scripts
│   └── organized/         # Organized components
├── tests/                 # Test suites
├── corpus/                # Test documents
├── rules/                 # Rule files
├── docs/                  # Documentation
└── archive/               # Historical files
```

## 2. Coq Files Status

### Compiled Coq Files (.vo present)

#### In vsna directory:
- ✅ Compiler.v
- ✅ Core.v
- ✅ Correctness.v
- ✅ DFA.v
- ✅ Performance.v
- ✅ SymbolTable.v
- ✅ UVSNA.v
- ✅ UVSNA_CARC.v
- ✅ VPA.v

#### In other directories:
- ✅ src/coq/dfa/ExtractVNV2.v
- ✅ src/coq/dfa/SimpleRegexDFA.v
- ✅ src/coq/extraction/Extract.v
- ✅ src/core/expander/ExpanderCompat.v
- ✅ src/core/expander/LatexExpanderFix.v
- ✅ src/core/lexer/CatcodeAnalysis.v
- ✅ src/core/lexer/LatexCatcodes.v
- ✅ src/core/lexer/LatexLexer.v
- ✅ src/core/lexer/LatexLexerProofs.v
- ✅ src/core/validation/ValidationRules.v
- ✅ src/core/validation/ValidationTypes.v
- ✅ src/rules/phase1/CommandRules.v
- ✅ src/rules/phase1/RuleTests.v
- ✅ src/rules/phase1/TypoRules.v

### Uncompiled Coq Files (only .v, no .vo)
- ❌ Many files in src/core/expander/ (Enhanced, Optimized, Refactored, UltraOptimized versions)
- ❌ Files in src/rules/enhanced/
- ❌ Files in src/rules/migrated/
- ❌ Files in src/rules/phase1_5/
- ❌ Files in src/rules/proofs/

## 3. Executable Files

### Working Executables Found:
```
/src/coq/dfa/test_extracted
/src/coq/dfa/test_single
/src/coq/dfa/test_vnv2
/src/extraction/debug_slow_rule
/src/extraction/enterprise_optimized
/src/extraction/test_document_parallel_native
/src/extraction/test_domains
/src/extraction/test_enterprise
/src/extraction/test_enterprise_adaptive
/src/extraction/test_enterprise_native
/src/extraction/test_enterprise_streaming
/src/extraction/test_enterprise_streaming_native
/src/extraction/test_optimized_no_slow
/src/extraction/test_simple_parallel_native
/src/extraction/test_ultra_fast_native
/src/extraction/verify_filter
/src/ocaml/bin/carc_main
/src/ocaml/bin/corpus_test
/src/ocaml/bin/perf_test
/src/ocaml/lib/latex_validator
/src/ocaml/lib/latex_validator_brackets
/src/ocaml/lib/latex_validator_fixed
/src/ocaml/lib/latex_validator_optimized
/src/ocaml/lib/test
/src/ocaml/lib/test_rule_loader
/src/ocaml/lib/test_vsna
/src/ocaml/test_load
/src/ocaml/test_rule_loader_simple
```

## 4. Test Infrastructure

### Test Organization:
- **Unit Tests**: `/tests/unit/` - Contains many .v files, some compiled
- **Integration Tests**: `/tests/integration/` - Contains HELL_LEVEL tests
- **Performance Tests**: `/tests/performance/`
- **Corpus Tests**: `/tests/corpus_test/` - Contains 50 test papers with metadata

### Notable Test Files:
- HELL_LEVEL_TESTS.v variations
- EXTREME_PARANOID_TESTS.v
- Various rule validation tests
- OCaml test executables

## 5. Corpus Directory

### Structure:
- **Papers**: `/corpus/papers/` - Contains LaTeX source files
- **Ground Truth**: `/corpus/ground_truth/` - JSON files with expected results
- **Metadata**: `/corpus/metadata/` - JSON metadata for papers
- **Scripts**: Multiple Python scripts for corpus processing

### Key Files:
- `enterprise_corpus_summary.json`
- `corpus_stats.json`
- `corpus_metadata.db`
- Various validation and collection scripts

## 6. Rules Directory

### Contents:
- `rules_unified.yaml` - Main rules file
- `rules_v2.yaml` - Version 2 rules
- `rules.yaml` - Basic rules
- `/phase1/` - Contains CommandRules.v, TypoRules.v, RuleTests.v
- `/phase1_5/` - Contains PostExpansionRules.v

## 7. Documentation

### Key Documentation Files Found:
- README.md (main)
- PROJECT_STRUCTURE.md
- PROJECT_MASTER_PLAN.md
- CURRENT_STATUS_VERIFIED.md
- QUICK_START.md
- Various architecture and planning documents

### Documentation Directories:
- `/docs/vsna-core/` - VSNA specific documentation
- `/docs/architecture/` - Architecture documentation
- `/docs/implementation/` - Implementation guides

## 8. Build System

### Build Files:
- Makefile
- Makefile.vsna
- Makefile.corpus
- _CoqProject
- _CoqProject.vsna
- dune-project
- automated_verification.sh
- build_ocaml.sh

## 9. Notable Findings

### What EXISTS:
1. **Core VSNA Coq modules** - Compiled
2. **Extensive test infrastructure** - Multiple levels of testing
3. **Large corpus** - 8,604 papers claimed, substantial corpus present
4. **Multiple executables** - Various validators and test tools
5. **Rule systems** - Multiple rule formats and organizations

### What's MISSING or UNCLEAR:
1. **No src/ directory directly in vsna/** - Despite documentation claims
2. **No tests/ or corpus/ in vsna/** - These are at higher levels
3. **tools/carc/** - Exists but appears empty
4. **benchmarks/** - Not found in expected location
5. **Many uncompiled Coq files** - Suggesting partial development

### Discrepancies:
1. Documentation claims more organized structure than exists
2. Many experimental files (Enhanced, Optimized, etc.) suggest iterative development
3. Multiple validation approaches exist simultaneously
4. Directory structure is more complex than documented

## 10. Recommendations

1. **Consolidate Structure**: The actual structure differs significantly from documentation
2. **Finish Compilation**: Many Coq files are not compiled
3. **Clean Up Experiments**: Multiple versions of similar files suggest experimentation
4. **Update Documentation**: Align documentation with actual structure
5. **Organize Test Suite**: Tests are scattered across multiple locations

## Conclusion

The project contains substantial work but differs significantly from its documented structure. The core VSNA modules are compiled and present, along with extensive testing infrastructure and corpus. However, the organization is more complex and experimental than the clean structure described in documentation.