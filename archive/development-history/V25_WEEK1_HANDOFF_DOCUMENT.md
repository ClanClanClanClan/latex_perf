# LaTeX Perfectionist v25 Week 1 → Week 2 Handoff Document

**CRITICAL**: This document provides the other AI with complete context for continuing v25 development without breaking existing v24 validation rules.

---

## 🏗️ **ARCHITECTURE OVERVIEW**

### Current State: Hybrid v24/v25 System
- **v24 Validation Rules**: 499 rules across L0-L4 processing stages ✅ **MUST PRESERVE**
- **v25 Foundation**: New L0 Lexer + L1 Expander implementation ✅ **NEARLY COMPLETE**
- **Integration Strategy**: v25 provides verified foundation, v24 rules run on top

### File Organization Status
```
src/core/
├── lexer/           # v25 L0 Lexer (6 files, all ✅ compiled)
├── expander/        # v25 L1 Expander (9 files, 8/9 ✅ compiled)
├── validation/      # Current validation engine 
└── lexer/v24r3/    # ⚠️ Legacy v24 files (contains 2 axioms - IGNORE)

src/rules/
├── migrated/        # v24 rules in new format
├── enhanced/        # Enhanced v24 rules  
└── phase1_5/        # Post-expansion rules

docs/specifications/rules/
└── rules_unified.yaml  # 499 validation rules specification
```

---

## ✅ **WEEK 1 ACHIEVEMENTS (L0 + L1 Foundation)**

### L0 Lexer - **COMPLETE** (6/6 files compiled, 0 admits)
- `LatexLexer.v` - Core lexer implementation ✅
- `LatexCatcodes.v` - Category code handling ✅  
- `LatexLexerProofs.v` - Formal verification ✅
- `IncrementalLatexLexer.v` - Incremental processing ✅
- `IncrementalLexerExtraction.v` - OCaml extraction ✅
- `CatcodeAnalysis.v` - Analysis functions ✅

### L1 Expander - **NEARLY COMPLETE** (8/9 files compiled, 0 admits)
✅ **COMPILED:**
- `ExpanderTypes.v` - Core types and definitions
- `MacroCatalog.v` - 76 built-in macros
- `ExpanderAlgorithm.v` - Expansion logic
- `ExpanderProofsSimplified.v` - Basic proofs
- `ExpanderTests.v` - Test cases
- `IntegrationTests.v` - Integration verification
- `PerformanceTests.v` - Performance validation
- `Layer02Verified.v` - Layer integration

❌ **REMAINING ISSUE:**
- `ExpanderProofsFinal.v` - Complex formal proofs (compilation fails due to import issues)

---

## 🎯 **CRITICAL: ONE REMAINING ISSUE**

### Problem: ExpanderProofsFinal.v Won't Compile
**File**: `src/core/expander/ExpanderProofsFinal.v`  
**Status**: Contains original complex proofs but has import path issues  
**Impact**: Prevents 100% completion of Week 1 L1 layer

### What's in This File (CRITICAL SAFETY PROPERTIES):
1. `expand_no_teof` - Prevents TEOF token corruption during expansion
2. `expand_fuel_monotonic` - Fuel monotonicity guarantees  
3. `expand_fuel_insensitive` - Result independence from fuel amount
4. `expand_terminates_acyclic` - Termination guarantee for valid input

### Why It Matters:
These are not trivial theorems - they provide **essential safety guarantees** for the macro expansion system. The file was restored to original complex proofs during this session to preserve formal verification integrity.

---

## 🚨 **WHAT MUST NOT BE BROKEN**

### 1. V24 Validation Rules (499 rules)
- **Location**: `docs/specifications/rules/rules_unified.yaml`
- **Implementation**: Files in `src/rules/migrated/` and `src/rules/enhanced/`
- **Categories**: ACCESS, DELIM, ENVIRON, MATH, REF, TYPO, etc.
- **Status**: ✅ **WORKING** (successfully reduced false positives from 99.8% to 0.74%)

### 2. V24 Validation Engine  
- **Location**: `src/core/validation/ValidationRules.v`
- **Status**: ✅ **COMPILED** and functional
- **Function**: Processes tokens from L0/L1 and applies validation rules

### 3. Python-OCaml Integration Bridge
- **Location**: `src/integration/python-ocaml/`
- **Status**: ✅ **WORKING** (processes real arXiv papers)
- **Achievement**: File-based communication eliminates subprocess issues

---

## 📋 **IMMEDIATE NEXT STEPS (Week 2)**

### Priority 1: Fix ExpanderProofsFinal.v Compilation
**Goal**: Get this single file to compile while preserving all 4 critical theorems
**Approach**: 
1. Fix import path issues (use rescue plan from previous session)
2. Resolve any missing dependencies  
3. Ensure 0 admits maintained
4. **DO NOT** simplify the proofs - they provide essential safety guarantees

### Priority 2: Week 2 V1½ Post-Expansion Rules
**Goal**: Implement ~50 post-expansion validation rules
**Location**: `src/rules/phase1_5/PostExpansionRules.v` (already exists)
**Integration**: Apply rules to L1 expander output
**Performance**: Maintain 42ms SLA compliance

### Priority 3: Preserve V24 Rule Integration
**Goal**: Ensure v25 foundation doesn't break existing 499 rules
**Test**: Run existing corpus validation to verify 0.74% false positive rate maintained
**Monitor**: `src/integration/python-ocaml/real_corpus_validator.py`

---

## 🔧 **TECHNICAL IMPLEMENTATION NOTES**

### Coq Project Structure
The `_CoqProject` file is properly configured:
```
-R src/core/lexer lexer
-R src/core/expander expander  
-R src/core/validation validation
-R src/core/performance performance
```

### Import Strategy for ExpanderProofsFinal.v
Use these imports (from rescue plan):
```coq
From Coq Require Import String List Bool Arith Lia.
From lexer Require Import LatexLexer.
From expander Require Import ExpanderTypes MacroCatalog ExpanderAlgorithm.
```

### Performance Context
- **Current L0+L1**: 4.43ms (9.5x under 42ms target)
- **Challenge**: Add V1½ rules while maintaining SLA
- **Monitoring**: Performance tests already implemented in `PerformanceTests.v`

---

## 📊 **SUCCESS METRICS FOR WEEK 2**

### Formal Verification
- [ ] ExpanderProofsFinal.v compiles with 0 admits
- [ ] All 4 critical safety theorems proven
- [ ] V1½ rules implemented with formal guarantees

### Integration
- [ ] 499 v24 rules continue working
- [ ] False positive rate remains ≤ 0.74%
- [ ] Python-OCaml bridge functional
- [ ] End-to-end pipeline L0→L1→V1½ working

### Performance  
- [ ] Processing time ≤ 42ms (current: 4.43ms + rules overhead)
- [ ] Memory usage within bounds
- [ ] Real corpus validation passes

---

## ⚠️ **CRITICAL WARNINGS**

1. **DO NOT** modify files in `src/rules/migrated/` or `src/rules/enhanced/` unless specifically needed for v25 integration
2. **DO NOT** change the validation rule specifications in `rules_unified.yaml` 
3. **DO NOT** break the Python-OCaml bridge in `src/integration/python-ocaml/`
4. **DO NOT** simplify proofs in ExpanderProofsFinal.v just to make them compile
5. **IGNORE** files in `src/core/lexer/v24r3/` - these are legacy with axioms

---

## 🎯 **HANDOFF SUMMARY**

**Current Status**: v25 Week 1 is 14/15 files complete (93.3% compilation rate)  
**Blocking Issue**: One complex proof file needs import fixes  
**Risk Level**: LOW (clear path forward, existing rules preserved)  
**Next Session Focus**: Fix ExpanderProofsFinal.v, then implement V1½ rules  
**Success Path**: Follow rescue plan, preserve safety guarantees, maintain rule compatibility

The foundation is solid. The other AI needs to fix one compilation issue and then can proceed confidently to Week 2 without breaking any of the 499 existing validation rules.