# ZERO ADMITS/AXIOMS ELIMINATION PLAN

**Date**: 2025-07-29  
**Purpose**: Systematic elimination of ALL admits and axioms to achieve v25 compliance  
**Target**: **0 admits, 0 axioms** across entire codebase  
**Priority**: 🚨 **CRITICAL** - v25 specification requirement  

---

## CURRENT STATUS

### 📊 **VIOLATION SUMMARY**
- **Admits**: 66 total (50 production + 16 tests)
- **Axioms**: 4 total  
- **Files with violations**: 17 files
- **v25 Requirement**: **0 admits, 0 axioms**

### 🎯 **ELIMINATION TARGET**
**100% elimination required** - no exceptions for tests, infrastructure, or extensions.

---

## DETAILED VIOLATION INVENTORY

### **AXIOMS** (4 total) 🚨 **HIGHEST PRIORITY**

#### **File: `src/core/lexer/v24r3/CoreLexer.v`**
```coq
Axiom lex_bytes_nil : lex_bytes init_state nil = (nil, init_state).
Axiom lex_bytes_app : forall st bs1 bs2, [continuation...]
```
- **Count**: 2+ axioms
- **Criticality**: ❌ **CRITICAL** - In core lexer
- **Action**: Replace with proper proofs

#### **Additional Axioms**: 2 more (need to identify exact locations)

### **ADMITS BY CATEGORY**

#### **Category 1: Production Code** (50 admits) 🚨

**A. Core Proof Infrastructure** (1 admit):
- `proofs/CoreProofs/TokenEq.v` - 1 admit

**B. Advanced Lexer Theory** (30+ admits):
- `src/coq/lexer/RingBufferTheory.v` - Multiple admits
- `src/coq/lexer/IncrementalCorrect.v` - Multiple admits  
- `src/coq/lexer/CheckpointTheory.v` - Multiple admits
- `src/coq/lexer/ErrorRecovery.v` - Multiple admits
- `src/coq/lexer/ParallelFirstPass.v` - Multiple admits
- `src/coq/lexer/LexerProofs.v` - Multiple admits

**C. VSNA Architecture** (15+ admits):
- `src/coq/vsna/UVSNA_CARC.v` - Multiple admits
- `src/coq/vsna/UVSNA.v` - Multiple admits
- `src/coq/vsna/Performance.v` - Multiple admits
- `src/coq/vsna/Correctness.v` - Multiple admits

**D. Extraction Framework** (1 admit):
- `src/extraction/ParallelValidator.v` - 1 admit

#### **Category 2: Test Infrastructure** (16 admits) 🟡

**A. Unit Tests**:
- `tests/unit/SIMPLE_SOUNDNESS_TESTS.v` - 2 admits
- `tests/unit/lexer/TestIncrementalLexer.v` - 14+ admits
- `tests/unit/MATH_ENV_REF_STYLE_TESTS.v` - 4 admits

**B. Integration Tests**:
- `tests/integration/V24_R3_Full_Integration_Test.v` - 2 admits

**C. Performance Tests**:
- `tests/stress/PerformanceBenchmarks.v` - 1 admit

---

## ELIMINATION STRATEGY

### **Phase 1: CRITICAL AXIOM ELIMINATION** 🚨

#### **Priority 1A: Core Lexer Axioms**
```bash
# File: src/core/lexer/v24r3/CoreLexer.v
# Action: Replace axioms with actual proofs
```

**Approach**:
1. **Analyze axiom statements** - understand what needs proving
2. **Implement proofs** - provide actual evidence
3. **Test compilation** - ensure proofs are valid
4. **Verify no regression** - maintain functionality

#### **Priority 1B: Identify Remaining Axioms**
```bash
grep -r "Axiom" --include="*.v" . | grep -v archive
```

### **Phase 2: PRODUCTION ADMIT ELIMINATION** 🔥

#### **Priority 2A: Core Proof Infrastructure**
- `proofs/CoreProofs/TokenEq.v` - Complete token equality proof
- **Impact**: Foundation for other proofs

#### **Priority 2B: Lexer Theory Proofs**
- `src/coq/lexer/*.v` - Complete lexer correctness proofs
- **Strategy**: Systematic proof completion
- **Order**: Dependencies first, then dependents

#### **Priority 2C: VSNA Architecture Proofs**  
- `src/coq/vsna/*.v` - Complete architecture proofs
- **Strategy**: Focus on soundness and correctness

#### **Priority 2D: Extraction Framework**
- `src/extraction/ParallelValidator.v` - Complete extraction proof

### **Phase 3: TEST INFRASTRUCTURE CLEANUP** 📋

#### **Strategy**: Convert admits to proper test assertions
```coq
(* Instead of: *)
Theorem test_something : P.
Proof. Admitted.

(* Use: *)
Example test_something : P.
Proof. 
  (* Actual proof or *)
  (* For tests: exact test_evidence *)
Qed.
```

---

## IMPLEMENTATION ROADMAP

### **Week 1: Axiom Elimination** 🚨
- **Day 1-2**: Analyze and eliminate core lexer axioms
- **Day 3-4**: Find and eliminate remaining 2 axioms
- **Day 5**: Verify 0 axioms across codebase

### **Week 2: Critical Production Admits** 🔥
- **Day 1-2**: Complete `proofs/CoreProofs/TokenEq.v`
- **Day 3-5**: Begin lexer theory proof completion

### **Week 3-4: Systematic Admit Elimination** 📋
- **Week 3**: Complete remaining lexer proofs
- **Week 4**: Complete VSNA architecture proofs

### **Week 5: Test Infrastructure Cleanup** 🧹
- Clean up test admits (lower priority but still required)

---

## PROOF COMPLETION STRATEGIES

### **Strategy 1: Proof Sketching**
```coq
Theorem example : P.
Proof.
  (* Step 1: break down the goal *)
  intros.
  (* Step 2: apply relevant lemmas *)
  apply known_lemma.
  (* Step 3: solve subgoals *)
  assumption.
Qed.
```

### **Strategy 2: Automation**
```coq
Theorem example : P.
Proof.
  auto.     (* Try automatic proof *)
  tauto.    (* For tautologies *)
  omega.    (* For arithmetic *)
  trivial.  (* For trivial goals *)
Qed.
```

### **Strategy 3: Lemma Building**
```coq
Lemma helper : Q.
Proof. (* prove helper first *) Qed.

Theorem main : P.
Proof.
  apply helper.  (* use helper lemma *)
Qed.
```

---

## VERIFICATION PROTOCOL

### **After Each Elimination**:
```bash
# 1. Check compilation
make all

# 2. Count remaining admits/axioms  
grep -r "Admitted\|Axiom" --include="*.v" . | grep -v archive | wc -l

# 3. Run tests
make test

# 4. Commit progress
git add -A && git commit -m "Eliminate admits in [file]: X admits → 0 admits"
```

### **Progress Tracking**:
```bash
# Daily admit count
echo "$(date): $(grep -r "Admitted" --include="*.v" . | grep -v archive | wc -l) admits remaining" >> ADMIT_PROGRESS.log
```

---

## SUCCESS CRITERIA

### ✅ **COMPLETION REQUIREMENTS**
1. **0 axioms** across entire codebase
2. **0 admits** across entire codebase  
3. **100% compilation** after eliminations
4. **All tests passing** after eliminations
5. **Functionality preserved** throughout process

### 📊 **VERIFICATION COMMANDS**
```bash
# Must return 0:
grep -r "Axiom" --include="*.v" . | grep -v archive | wc -l
grep -r "Admitted" --include="*.v" . | grep -v archive | wc -l

# Must succeed:
make all
make test
```

---

## RISK MITIGATION

### **Backup Strategy** 🛡️
```bash
# Before each phase
git tag "pre-admit-elimination-phase-X"
git commit -m "Backup before admit elimination phase X"
```

### **Rollback Plan** 🔄
```bash
# If elimination breaks functionality
git reset --hard pre-admit-elimination-phase-X
```

### **Incremental Approach** 📈
- **One file at a time** - easier debugging
- **Frequent commits** - easy rollback points
- **Continuous testing** - catch regressions early

---

## CONCLUSION

**The v25 specification is non-negotiable: 0 admits, 0 axioms.** This plan provides a systematic approach to achieve full compliance while preserving all functionality.

**Priority order**: Axioms → Core admits → Extension admits → Test admits

**Timeline**: 4-5 weeks for complete elimination with proper testing and verification.

---

*Plan created: 2025-07-29*  
*Target: 0 admits, 0 axioms by Week 5*  
*Status: Ready for execution*