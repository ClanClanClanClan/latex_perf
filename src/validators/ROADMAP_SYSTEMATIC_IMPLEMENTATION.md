# ROADMAP SYSTEMATIC IMPLEMENTATION
## Following PLANNER_v25_R1.yaml 156-Week Timeline

**Status**: 🎯 **ROADMAP EXECUTION INITIATED**  
**Current**: Week 1 of 156-week schedule (Week-0 = 2025-07-28)  
**Approach**: Systematic progression following official milestones

---

## 📅 ROADMAP TIMELINE (From PLANNER_v25_R1.yaml)

### **Current Position**: Week 1
- **Baseline**: 80 validators (planner reference)
- **Performance**: 8.36ms (✅ under 20ms gate)
- **Admits**: 0 (✅ zero-admit gate achieved)
- **Clean state**: ✅ Achieved

### **Systematic Milestones**
```yaml
Week 1-5:   Bootstrap → Perf α (Foundation validators)
Week 5-10:  Perf α → Proof β (Formal verification)
Week 10-52: Foundation Year (180 validators total)
Week 52-104: Acceleration Year (430 validators)
Week 104-156: Completion Year (623 validators)
```

### **Three-Year Trajectory**
- **Year 1**: Foundation – infra, proofs, **180 rules**
- **Year 2**: Acceleration – pattern mining (**430 rules**)  
- **Year 3**: Completion – ML-assisted generation (**623 rules**)

---

## 🎯 WEEK 1-5 FOUNDATION TARGET

### **Core Validator Priorities** (30-50 validators for Bootstrap → Perf α)

#### **L0_Lexer Foundation** (15-20 validators)
```yaml
Priority 1: Essential TYPO rules
- TYPO-001: ASCII straight quotes [Error]
- TYPO-002: Double hyphen [Warning]  
- TYPO-003: Triple hyphen [Warning]
- TYPO-005: Ellipsis periods [Warning]
- TYPO-006: Tab character [Error]
- TYPO-007: Trailing spaces [Info]

Priority 2: Critical SPC rules  
- SPC-001: Missing thin space before differential [Info]
- SPC-002: Space before punctuation [Info]
- SPC-003: Non-breaking space usage [Warning]

Priority 3: Essential CHAR rules
- CHAR-001: Unicode validation [Error]
- CHAR-002: Character encoding [Error]
```

#### **L1_Expanded Foundation** (10-15 validators)
```yaml
Priority 1: Critical DELIM rules
- DELIM-001: Unmatched braces [Error]
- DELIM-002: Extra closing braces [Error]
- DELIM-003: Unmatched \left without \right [Error]
- DELIM-004: Unmatched \right without \left [Error]

Priority 2: Essential REF rules
- REF-001: Undefined references [Error]
- REF-002: Duplicate labels [Error]  
- REF-003: Label contains spaces [Warning]
- REF-004: Label uppercase [Info]

Priority 3: Core MATH rules (Draft only)
- MATH-009: First actual Draft MATH rule
- MATH-010: Mathematical operators [Info]
- MATH-011: Math spacing [Info]
```

#### **L3_Semantics Foundation** (5-10 validators)
```yaml
Priority 1: Essential BIB rules
- BIB-001: Bibliography validation [Error]
- BIB-002: Citation format [Warning]

Priority 2: Core CMD rules  
- CMD-001: Command usage [Warning]
- CMD-002: Deprecated commands [Warning]
```

---

## 🏗️ SYSTEMATIC IMPLEMENTATION APPROACH

### **Phase 1: Core Infrastructure** (Week 1)
```ocaml
(* Foundation DAG system with core validators *)
let foundation_week1_manifests = [
  (* Critical L0_Lexer validators *)
  typo001_manifest; (* ASCII quotes *)
  typo002_manifest; (* Double hyphen *)
  typo006_manifest; (* Tab character *)
  
  (* Critical L1_Expanded validators *)
  delim001_manifest; (* Unmatched braces *)
  delim003_manifest; (* \left without \right *)
  ref001_manifest;   (* Undefined references *)
  
  (* Essential performance/safety validators *)
]

(* Target: 10-15 critical validators for Week 1 *)
```

### **Phase 2: Foundation Expansion** (Week 2-3)
```ocaml
(* Expand to 30 foundation validators *)
let foundation_week2_manifests = foundation_week1_manifests @ [
  (* Additional TYPO validators *)
  typo003_manifest; typo005_manifest; typo007_manifest;
  
  (* Additional DELIM validators *)
  delim002_manifest; delim004_manifest;
  
  (* Additional REF validators *)  
  ref002_manifest; ref003_manifest;
  
  (* Core SPC and CHAR validators *)
  spc001_manifest; char001_manifest;
]
```

### **Phase 3: Bootstrap Complete** (Week 4-5)
```ocaml
(* Reach 50 foundation validators for Perf α gate *)
let foundation_perf_alpha_manifests = foundation_week2_manifests @ [
  (* Complete foundation set *)
  (* Additional MATH, BIB, CMD validators *)
  (* Performance optimization *)
  (* Formal proof preparation *)
]
```

---

## ⚡ PERFORMANCE GATE COMPLIANCE

### **Hard Gates** (Must meet to continue)
```yaml
Performance Gate: 
  - p95 ≤ 20ms on perf_smoke_big.tex (1.1MB)
  - p95 ≤ 3ms on 80KB edit-window harness

Zero-Admit Gate:
  - admits == 0 
  - proof-debt ≤ 10

Current Status:
  - Performance: 8.36ms ✅ (well under 20ms)
  - Admits: 0 ✅ 
  - DAG system: ✅ Implemented
```

### **Performance Monitoring**
```bash
# Performance validation per planner Section 8
bench/run_lexer.ml perf_smoke_big.tex  # Must stay under 20ms p95
./validator_dag_system test_80kb.tex   # Must stay under 3ms p95
```

---

## 📊 SYSTEMATIC DEVELOPMENT METRICS

### **Week 1-5 Targets**
- **Week 1**: 10-15 critical validators (foundation)
- **Week 2**: 20-25 validators (expansion)
- **Week 3**: 30-35 validators (consolidation)
- **Week 4**: 40-45 validators (optimization)
- **Week 5**: 50 validators (Perf α gate ready)

### **Quality Gates**
- ✅ **Specification compliance**: All validators match rules_v3.yaml
- ✅ **DAG system**: Proper dependency management
- ✅ **Performance**: Stay under hard limits
- ✅ **Formal proofs**: Prepare for Proof β gate (Week 10)

### **Year 1 Progression**
```
Week 1-5:   Foundation (50 validators)
Week 5-10:  Proof β (80 validators)  
Week 10-25: Expansion (120 validators)
Week 25-40: Consolidation (150 validators)
Week 40-52: Completion (180 validators)
```

---

## 🎯 NEXT IMMEDIATE ACTIONS

### **Current Week 1 Tasks**
1. **Implement 10-15 critical foundation validators** with DAG manifests
2. **Verify performance gates** on perf_smoke_big.tex
3. **Test DAG execution system** with foundation set
4. **Prepare formal proof framework** for upcoming gates

### **Week 2 Preparation**
1. **Expand to 25 validators** (second priority set)
2. **Performance optimization** if needed
3. **Documentation** of systematic approach
4. **Prepare for Perf α gate** (Week 5)

---

**ROADMAP EXECUTION READY**: Following the systematic 156-week timeline with proper milestone progression from the planner.