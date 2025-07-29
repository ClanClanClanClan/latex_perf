# COMPLETE IMPLEMENTATION PLAN: LaTeX Perfectionist v24-R3

## Based on Official Specification: `/docs/specifications/latex-perfectionist-v24-R3.yaml`

This document provides a comprehensive implementation plan for LaTeX Perfectionist v24-R3 based on the **actual specification file** and its companion `rules.yaml` containing 542 rule definitions.

---

## 1. Project Overview from Official Specification

### 1.1 Core Metadata
- **Project**: latex-perfectionist
- **Revision**: v24-R3 (from v24-R2)
- **Spec Date**: 2025-07-13
- **Total Rules**: 542 (across 5 phases)

### 1.2 Verified Layer Stack (L0-L4)

```
L0: Lexer (list<char> → list<token>) ✓ DONE
L1: Macro-expander (with fuel limits)
L2: PEG Parser (token list → ast)
L3: Reference Interpreter (ast → semantic_state)
L4: Validation Layers (rule engine)
```

### 1.3 Official Roadmap from Spec

| Month | Deliverable | Proof Targets | Status |
|-------|------------|---------------|---------|
| 1-2 | L0 Verified Lexer | lexer_deterministic | ✓ DONE |
| 3-4 | L1 Macro Expander | expand_fuel_insensitive, expand_terminates_acyclic, expand_no_teof | CURRENT |
| 5 | Phase 1 Rules (72) | rule_sound (70 rules) | TODO |
| 6 | CI Translation Validation | - | TODO |
| 7-9 | L2 PEG Parser | parse_sound | TODO |
| 10 | L3 Interpreter | interp_preserves_tokens | TODO |
| 11 | Phase 4 Style Rules | - | TODO |
| 12 | Verified Build 1.0 | no_false_positives_epsilon | TODO |

---

## 2. LaTeX Epsilon (ε) Subset Definition

### 2.1 Permitted Environment
- **Classes**: article, amsart, amsbook (frozen CTAN date: 2025-03-31)
- **Packages**: 17 whitelisted (amsmath, graphicx, hyperref, tikz, etc.)
- **Engine**: pdfTeX 1.40.26 (containerized with SHA256 verification)

### 2.2 Constraints
- **Macros**: Only \newcommand, \renewcommand with restrictions
  - No optional arguments
  - Acyclic bodies only
  - No conditionals or loops
- **Fuel Limits**:
  - Token growth: 8,192 max
  - Macro calls: 512 (depth AND count)
- **Catcodes**: Local group-scoped changes only
- **IO**: No shell_escape, write18, or network access

### 2.3 Verbatim Handling
- Token type: `TVerbatim`
- Behavior: Merge entire region into single token

---

## 3. Integration with Current Implementation

### 3.1 What We Have vs What's Required

| Component | Current State | Spec Requirement | Gap |
|-----------|--------------|------------------|-----|
| L0 Lexer | ✅ Working (4,955x speedup) | Verified with proof | Need Coq proof |
| Incremental | ✅ Checkpoint-based | Not mentioned in spec | EXTRA feature |
| L1 Expander | ❌ Not implemented | Required with proofs | CRITICAL GAP |
| Rules | ❌ None implemented | 542 rules across phases | MAJOR WORK |
| CI Pipeline | ❌ Not setup | Translation validation | TODO |
| Proofs | ❌ None | Multiple theorems | Coq expertise needed |

### 3.2 Critical Realization

**Our incremental lexer is NOT part of the v24-R3 spec!** The specification focuses on:
- Verified correctness (proofs)
- Comprehensive rule coverage (542 rules)
- LaTeX subset enforcement (epsilon)
- Translation validation against pdfTeX

**But** our incremental performance is a valuable addition that can enhance the v24-R3 implementation.

---

## 4. Complete Implementation Roadmap

### Phase 0: Foundation Alignment (Weeks 1-2)

**Goal**: Align our implementation with v24-R3 specification structure

**Tasks**:
1. Map our lexer to L0 interface `list<char> → list<token>`
2. Define token types matching spec (including `TVerbatim`)
3. Create Coq specification for lexer_deterministic proof
4. Setup development environment with Coq 8.20
5. Create manifest system for latex-epsilon.lock

**Deliverables**:
- L0-compliant lexer interface
- Coq project structure
- Token type definitions matching spec

### Phase 1: L1 Macro Expander (Weeks 3-6) 🔴 CRITICAL

**Goal**: Implement verified macro expander per spec

**Requirements from Spec**:
```ocaml
type fuel = nat
val expand : fuel × token list → option token list
```

**Proof Obligations**:
1. `expand_fuel_insensitive`: Result independent of excess fuel
2. `expand_terminates_acyclic`: Always terminates for acyclic macros
3. `expand_no_teof`: Never produces TEOF token

**Implementation Tasks**:
1. Design macro expansion engine with fuel tracking
2. Implement \newcommand and \renewcommand parsers
3. Enforce constraints (no optional args, acyclic bodies)
4. Add fuel limits (8,192 tokens, 512 calls)
5. Write Coq proofs for three theorems
6. Extract verified OCaml code

**Deliverables**:
- Working macro expander
- All three proofs verified in Coq
- Integration with L0 lexer

### Phase 2: Phase 1 Rules Implementation (Weeks 7-10)

**Goal**: Implement 72 lexical rules from Phase 1

**Rule Families** (from spec):
- TYPO (10+ rules): Quote handling, dashes, ellipsis
- ENC (5+ rules): UTF-8, control characters
- CHAR (10+ rules): Character restrictions
- SPC (10+ rules): Spacing rules
- VERB (5+ rules): Verbatim handling

**Tasks**:
1. Implement rule registry matching spec schema
2. Create validators for each rule
3. Implement auto-fix capabilities where specified
4. Write proofs for "rule_sound" property (70 rules)
5. Performance optimization for token type buckets

**Deliverables**:
- 72 working rules with fixes
- 70 Coq proofs of soundness
- Rule registry system

### Phase 3: CI Translation Validation (Weeks 11-12)

**Goal**: Zero false-positive guarantee vs pdfTeX

**Requirements from Spec**:
```bash
for f in tests/corpus/*.tex tests/adversarial/*.tex; do
  ./bin/verifier "$f" || exit 1
  pdftex -no-shell-escape -interaction=nonstopmode "$f" || exit 1
done
```

**Tasks**:
1. Setup Alpine 3.19 + Coq 8.20 CI environment
2. Implement pdfTeX integration (containerized)
3. Create 500-document corpus
4. Create 20 adversarial test cases
5. Build comparison harness
6. Setup nightly runs with arXiv samples

**Deliverables**:
- Complete CI pipeline
- Translation validation system
- Corpus and adversarial tests

### Phase 4: L2 PEG Parser (Weeks 13-20) 

**Goal**: Implement verified PEG parser

**Interface**: `token list → ast`

**Proof**: `parse_sound`

**Tasks**:
1. Design AST representation
2. Implement PEG grammar for LaTeX epsilon
3. Build parser with error recovery
4. Write parse_sound proof in Coq
5. Extract verified parser

**Deliverables**:
- Working PEG parser
- Formal grammar specification
- parse_sound proof

### Phase 5: Phase 1.5 Rules (Weeks 21-24)

**Goal**: Implement 80 post-expansion rules

**Rule Families**:
- DELIM: Delimiter matching
- MATH (0-40): Math mode rules
- REF: Reference checking
- SCRIPT (≤010): Sub/superscript rules
- CMD: Command validation

**Note**: These rules require L1 macro expansion to work correctly

### Phase 6: L3 Interpreter (Weeks 25-30)

**Goal**: Reference interpreter for semantic analysis

**Interface**: `ast → semantic_state`

**Proof**: `interp_preserves_tokens`

### Phase 7: Remaining Phases (Weeks 31-40)

- **Phase 2 Rules** (200): Structural rules requiring parser
- **Phase 3 Rules** (150): Semantic rules requiring interpreter
- **Phase 4 Rules** (40): Style rules

### Phase 8: Integration and Release (Weeks 41-44)

**Goal**: Enterprise release as Verified Build 1.0

**Final Proof**: `no_false_positives_epsilon`

---

## 5. Critical Technical Challenges

### 5.1 Macro Expansion Complexity

**Challenge**: Implementing terminating macro expansion with proofs

**Key Issues**:
- Detecting cyclic macro definitions
- Fuel mechanism design
- Maintaining expansion history
- Proof of termination

**Solution Approach**:
```coq
Inductive macro_call_tree := 
  | Leaf : token → macro_call_tree
  | Node : string → list macro_call_tree → macro_call_tree.

Definition acyclic (t : macro_call_tree) : Prop := 
  no_repeated_nodes_on_path t.
```

### 5.2 Rule Soundness Proofs

**Challenge**: Proving 70+ rules are sound

**Example** (TYPO-001):
```coq
Theorem typo_001_sound : 
  ∀ doc, no_straight_quotes (apply_typo_001 doc) = true.
```

**Automation Strategy**:
- Common proof tactics
- Property-based testing
- Proof generation templates

### 5.3 Integration Complexity

**Challenge**: Our incremental lexer vs spec's batch model

**Resolution**:
1. Keep incremental as performance optimization
2. Prove incremental_equiv to batch mode
3. Use batch mode for verification
4. Switch to incremental for production

---

## 6. Resource Requirements

### 6.1 Human Resources

| Role | FTE | Duration | Critical Skills |
|------|-----|----------|----------------|
| Coq Expert | 1.0 | 44 weeks | Proofs, extraction |
| OCaml Developer | 1.0 | 44 weeks | Core implementation |
| LaTeX Expert | 0.5 | 30 weeks | Rule design |
| QA Engineer | 1.0 | 35 weeks | Testing, corpus |
| DevOps | 0.5 | 20 weeks | CI/CD, containers |
| **Total** | **4.0 FTE** | | |

### 6.2 Critical Dependencies

- **Coq 8.20**: For all proofs
- **OCaml 5.1**: Multicore support
- **pdfTeX 1.40.26**: Exact version for validation
- **Alpine 3.19**: CI environment

### 6.3 Infrastructure

- CI/CD pipeline with Coq support
- Container registry for pdfTeX
- Storage for 500+ document corpus
- Nightly test infrastructure

---

## 7. Risk Assessment

### 7.1 Highest Risks

1. **Coq Expertise** 🔴
   - Current team lacks deep Coq knowledge
   - Complex proofs (termination, soundness)
   - Extraction performance concerns

2. **Macro Expansion Correctness** 🔴
   - Most complex component
   - Must handle edge cases
   - Termination proof challenging

3. **Timeline Pressure** 🟡
   - 44 weeks for complete implementation
   - 542 rules to implement
   - Multiple complex proofs

4. **Integration Complexity** 🟡
   - Incremental vs batch reconciliation
   - Performance vs correctness tradeoffs
   - Multiple language boundaries

### 7.2 Mitigation Strategies

1. **Hire Coq consultant immediately**
2. **Start with macro expander** (critical path)
3. **Implement rules incrementally** with tests
4. **Maintain working system** throughout

---

## 8. Success Criteria

### 8.1 Mandatory (from spec)

- ✓ All layers implemented (L0-L4)
- ✓ All proofs verified in Coq
- ✓ 542 rules implemented
- ✓ CI translation validation passing
- ✓ ≤0.1% false positive rate
- ✓ Deterministic compilation

### 8.2 Performance (our addition)

- ✓ Maintain 1,000x+ speedup
- ✓ Sub-millisecond edit latency
- ✓ Memory efficient (<100MB)

---

## 9. Next Immediate Actions

Based on spec section 8 (next_actions):

1. **Week 4.1**: ValidationTypes.v + executor scaffold
2. **Week 4.2**: Implement 10 lexical rules + proofs
3. **Week 4.3**: latex-epsilon.lock generator
4. **Week 4.4**: CI pipeline with pdfTeX docker

**Critical**: Start L1 macro expander immediately after!

---

## 10. Conclusion

The v24-R3 specification is **significantly more ambitious** than our current incremental lexer implementation. Key realizations:

1. **Focus is on formal verification**, not just performance
2. **542 rules** must be implemented (we have 0)
3. **Macro expansion** is required and complex
4. **Our incremental feature** is a bonus, not required

**Recommended Approach**:
1. Keep our high-performance incremental lexer
2. Add required components (L1-L4) on top
3. Implement rules systematically
4. Invest heavily in Coq expertise
5. Use CI translation validation for confidence

**Total Effort**: 4.0 FTE × 44 weeks = 176 staff-weeks

This is a **major undertaking** requiring significant investment in formal methods, comprehensive rule implementation, and careful integration with our existing high-performance system.