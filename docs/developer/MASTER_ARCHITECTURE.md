# LaTeX Perfectionist v24 - Master Architecture Document

**CANONICAL REFERENCE** - Single source of truth for project architecture  
**Status**: Authoritative  
**Last Updated**: 2025-07-22  

---

## Executive Summary

LaTeX Perfectionist v24 is a formally verified LaTeX processing pipeline with 542 validation rules. The system uses a dual-layer architecture: VSNA processing layers transform documents through stages, while validation layers apply rules to each stage's output.

---

## I. FUNDAMENTAL ARCHITECTURE

### Core Concept: Dual Layer System

**VSNA Processing Layers (L0-L4)**: Sequential pipeline that transforms documents
```
Input File → L0 Lexer → L1 Expander → L2 Parser → L3 Interpreter → L4 Stylesheet → PDF
```

**Validation Layers (V1-V4)**: Orthogonal rule engines that consume VSNA outputs
```
L0 output → V1 Token Rules (150+ rules)
L1 output → V1½ Post-Expansion Rules (50+ rules) 
L2 output → V2 Structural Rules (200+ rules)
L3 output → V3 Semantic Rules (100+ rules)
L4 output → V4 Style Rules (42+ rules)
```

### Key Principle
- **VSNA layers PRODUCE artifacts**
- **Validation layers CONSUME artifacts**
- They operate independently but synchronously

---

## II. VSNA PROCESSING PIPELINE

### L0: Verified Lexer ✅ COMPLETE
- **Input**: Raw LaTeX string
- **Output**: `list latex_token`
- **Status**: Fully implemented, 0 axioms, 0 admits
- **File**: `src/core/lexer/LatexLexer.v`
- **Proof Target**: `lexer_deterministic`

### L1: Verified Macro Expander ✅ COMPLETE
- **Input**: `list latex_token` (from L0)
- **Output**: `expand_result` (success or error + expanded tokens)
- **Status**: 100% implemented, 0 axioms, 0 admits
- **File**: `src/core/expander/Layer02Verified.v`
- **Performance**: 4.43ms runtime (9.5x under 42ms SLA)
- **Proof Targets**: 
  - `expand_fuel_insensitive` ✅ PROVEN
  - `expand_terminates_acyclic` ✅ PROVEN
  - `expand_no_teof` ✅ PROVEN

### L2: PEG Parser 📅 MONTH 7-9
- **Input**: Expanded tokens (from L1)
- **Output**: Abstract Syntax Tree (AST)
- **Status**: Planned
- **Proof Target**: `parse_sound`

### L3: Reference Interpreter 📅 MONTH 10  
- **Input**: AST (from L2)
- **Output**: Semantic document model
- **Status**: Planned
- **Proof Target**: `interp_preserves_tokens`

### L4: Style Processor 📅 MONTH 11-12
- **Input**: Semantic model (from L3)
- **Output**: Formatted document + PDF
- **Status**: Planned

---

## III. VALIDATION RULE SYSTEM

### V1: Token-Level Rules (Post-L0)
- **Operates on**: Raw token stream
- **Rules**: TYPO-001 to TYPO-050, DELIM-001, etc.
- **Count**: ~150 rules
- **Implementation**: Direct pattern matching on tokens

### V1½: Post-Expansion Rules (Post-L1) 🎯 NEXT PRIORITY
- **Operates on**: Expanded token stream  
- **Rules**: POST-001, deprecated macro detection
- **Count**: ~50 rules
- **Purpose**: Detect expansion failures, validate macro usage
- **Status**: Ready to implement (L1 complete)

### V2: Structural Rules (Post-L2)
- **Operates on**: Parse tree/AST
- **Rules**: Section hierarchy, environment matching
- **Count**: ~200 rules
- **Implementation**: Tree traversal patterns

### V3: Semantic Rules (Post-L3)
- **Operates on**: Semantic document model
- **Rules**: Cross-references, citations, mathematical consistency
- **Count**: ~100 rules

### V4: Style Rules (Post-L4)
- **Operates on**: Final document representation
- **Rules**: Typography, formatting consistency
- **Count**: ~42 rules

**Total**: 542 validation rules across all layers

---

## IV. DATA FLOW ARCHITECTURE

### Complete Processing Flow
```
1. Input: document.tex (string)
2. L0 Lexer: string → list latex_token
3. V1 Rules: Apply token-level validation
4. L1 Expander: list latex_token → expand_result  
5. V1½ Rules: Apply post-expansion validation
6. L2 Parser: expanded_tokens → AST
7. V2 Rules: Apply structural validation
8. L3 Interpreter: AST → semantic_model
9. V3 Rules: Apply semantic validation
10. L4 Stylesheet: semantic_model → formatted_document
11. V4 Rules: Apply style validation
12. Output: PDF + validation_report
```

### Document State Record
```coq
Record document_state := {
  raw_tokens      : list latex_token;        (* After L0 *)
  expanded_tokens : option (list latex_token); (* After L1 *)
  ast             : option ast_tree;         (* After L2 *)
  semantic_model  : option semantic_doc;     (* After L3 *)
  final_document  : option formatted_doc;    (* After L4 *)
  layer           : layer;                   (* Highest layer completed *)
  validation_issues : list validation_issue  (* From all V-layers *)
}.
```

---

## V. CURRENT PROJECT STATUS

### Completed Components ✅
- **L0 Lexer**: 100% complete with formal verification
- **L1 Expander**: 100% complete, 76 macros, 3 proofs, 0 admits
- **Token Types**: Canonical 13-token system in `LatexLexer.v`
- **Performance SLA**: 4.43ms runtime (9.5x under 42ms target)
- **V1 Rules Framework**: Basic infrastructure in `ValidationTypes.v`

### Active Development 🎯
- **V1½ Post-Expansion Rules**: Ready to implement (~50 rules)
- **V1 Token Rules**: Continue parallel development
- **Performance Integration**: Maintain 42ms SLA with rules

### Planned Components 📅
- **L2-L4 Pipeline**: Months 7-12 per roadmap
- **V2-V4 Rules**: Corresponding to pipeline completion
- **Integration Testing**: 1000-document corpus validation (Month 6)
- **Performance SLA**: 42ms per document processing (✅ achieved: 4.43ms)
- **Enterprise Deployment**: SaaS platform

---

## VI. KEY TERMINOLOGY (GLOSSARY)

| Term | Definition |
|------|------------|
| VSNA | Verified Streaming Nested Automaton - the core processing architecture |
| L0-L4 | Processing layers that transform documents sequentially |
| V1-V4 | Validation layers that apply rules to processing outputs |
| LaTeX ε | Constrained LaTeX subset with acyclic macros only |
| CARC | Certified Automatic Rule Classifier - rule optimization system |
| Track 1 | Coq implementation (verified) |
| Track 2 | OCaml implementation (performance-optimized) |

---

## VII. CRITICAL DISAMBIGUATIONS  

### ❌ AVOID THESE CONFUSIONS:
1. **"Layer-02"** in roadmap = **L1 Expander** (not L2 Parser)
2. **Validation layers ≠ Processing layers** (orthogonal systems)
3. **"Phase 1½ rules"** = **V1½ rules** (post-expansion validation)
4. **Layer "done"** means **verified + integrated**, not just implemented

### ✅ CORRECT UNDERSTANDING:
- **L1 Verified Macro Expander** is ✅ **COMPLETE**
- Next priority: **V1½ post-expansion validation rules**  
- L0 Lexer is complete and provides the token foundation
- L0+L1 pipeline fully functional, ready for rule development
- All other layers (L2-L4) are planned for future months

---

## VIII. INTEGRATION WITH OTHER DOCUMENTS

### Primary References:
- **L1 Complete Specification**: `docs/LAYER_L1_SPECIFICATION.md`
- **Implementation Guide**: `docs/IMPLEMENTATION_GUIDE.md`
- **Project Status**: `docs/PROJECT_STATUS.md`
- **Original Roadmap**: `latex‑perfectionist‑v24‑R3.yaml`

### Document Hierarchy:
1. **This Document**: Architecture overview and disambiguation
2. **Layer Specifications**: Technical details for each component
3. **Implementation Guides**: Step-by-step coding instructions
4. **Status Updates**: Current progress and milestones

---

---

## IX. PERFORMANCE TARGETS CLARIFICATION

### Runtime Performance SLA: 42ms
- **Target**: Process typical LaTeX documents within 42ms
- **Current Achievement**: ✅ 4.43ms (9.5x under target)
- **Measurement**: End-to-end L0→L1 processing time
- **Status**: ✅ SLA EXCEEDED

### Compilation Performance
- **L0 Lexer**: 4.3s compilation time (reasonable for formal verification)
- **L1 Expander**: 0.7s compilation time (excellent)
- **Note**: Compilation time separate from runtime SLA

---

*This document resolves all architectural confusion identified in the uncertainty analysis of 2025-07-21 and reflects L1 implementation completion as of 2025-07-22.*