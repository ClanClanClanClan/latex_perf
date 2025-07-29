# CLAUDE.md - Mandatory Session Instructions

**CRITICAL**: This file contains mandatory instructions for Claude Code sessions working on LaTeX Perfectionist v24. Updated for L1 completion and V1½ transition phase.

## MANDATORY READING ORDER

### 1. MASTER ARCHITECTURE (REQUIRED - START HERE)
**Read FIRST**: `docs/MASTER_ARCHITECTURE.md`
- Single source of truth for project architecture
- Defines dual-layer system: VSNA processing layers vs Validation layers
- ✅ Updated: L1 complete, V1½ rules next priority
- Performance SLA clarification (42ms runtime target)

### 2. PROJECT STATUS (CURRENT WORK)
**Read SECOND**: `docs/PROJECT_STATUS.md`  
- ✅ L0 Lexer complete, ✅ L1 Expander complete
- 🎯 **Current Phase**: V1½ Post-Expansion Rules development
- Next steps and development priorities
- Performance SLA achievement status

### 3. LAYER SPECIFICATIONS (IMPLEMENTATION DETAILS)
**Read THIRD**: `docs/LAYER_L1_SPECIFICATION.md`
- ✅ **IMPLEMENTATION COMPLETE** - L1 fully verified
- All success criteria achieved
- Ready for V1½ post-expansion rule integration

### 4. IMPLEMENTATION GUIDANCE (NEXT PHASE)  
**Read FOURTH**: `docs/IMPLEMENTATION_GUIDE.md`
- Now applies to V1½ post-expansion rule development
- V1 token rules parallel development
- Testing strategies for rule pipeline

## CRITICAL UPDATES

### ✅ COMPLETED ACHIEVEMENTS
- **L0 Verified Lexer**: ✅ COMPLETE (100% implemented, 0 axioms, 0 admits)
- **L1 Verified Macro Expander**: ✅ COMPLETE (76 macros, 3 proofs, performance SLA exceeded)
- **Performance SLA**: ✅ EXCEEDED (4.43ms vs 42ms target)
- **Integration**: ✅ READY (L0→L1 pipeline functional)

### 🎯 CURRENT PRIORITIES
- **V1½ Post-Expansion Rules**: Ready to implement (~50 rules)
- **V1 Token Rules**: Continue parallel development  
- **Performance Integration**: Maintain 42ms SLA with rule pipeline

### ❌ DO NOT ASSUME OLD STATUS  
- **L1 Expander**: ✅ **COMPLETE** (not in-progress)
- **V1½ Rules**: 🎯 **NEXT PRIORITY** (not waiting)
- **Current Phase**: **Month 5** (V1½ Rules), not Month 3-4 (L1 Implementation)

## SESSION STARTUP CHECKLIST

Before starting any development work:

1. [ ] Read updated MASTER_ARCHITECTURE.md (reflects L1 completion)
2. [ ] Read updated PROJECT_STATUS.md (V1½ priorities)  
3. [ ] Understand current phase: **V1½ post-expansion rule development**
4. [ ] Verify L0+L1 pipeline is complete and functional
5. [ ] Check rule framework in `src/core/validation/`

## IMPLEMENTATION PRIORITIES (Current Session)

### PRIMARY GOAL: Begin V1½ Post-Expansion Rules
- Create rule framework for post-expansion validation
- Implement deprecated macro detection rules
- Integrate with L1 expanded token stream
- ~50 rules targeting macro expansion validation

### SECONDARY GOAL: Continue V1 Token Rules (Parallel)
- Complete remaining token-level validation rules
- Build on existing ValidationRules.v foundation
- Focus on TYPO, DELIM, and advanced MATH rules

### PERFORMANCE GOAL: Maintain SLA
- Ensure rule pipeline maintains 42ms SLA
- Optimize rule application for performance
- Test with document corpus when ready (Month 6)

## SUCCESS METRICS

Session is successful when:
- [ ] V1½ rule framework created and functional
- [ ] First batch of post-expansion rules implemented
- [ ] Rules integrate with L1 expanded token stream
- [ ] Performance SLA maintained with rules active
- [ ] Foundation ready for full V1½ rule set completion

## PERFORMANCE CLARIFICATION

**42ms SLA Target**: Document processing runtime ✅ ACHIEVED
- Current: 4.43ms (9.5x under target)
- Compilation time (4.3s L0 + 0.7s L1) is separate infrastructure concern
- Focus: Maintain runtime SLA when adding rule processing

## CRITICAL WARNINGS

### ❌ DO NOT USE YAML SPECIFICATIONS DIRECTLY
The `latex‑perfectionist‑v24‑R3.yaml` file contains **contradictory** and **outdated** information. Always use the internal documentation hierarchy above.

### ❌ DO NOT CONFUSE LAYER NAMES
- **"Layer-02"** in roadmap = **L1 Expander** (✅ COMPLETE)
- **VSNA Processing Layers** (L0-L4) ≠ **Validation Layers** (V1-V4)
- Current work is **V1½ Post-Expansion Rules** development

## EMERGENCY FALLBACK

If confusion arises:
1. **STOP** and re-read updated `docs/MASTER_ARCHITECTURE.md`
2. Check `docs/PROJECT_STATUS.md` for current V1½ phase status
3. Remember: L1 is ✅ COMPLETE, focus is on V1½ rules
4. Ask user for clarification if documentation conflicts persist

## PROJECT CONTEXT REMINDERS

### What LaTeX Perfectionist v24 IS:
- Complete formally verified LaTeX processing pipeline
- VSNA architecture with 542 validation rules  
- L0 Lexer (✅ complete) → L1 Expander (✅ complete) → L2-L4 (📅 planned)
- V1½ Post-Expansion Rules (🎯 current priority)
- Coq implementation with formal proofs, 0 axioms/admits

### Current Implementation Status:
- **L0**: ✅ COMPLETE (2,289 lines, 0 axioms/admits, deterministic proven)
- **L1**: ✅ COMPLETE (1,847 lines, 76 macros, 3 proofs, 4.43ms performance)
- **V1½**: 🎯 NEXT PRIORITY (~50 post-expansion validation rules)
- **L2-L4**: 📅 FUTURE (months 7-12 per roadmap)

This file reflects L1 completion and transition to V1½ rule development phase.