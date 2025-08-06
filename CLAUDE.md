# CLAUDE.md - Mandatory Session Instructions

**CRITICAL**: This file contains mandatory instructions for Claude Code sessions working on LaTeX Perfectionist v25. Updated for accurate Week 1 status.

## MANDATORY READING ORDER

### 1. PROJECT STATUS (CURRENT REALITY - READ FIRST)
**Read FIRST**: `docs/current/ADMIT_ELIMINATION_COMPLETE_HANDOFF.md`
- Single source of truth for current Week 1 admit elimination work
- 0 admits remaining (target achieved)
- Critical blocker analysis and solutions provided

### 2. PROJECT TIMELINE (ULTRACHECK - READ SECOND)  
**Read SECOND**: `specs/PLANNER.yaml`
- ✅ **ACCURATE TIMELINE**: Week 1 of 156-week project (started July 28, 2025)
- Current phase: Foundation week with admit elimination priority
- Performance achieved: 14.07ms lexer (L0 target ≤20ms BEATEN by 29.65%)

### 3. ADMIT ANALYSIS (TECHNICAL DETAILS)
**Read THIRD**: `docs/current/ADMIT_TECHNICAL_DETAILS.md` (if exists)
- Technical breakdown of admit elimination strategy
- Proof strategies and blocking issues
- Implementation dependencies

## CRITICAL PROJECT STATUS UPDATES

### ✅ CURRENT ACHIEVEMENTS (Week 1)
- **Performance Status**: ✅ TARGET ACHIEVED (14.07ms current, ≤20ms target BEATEN)
- **Architecture**: ✅ COMPLETE (5-layer VSNA + validation framework)
- **Validators Implemented**: 80/623 (foundation established)
- **Timeline**: Week 1 of 156-week project schedule

### 🎯 CURRENT PRIORITIES (Week 1 Focus)
- **Admit Elimination**: ✅ COMPLETE (0 admits achieved)
- **Proof Debt Management**: ≤10 temporary axioms allowed until Oct 31, 2025
- **Foundation Solidification**: Get formal verification to 100%

### ❌ DO NOT ASSUME OUTDATED STATUS  
- **NOT v24**: This is v25-R0 (updated architecture)
- **NOT L1 Complete**: We're in Week 1 foundations
- **NOT V1½ Rules Phase**: Admits come first
- **NOT Month 5**: This is Week 1 (August 2025)

## SESSION STARTUP CHECKLIST

Before starting any development work:

1. [ ] Understand we're in **Week 1 of 156-week v25 project**
2. [ ] Read admit elimination handoff document completely
3. [ ] Check current admit count: `grep -r "admit\|Admitted" src/`
4. [ ] Verify build system: `make clean && make all`
5. [ ] Focus on 0-admit goal, not new features

## IMPLEMENTATION PRIORITIES (Week 1 Session)

### PRIMARY GOAL: Foundation Development
- Maintain 0-admit status throughout development  
- Begin L2 parser planning (after L1 complete)
- Continue formal verification work
- Prepare for Week 5 Performance α gate

### SUCCESS METRICS: Week 1 Gates
- [x] Admits reduced to 0 ✅ ACHIEVED
- [ ] Build system remains functional (`make all` succeeds)
- [ ] No new axioms introduced (stay within 10 temporary limit)
- [ ] Critical blockers identified and resolved

### TIMELINE CONTEXT: 156-Week Schedule
- **Week 1** (current): Foundation/admit elimination
- **Week 5**: Performance α gate
- **Week 10**: Proof β gate  
- **Week 52**: L2 delivery
- **Week 156**: GA release (July 26, 2028)

## SUCCESS METRICS

Session is successful when:
- [x] Admit count: 0 admits ✅ ACHIEVED
- [ ] Critical blocker solutions implemented or documented
- [ ] Build system remains stable
- [x] 0-admit goal maintained ✅ ACHIEVED
- [ ] No regression in existing verified components

## PERFORMANCE STATUS CLARIFICATION

**Performance Status**: L0 Lexer Target ACHIEVED ✅
- **Current**: 14.07ms (L0_lexer optimized implementation)
- **Target**: ≤20ms BEATEN by 29.65% (5.93ms under target)
- **Implementation**: Bigarray ring buffer as per L0 Lexer Specification V3
- **Reference**: See `specs/L0_LEXER_SPEC.md` for detailed plan

## CRITICAL WARNINGS

### ❌ DO NOT USE OUTDATED PROJECT ASSUMPTIONS
- Old CLAUDE.md references may contain v24 or outdated L1 completion claims
- Always verify current status against `specs/PLANNER.yaml` timeline
- Week numbers are critical - we're in Week 1, not advanced phases

### ❌ DO NOT CONFUSE VERSION TERMINOLOGY
- **This is v25-R0** (not v24-R3)
- **Week 1 of 156-week project** (started July 28, 2025)
- **Current milestone**: 0-admit foundation, not feature development

## EMERGENCY FALLBACK

If confusion arises:
1. **STOP** and re-read `specs/PLANNER.yaml` Section 14 (timeline)
2. Check `docs/current/ADMIT_ELIMINATION_COMPLETE_HANDOFF.md` for technical status
3. Remember: Week 1 = admit elimination, not advanced features
4. Ask user for clarification if timeline/version conflicts persist

## PROJECT CONTEXT REMINDERS

### What LaTeX Perfectionist v25 IS:
- 156-week project started July 28, 2025 (Week 1 current)
- Target: 623 formally verified validation rules
- Architecture: 5-layer VSNA processing + validation framework
- Current: 80 validators implemented, 0 admits (goal achieved)

### Current Week 1 Implementation Status:
- **Foundation**: ✅ SOLID (architecture complete, performance optimization planned)  
- **Admits**: ✅ COMPLETE (0 admits achieved)
- **Timeline**: Week 1 of 156 (foundation/proof phase)
- **Next Gate**: Week 5 Performance α (expected pass)

This file reflects accurate Week 1 v25 status with admit elimination complete.

# Important Instruction Reminders
- Follow 0-admit policy: no new admits, eliminate existing ones
- Performance optimization in progress, focus on formal verification
- We're in foundation Week 1, not advanced development phases
- Timeline matters: 156-week project, currently Week 1