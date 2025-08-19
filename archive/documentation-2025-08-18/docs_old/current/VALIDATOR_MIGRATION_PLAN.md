# Validator Migration Plan - From Mockup to Reality

## 🚨 Current Reality

### What We Have
- **40 validator mockups** that don't work with real tokens
- **Good framework** with DAG scheduling
- **Correct manifest structure**
- **Wrong token assumptions** throughout

### What Actually Works
- ✅ Validator framework (DAG, manifest, scheduling)
- ✅ Rule definitions (the validation logic is sound)
- ❌ Token processing (completely broken)
- ❌ Integration with L0 lexer (non-existent)

## 📊 Technical Debt Assessment

### Critical Issues

1. **Token Type Mismatch**
   - Validators expect: Simplified token types
   - L0 produces: `Lexer_v25.token` (6 types)
   - Pipeline uses: `Pipeline_core.token` (11 types)
   - **Impact**: 100% of validators broken

2. **Tokenization Misunderstanding**
   - Words are character sequences, not macros
   - Math mode uses catcodes, not special tokens
   - **Impact**: ~60% of patterns won't match

3. **Location Tracking**
   - All validators use fake locations
   - No real error positioning
   - **Impact**: Users can't find issues

4. **State Management**
   - No context tracking
   - No environment stacks
   - No scope management
   - **Impact**: ~40% of validators need this

## 🔧 Migration Strategy

### Phase 1: Foundation Fix (Week 2, Day 2-3)
**Goal**: Make validators work with real tokens

1. **Update Token Types** ✅ STARTED
   - Created `proper_validator_base.ml`
   - Use `Pipeline_core.located_token`
   - Handle catcodes correctly

2. **Fix Core Validators** (10 validators)
   - TYPO-001: Smart quotes ✅ EXAMPLE DONE
   - TYPO-002: Ellipsis
   - TYPO-003: Dashes
   - SPACE-001: Citations
   - MATH-001: Deprecated environments

3. **Create Test Harness**
   - Connect to real L0 lexer
   - Test with actual documents
   - Verify error locations

### Phase 2: State Management (Week 2, Day 3-4)
**Goal**: Add proper context tracking

1. **Implement State System**
   - Math mode tracking
   - Environment stacks
   - Label/reference tracking
   - Section hierarchy

2. **Migrate Complex Validators** (15 validators)
   - MATH-002 to MATH-011 (need math mode)
   - NEST-002 to NEST-006 (need env stack)

### Phase 3: Pattern Matching (Week 2, Day 4-5)
**Goal**: Fix tokenization patterns

1. **Character Sequence Matching**
   - Words like "and", "sin", "cos"
   - Abbreviations "e.g.", "i.e."
   - Date patterns

2. **Migrate Pattern Validators** (15 validators)
   - TYPO-004 to TYPO-018
   - REF-002 to REF-006

### Phase 4: Integration (Week 2, Day 5-6)
**Goal**: Full pipeline integration

1. **Connect to Pipeline**
   - L0 → validators
   - Proper error reporting
   - Performance testing

2. **Update Manifest**
   - Correct dependencies
   - Accurate provides/requires
   - Performance metrics

## 📋 Migration Checklist

### Immediate Actions
- [ ] Stop claiming validators work
- [ ] Update documentation to reflect reality
- [ ] Begin systematic migration

### Per-Validator Migration
For each validator:
1. [ ] Convert to use `located_token`
2. [ ] Fix pattern matching for real tokens
3. [ ] Add state management if needed
4. [ ] Test with real L0 output
5. [ ] Update manifest entry

### Validation Criteria
A validator is "migrated" when it:
- ✅ Uses correct token types
- ✅ Handles real tokenization
- ✅ Reports accurate locations
- ✅ Passes integration tests

## 📈 Progress Tracking

| Category | Total | Mockup | Migrated | Tested |
|----------|-------|--------|----------|--------|
| Typography | 18 | 18 | 1 | 0 |
| Math | 11 | 11 | 1 | 0 |
| Structure | 11 | 11 | 0 | 0 |
| Semantic | 6 | 6 | 1 | 0 |
| **Total** | **46** | **46** | **3** | **0** |

## ⏰ Realistic Timeline

### Week 2 Revised Goals
- **Original**: 40 new validators ✅ (but mockups)
- **Reality**: 10-15 properly working validators
- **Focus**: Quality over quantity

### Week 3 Goals
- Complete migration of remaining validators
- Full integration testing
- Performance optimization

### Week 4 Goals
- Add 20 new validators (properly implemented)
- Reach 60-70 working validators total

## 💡 Lessons Learned

1. **Don't assume token structure** - Always check actual lexer output
2. **Test with real data early** - Mockups hide critical issues
3. **State management is essential** - Most validators need context
4. **Location tracking is critical** - Users need accurate positions

## 🎯 Success Metrics

### Short Term (End of Week 2)
- [ ] 10+ validators fully migrated
- [ ] Integration test suite passing
- [ ] Real error locations working

### Medium Term (End of Week 3)
- [ ] All 40 validators migrated
- [ ] <0.5ms per validator performance
- [ ] <1% false positive rate

### Long Term (Week 5)
- [ ] 100+ working validators
- [ ] Full pipeline integration
- [ ] Production ready

## ⚠️ Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Migration takes longer than expected | High | Prioritize high-value validators |
| Performance degrades with proper implementation | Medium | Optimize hot paths, use caching |
| Integration reveals more issues | High | Allocate buffer time |
| State management adds complexity | Medium | Create reusable state helpers |

## 📝 Next Steps

1. **Immediate**: Continue migrating validators using `proper_validator_base.ml`
2. **Today**: Get 5 validators fully working with real tokens
3. **Tomorrow**: Add state management system
4. **This Week**: Achieve 10-15 production-ready validators

---

**Status**: Migration IN PROGRESS
**Honest Assessment**: We have a framework, not working validators
**Path Forward**: Clear but requires significant work