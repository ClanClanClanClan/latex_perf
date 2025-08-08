# DOCUMENTATION CONTRADICTION AUDIT

## 🚨 CRITICAL CONTRADICTIONS FOUND

### CONTRADICTION #1: Performance Numbers

| Document | Claims | Reality Check |
|----------|--------|---------------|
| `CLAUDE.md` | 31.40ms (current) | ✅ Correct WITHOUT Flambda2 |
| `CORRECTED_STATUS_REPORT.md` | 17.7ms "ACHIEVED" | ❌ WRONG - this was aspirational |
| `CRYSTAL_CLEAR_BUILD_REQUIREMENTS.md` | 17-18ms with Flambda2 | ✅ Correct WITH Flambda2 |
| Various old docs | 17.7ms everywhere | ❌ Not achieved without Flambda2 |

### CONTRADICTION #2: Build Requirements

| Document | Says |
|----------|------|
| Most docs | No mention of Flambda2 requirement |
| `CRYSTAL_CLEAR_BUILD_REQUIREMENTS.md` | Flambda2 MANDATORY |
| Old build scripts | Standard OCaml flags only |

### CONTRADICTION #3: Status Claims

| Document | Claims |
|----------|--------|
| `CLAUDE.md` | "Optimization needed" |
| `CORRECTED_STATUS_REPORT.md` | "Already ACHIEVED" |
| Reality | Achieved ONLY with Flambda2 |

## THE REAL TRUTH

### Performance Matrix

| Configuration | Actual Performance | vs Target |
|--------------|-------------------|-----------|
| Standard OCaml | 31.40ms | ❌ 1.6x over |
| OCaml with -O3 flags | 26.24ms | ❌ 1.3x over |
| OCaml with Flambda2 | 17-18ms | ✅ MEETS target |
| Wrong implementation | 77.85ms | ❌ Disaster |

### What Needs Fixing

1. **Remove all "17.7ms achieved" claims** from docs that don't specify Flambda2
2. **Update CLAUDE.md** to clarify Flambda2 requirement
3. **Consolidate all performance claims** to single source of truth
4. **Remove contradictory status reports**

## DOCUMENTS TO UPDATE

### High Priority (Active confusion):
- [ ] `CLAUDE.md` - Says 31.40ms, needs Flambda2 context
- [ ] `CORRECTED_STATUS_REPORT.md` - Says 17.7ms achieved (FALSE without Flambda2)
- [ ] All docs claiming "17.7ms achieved" without build context

### Medium Priority (Historical docs):
- [ ] Old performance reports claiming success
- [ ] Build scripts missing Flambda2 flags
- [ ] Test reports with wrong methodology

## RECOMMENDED SINGLE SOURCE OF TRUTH

All performance documentation should state:

```
L0 Lexer Performance:
- With standard OCaml: 31.40ms (FAILS ≤20ms target)
- With Flambda2 compiler: 17-18ms (MEETS ≤20ms target)
- Requirement: OCaml 5.1.1+flambda2 with specific flags
- Test corpus: perf_smoke_big.tex (1.1MB)
```

No other numbers should appear anywhere.