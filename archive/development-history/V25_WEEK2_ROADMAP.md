# V25 WEEK 2 ROADMAP - VALIDATOR DSL FOUNDATION

**Current Status**: Week 1 complete - L0/L1 integration working with stubs  
**Next Phase**: Weeks 1-4 focus on Validator Pattern DSL (per comprehensive plan)

---

## WEEK 2 OBJECTIVES (From Comprehensive Plan)

### Primary Goal: Begin Validator Pattern DSL
According to the plan, weeks 1-4 should deliver:
- Validator DSL implementation
- Pattern mining from 100+ ground truth files  
- 30-50 validator templates ready
- Proof automation tactics library

### Week 2 Specific Tasks

#### 1. Define Validator Pattern Types
```ocaml
type validator_pattern = {
  family: string;           (* MATH, TYPO, STYLE, etc *)
  id_prefix: string;        (* MATH-001, TYPO-002, etc *)
  detector: token list -> issue list;
  fix_template: string -> string;
  proof_template: proof_tactic list;
  test_cases: (string * expected_result) list;
}
```

#### 2. Create Ground Truth Infrastructure
- Locate/create ground truth files
- Define ground truth format
- Build parser for ground truth data

#### 3. Start Pattern Mining System
```python
class ValidatorPatternMiner:
    def extract_patterns(self, ground_truth_file):
        # Extract validation patterns from annotated files
```

#### 4. Coq Extraction (If Time Permits)
- Set up extraction configuration
- Extract lexer from `src/coq/lexer/Lexer.v`
- Replace stub with real implementation

---

## IMPLEMENTATION PRIORITIES

### Must Have (Week 2)
1. Validator pattern type definitions
2. Basic DSL structure  
3. Ground truth file format
4. Initial pattern examples

### Should Have
1. Pattern compiler skeleton
2. Test framework for validators
3. Documentation of DSL syntax

### Nice to Have
1. Coq extraction working
2. First generated validator
3. Proof template examples

---

## SUCCESS CRITERIA

Week 2 is successful if:
- [ ] Validator DSL types defined and compile
- [ ] Ground truth format specified
- [ ] At least 10 example patterns documented
- [ ] Basic pattern → validator compilation demonstrated
- [ ] Foundation ready for weeks 3-4 expansion

---

## TECHNICAL DECISIONS NEEDED

1. **DSL Syntax**: S-expressions vs custom syntax?
2. **Pattern Language**: Regex vs token patterns vs AST patterns?
3. **Ground Truth Format**: YAML vs JSON vs custom?
4. **Proof Strategy**: Ltac vs Ltac2 vs manual?

---

## RISKS & MITIGATION

1. **Risk**: DSL too complex
   - **Mitigation**: Start with simple regex-based patterns

2. **Risk**: Pattern mining yields poor results
   - **Mitigation**: Manual pattern creation fallback

3. **Risk**: Proof automation too ambitious
   - **Mitigation**: Focus on simple proof templates first

---

## NOTES FROM V25 PLAN

The comprehensive plan expects 15x productivity improvement through automation:
- Historical: 0.77 validators/week
- Required: 10-12 validators/week
- Solution: Automated generation via DSL

This week lays the foundation for that automation.

---

*Roadmap Date: 2025-07-29*  
*Next Review: End of Week 2*