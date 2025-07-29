# LaTeX Perfectionist v24 - Rules Directory

## Files

- **rules.yaml** - Original rule definitions (438 rules, phase-based organization)
- **rules_v2.yaml** - Enhanced rule definitions (612 rules, category-based organization)
- **rules_unified.yaml** - (TO BE CREATED) Merged ruleset combining both versions

## Rule Organization

### Phase-based (rules.yaml)
- L0_Lexer - Lexical analysis rules
- L1_Expanded - Post-expansion rules  
- L2_Ast - AST-based rules
- L3_Semantics - Semantic analysis rules
- L4_Style - Style and formatting rules

### Category-based (rules_v2.yaml)
- ACCESS - Accessibility rules
- SEC - Security rules
- CJK/RTL - Internationalization rules
- FONT/COL - Typography and color rules
- MATH - Mathematical typesetting rules
- And many more categories...

## Implementation Status
- Rules defined: 612
- Rules implemented: ~15 (3%)
- Rules with formal proofs: 0

## Next Steps
1. Create rules_unified.yaml merging both versions
2. Update Coq implementations to reference unified rules
3. Implement priority L0_Lexer rules with proofs