# LaTeX Perfectionist Validation Challenge: Achieving 100% Accuracy at Scale

## Executive Summary

We need a validation system for LaTeX Perfectionist, a rule-based LaTeX linter that must achieve 100% accuracy (zero false positives) across hundreds of rules. Current approaches fail due to fundamental design flaws. We seek innovative solutions that enable a single developer to validate rules with mathematical certainty while avoiding manual review of thousands of documents.

## Background: What is LaTeX Perfectionist?

LaTeX Perfectionist is a linter that automatically fixes typography, formatting, and style issues in LaTeX documents. Rules are written in a DSL and compiled to Python. Example rules:

- **TYPO-001**: Convert straight quotes `"hello"` to smart quotes `"hello"`
- **TYPO-002**: Convert three dots `...` to proper ellipsis `…`
- **MATH-001**: Ensure consistent equation numbering
- **STYLE-001**: Enforce consistent spacing around math operators

### Critical Requirement: 100% Accuracy

Unlike typical linters that tolerate some false positives, LaTeX Perfectionist requires **100% precision** because:
1. LaTeX documents are often camera-ready publications
2. False positives can break compilation or change meaning
3. Authors trust the tool to never make incorrect changes
4. The tool may run automatically in CI/CD pipelines

## The Validation Challenge

### What We Need to Validate

For each rule, we must verify:

1. **Precision**: Every detected issue is a real issue (no false positives)
2. **Context Awareness**: Rules respect LaTeX environments exactly
   - No changes inside `\begin{verbatim}...\end{verbatim}`
   - No changes inside math mode `$...$`
   - No changes inside comments `% ...`
   - No changes inside code commands `\texttt{...}`
3. **Fix Correctness**: The applied fix produces the expected output
4. **Idempotency**: Running the rule multiple times converges (fix(fix(x)) = fix(x))
5. **Performance**: Rules complete in reasonable time on large documents
6. **Edge Cases**: Handles UTF-8, nested structures, malformed LaTeX

### Why Current Approaches Fail

#### 1. Manual Corpus Review (Infeasible)
- Would require reviewing 10,000+ papers manually
- One person cannot create ground truth for thousands of documents
- Doesn't scale to hundreds of rules

#### 2. Position-Based Testing (Error-Prone)
```python
# Current approach - tracking positions manually
assert fix.start == 10
assert fix.end == 23
assert fix.replacement == ""hello""
```
Problems:
- Position calculations are error-prone
- Positions change when fixes are applied
- Doesn't test actual output
- Hard to debug when tests fail

#### 3. Synthetic Tests (Incomplete)
```python
# Simple synthetic tests miss edge cases
test("simple", '"hello"', '"hello"')  # Works
# But misses: nested quotes, quotes at boundaries, quotes near commands, etc.
```

#### 4. Property-Based Testing (Insufficient)
- Can find crashes but not correctness issues
- Cannot verify that fixes are appropriate
- Doesn't help with context boundary detection

## Constraints

1. **Single Developer**: Solution must be feasible for one person
2. **100% Automation**: Cannot rely on manual review at scale
3. **Deterministic**: Results must be reproducible
4. **Debuggable**: When validation fails, must clearly show why
5. **Scalable**: Must work for hundreds of rules without linear effort
6. **Fast Iteration**: Changes to rules must be quickly re-validated

## Technical Context

### Rule Structure
```python
def audit(text: str, config: dict) -> RuleResult:
    """Check document and return issues + fixes."""
    issues = []
    fixes = []
    
    for match in PATTERN.finditer(text):
        # Check if match is in excluded context
        if _is_in_verbatim(text, match.start(), match.end()):
            continue
            
        # Create issue and fix
        issues.append(Issue(...))
        fixes.append(Fix(
            start=match.start(),
            end=match.end(), 
            replacement=calculate_replacement(match)
        ))
    
    return RuleResult(issues, fixes)
```

### The Context Detection Problem

Rules must detect context boundaries with byte-level precision:

```latex
Normal "quote" should change.
\begin{verbatim}
"quote" should NOT change here
\end{verbatim}
Back to "normal" quotes.
```

Context detection functions must handle:
- Nested environments
- Overlapping contexts  
- Malformed LaTeX
- Commands that span lines

### Real-World Complexity

Academic LaTeX documents contain:
- 50+ different packages each with their own commands
- Custom macros that redefine standard behavior
- Mixed languages and Unicode
- Computer-generated LaTeX
- Legacy documents with outdated syntax

## What We've Tried

### 1. Synthetic Ground Truth Generator
```python
# Generated test documents with known behavior
sections = [
    Section('Normal "quote"', should_fix=True),
    Section('\\texttt{"quote"}', should_fix=False),
    Section('$"quote"$', should_fix=False)
]
```
**Result**: Works but misses real-world edge cases

### 2. Smart Corpus Selection
```python
# Selected papers with specific features
papers = select_papers_with_features({
    'has_verbatim': 10,
    'has_math_quotes': 10,
    'has_code_blocks': 10
})
```
**Result**: Better coverage but still requires manual verification

### 3. Differential Testing
```python
# Compare with other tools
result_ours = our_rule(text)
result_theirs = other_linter(text)
differences = compare(result_ours, result_theirs)
```
**Result**: Other tools don't have our accuracy requirements

### 4. Behavior-Based Testing
```python
# Test input → output transformation
def test(input_text, expected_output):
    actual = apply_rule(input_text)
    assert actual == expected_output
```
**Result**: Good approach but need better test generation

## The Core Challenge

How do we systematically generate comprehensive test cases that:
1. Cover all edge cases without manual enumeration
2. Verify context boundaries precisely
3. Scale to hundreds of rules
4. Provide ground truth without manual annotation
5. Enable rapid iteration and debugging

## Success Criteria

A successful solution will:

1. **Automatically generate comprehensive test suites** that achieve high confidence in rule correctness
2. **Require zero manual document review** for ground truth creation
3. **Detect subtle bugs** like off-by-one errors in context detection
4. **Provide clear debugging** when tests fail
5. **Scale linearly** with number of rules (not documents)
6. **Enable rapid iteration** - validate changes in minutes, not days
7. **Guarantee 100% precision** with mathematical certainty

## Specific Technical Challenges

### 1. Context Boundary Detection
How to verify that `_is_in_verbatim()` returns true for exactly the right byte ranges?

### 2. Unicode Handling
```python
# These look identical but are different:
"hello"  # U+0022 straight quotes
"hello"  # U+201C/U+201D smart quotes
```

### 3. Nested Structure Handling
```latex
\textbf{Bold with \emph{nested "quote"} inside}
```

### 4. LaTeX Command Parsing Without Full Parser
Rules use regex, not a full LaTeX parser. How to ensure robustness?

### 5. Fix Composition
When multiple rules run, fixes must compose correctly.

## Resources Available

1. **arXiv Corpus**: Access to thousands of real LaTeX papers
2. **Rule DSL Compiler**: Generates Python code from rule specifications  
3. **Existing Rules**: ~50 rules already implemented (but not fully validated)
4. **Test Infrastructure**: Python testing framework ready
5. **One Dedicated Developer**: Full-time focus on validation

## The Ask

Design a validation methodology and system that:

1. Enables 100% accuracy validation without manual corpus review
2. Scales to hundreds of rules with linear effort
3. Provides mathematical confidence in correctness
4. Makes debugging failures trivial
5. Can be implemented by a single developer

We seek innovative approaches that may include:
- Novel test generation strategies
- Formal verification techniques
- Automated ground truth synthesis
- Advanced property-based testing
- Differential testing innovations
- Machine learning for edge case discovery
- Symbolic execution approaches
- Or completely different paradigms we haven't considered

The solution should be practical, not just theoretical, and implementable with available resources.

## Appendix: Concrete Examples

### Example 1: Simple Quote Fix
```latex
Input:  He said "hello" to her.
Output: He said "hello" to her.
```

### Example 2: Context Exclusion  
```latex
Input:  Normal "quote" and \texttt{"code"} done.
Output: Normal "quote" and \texttt{"code"} done.
        ↑ changed              ↑ NOT changed
```

### Example 3: Edge Case - Quote at Environment Boundary
```latex
Input:  "\begin{verbatim}text\end{verbatim}"
Output: "\begin{verbatim}text\end{verbatim}"
        ↑ should this change? (not inside verbatim)
```

### Example 4: Nested Structures
```latex
Input:  She said "he told me 'hello' yesterday".  
Output: She said "he told me 'hello' yesterday".
```

### Example 5: Math Mode Boundary
```latex
Input:  The equation $f(x) = "?"$ is wrong.
Output: The equation $f(x) = "?"$ is wrong.
                            ↑ NOT changed (inside math)
```

---

*End of Challenge Specification*