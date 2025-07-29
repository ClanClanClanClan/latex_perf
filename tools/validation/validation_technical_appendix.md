# Technical Appendix: LaTeX Perfectionist Validation Challenge

## A. Detailed Rule Implementation Example

### TYPO-001: Smart Quotes Rule (Full Implementation)

```python
import re
from typing import List
from latex_perfectionist.core.types import Issue, Fix, RuleResult
from latex_perfectionist.core.severity import Severity

# Rule metadata
RULE_ID = "TYPO-001"
MESSAGE = "Use proper curly quotes instead of straight ASCII quotes"

# Pattern to find quotes
PATTERN = re.compile(r'(?<![\\\\])("([^"]*)")', re.DOTALL)

def _is_in_verbatim(text: str, start: int, end: int) -> bool:
    """Check if position is inside verbatim environment."""
    before = text[:start]
    
    # Count \begin{verbatim} and \end{verbatim} before position
    begin_count = len(re.findall(r'\\begin\{verbatim\}', before))
    end_count = len(re.findall(r'\\end\{verbatim\}', before))
    
    # If more begins than ends, we're inside verbatim
    return begin_count > end_count

def _is_in_math(text: str, start: int, end: int) -> bool:
    """Check if position is inside math mode."""
    before = text[:start]
    
    # Check inline math $...$
    dollar_count = before.count('$') - before.count('\\$')
    if dollar_count % 2 == 1:
        return True
    
    # Check display math \[...\]
    display_begin = len(re.findall(r'\\\[', before))
    display_end = len(re.findall(r'\\\]', before))
    if display_begin > display_end:
        return True
        
    return False

def _is_in_texttt(text: str, start: int, end: int) -> bool:
    """Check if position is inside \texttt{} command."""
    # Find all \texttt{ positions before start
    pattern = r'\\texttt\{'
    
    # This is where it gets complex - need to track brace nesting
    # to find the closing } that matches \texttt{
    # Current implementation has bugs here!
    
    # ... complex brace matching logic ...
    
def audit(text: str, cfg: dict) -> RuleResult:
    """Main rule function."""
    issues = []
    fixes = []
    
    for match in PATTERN.finditer(text):
        # Check exclusion contexts
        if (_is_in_verbatim(text, match.start(), match.end()) or
            _is_in_math(text, match.start(), match.end()) or
            _is_in_texttt(text, match.start(), match.end())):
            continue
        
        # Create issue
        line_num = text[:match.start()].count('\n') + 1
        issues.append(Issue(
            type=RULE_ID,
            level=Severity.ERROR.value,
            line=line_num,
            message=MESSAGE
        ))
        
        # Create fix - replace straight quotes with smart quotes
        fixes.append(Fix(
            start=match.start(),
            end=match.end(),
            replacement=match.group(0).replace('"', '"').replace('"', '"')
        ))
    
    return RuleResult(issues, fixes)
```

## B. Why Position-Based Testing Fails

### Example: Position Calculation Errors

```python
# Test case with positions
text = 'Say "hello" and "world".'
#       0123456789012345678901234

# Expected matches:
# First quote: positions 4-11 ("hello")  
# Second quote: positions 16-23 ("world")

# But after applying first fix:
text = 'Say "hello" and "world".'  # Smart quotes are 3 bytes each in UTF-8!
#       012345678901234567890123456789  # Positions all shifted!

# Second fix now applies at wrong position
```

### UTF-8 Byte vs Character Position Issues

```python
text = 'Café "quote"'
# Character positions: C=0, a=1, f=2, é=3, space=4, "=5
# Byte positions: C=0, a=1, f=2, é=3-4 (2 bytes!), space=5, "=6

# Regex returns byte positions, but some tools expect character positions
```

## C. Context Detection Edge Cases

### 1. Nested Environments
```latex
\begin{figure}
  \begin{verbatim}
    "This quote is in verbatim"
  \end{verbatim}
  \caption{But "this" quote is not}
\end{figure}
```

### 2. Overlapping Commands
```latex
\texttt{Code with \emph{emphasis "quote"} inside}
%                                ↑ Is this in \texttt or not?
```

### 3. Math Mode Variants
```latex
% All of these are math mode:
$"quote"$
$$"quote"$$  
\["quote"\]
\("quote"\)
\begin{equation}"quote"\end{equation}
\begin{align}"quote"\end{align}
\begin{math}"quote"\end{math}
```

### 4. Comment Edge Cases
```latex
Normal text % Comment with "quote"
"This should change" % But "this" should not
\% Not a comment with "quotes"
```

### 5. Command Argument Parsing
```latex
\texttt{"simple"}  % Easy
\texttt{text with {nested} braces and "quote"}  % Hard!
\texttt{%
  "Multiline"
}  % Very hard!
```

## D. Mathematical Properties We Need to Verify

### 1. Context Function Properties

For any context detection function `is_in_context(text, start, end)`:

**Property 1: Monotonicity**
```
If is_in_context(text, a, b) = true
And a <= c <= d <= b
Then is_in_context(text, c, d) = true
```

**Property 2: Boundary Precision**
```
If context starts at position p:
  is_in_context(text, p-1, p) = false
  is_in_context(text, p, p+1) = true
```

**Property 3: Consistency**
```
is_in_context(text, a, b) should return same result
regardless of how many times called
```

### 2. Fix Application Properties

**Property 1: Order Independence** (when non-overlapping)
```
apply_fixes([fix1, fix2]) == apply_fixes([fix2, fix1])
when fix1.end <= fix2.start or fix2.end <= fix1.start
```

**Property 2: Idempotency**
```
apply_rule(apply_rule(text)) == apply_rule(text)
```

**Property 3: Preservation**
```
If no issues found: apply_rule(text) == text
(No changes to valid documents)
```

## E. Performance Constraints

### Document Size Distribution
- Median LaTeX document: ~5KB
- Large documents: ~500KB  
- Extreme cases: ~5MB (books)

### Performance Requirements
- Instant rules: <100ms on median document
- Fast rules: <1s on large document
- Deep rules: <30s on extreme cases

### Memory Constraints
- Must handle documents that don't fit in memory
- Cannot create full AST (LaTeX parser would use too much memory)
- Regex matching must be streaming-capable

## F. Formal Specification Challenge

### Could We Formally Verify Rules?

```coq
(* Formal specification in Coq pseudo-code *)
Definition quote_rule (text : string) : string :=
  transform_quotes text (fun pos => 
    not (in_verbatim text pos) ∧
    not (in_math text pos) ∧ 
    not (in_comment text pos)).

Theorem quote_rule_preserves_verbatim :
  ∀ text pos,
    in_verbatim text pos →
    nth_char (quote_rule text) pos = nth_char text pos.
```

### Challenges:
1. LaTeX has no formal grammar
2. Rules use regex, not parsers
3. Would need to model all package behaviors
4. Proof complexity exceeds development resources

## G. Test Oracle Problem

### What is "Correct" Output?

For many rules, the correct output is subjective or context-dependent:

```latex
% British vs American style
"Hello", she said.  % British: comma inside quotes  
"Hello," she said.  % American: comma outside quotes

% Which is correct depends on document locale!
```

### Oracle Strategies

1. **Differential Oracle**: Compare with human expert fixes
2. **Specification Oracle**: Match formal style guide
3. **Consistency Oracle**: Same input → same output
4. **Preservation Oracle**: Non-targeted text unchanged

## H. Why Machine Learning Might Help

### 1. Edge Case Discovery
```python
# ML could find inputs that trigger unexpected behavior
adversarial_input = ml_model.generate_edge_case(rule)
# "\"\\begin{verbatim" - unclosed quote before verbatim!
```

### 2. Pattern Learning
```python
# Learn what "looks like" a false positive
features = extract_features(context)
is_false_positive = ml_classifier.predict(features)
```

### 3. Test Priority
```python
# Rank test cases by likelihood of finding bugs
test_priority = ml_model.score_test_importance(test_case)
```

## I. Alternative Approaches to Consider

### 1. Symbolic Execution
```python
# Symbolically execute rule to find all paths
paths = symbolic_execute(rule_function)
for path in paths:
    generate_test_to_cover(path)
```

### 2. Grammar-Based Fuzzing
```python
# Generate valid LaTeX using grammar
latex_grammar = load_latex_grammar()
test_doc = grammar_fuzzer.generate(latex_grammar)
```

### 3. Metamorphic Testing
```python
# Define relations that should hold
# If rule fixes "X", it should also fix " X "
test_metamorphic_relations(rule)
```

### 4. Contract-Based Testing
```python
@contract
def rule_function(text: str) -> str:
    """
    pre: valid_latex(text)
    post: valid_latex(result)
    post: len(result.fixes) == 0 implies result == text
    """
```

## J. The Fundamental Questions

1. **Can we achieve 100% accuracy without parsing LaTeX fully?**
2. **Is regex-based context detection fundamentally limited?**
3. **How do we validate rules that depend on style preferences?**
4. **Can we prove correctness without formal specifications?**
5. **What is the minimum test set that gives maximum confidence?**

---

*This technical appendix provides deeper implementation details and challenges for the validation system design.*