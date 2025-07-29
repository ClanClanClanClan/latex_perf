# LaTeX Perfectionist Validation System: Problem Statement

## Executive Summary

We need to design a systematic automated validation system for LaTeX Perfectionist, a tool that finds and fixes style issues in LaTeX documents. The current validation approach has fundamental flaws that make it unreliable. We need a solution that can formally verify that our rules work correctly in all cases.

## Background

### What is LaTeX Perfectionist?

LaTeX Perfectionist is a linting tool for LaTeX documents. It contains "rules" that:
1. **Detect** style issues (e.g., straight quotes instead of curly quotes)
2. **Fix** these issues automatically (e.g., replace `"text"` with `"text"`)

Each rule is a Python function that takes a LaTeX document and returns:
- A list of `Issue` objects (what was found wrong)
- A list of `Fix` objects (how to fix it)

### Example Rule Structure

```python
# Rule TYPO-001: Convert straight quotes to smart quotes
def audit(document: str, config: dict) -> RuleResult:
    issues = []
    fixes = []
    
    # Find all straight quotes not in protected contexts
    for match in find_quotes(document):
        if not in_verbatim(match) and not in_math(match):
            issues.append(Issue(
                type="typography",
                level="error", 
                line=get_line_number(match),
                message="Use smart quotes instead of straight quotes"
            ))
            fixes.append(Fix(
                start=match.start(),
                end=match.end(),
                replacement=convert_to_smart_quotes(match.text)
            ))
    
    return RuleResult(issues=issues, fixes=fixes)
```

### The Core Challenge

Rules must be context-aware. For example, quotes should be converted in normal text but NOT inside:
- `\begin{verbatim}...\end{verbatim}` blocks
- Math mode: `$...$` or `\[...\]`
- Code spans: `\texttt{...}`
- Listings: `\begin{lstlisting}...\end{lstlisting}`
- And many other contexts

## The Validation Problem

### What We're Trying to Validate

1. **Detection Accuracy**: Does the rule find all issues it should find AND avoid false positives?
2. **Fix Correctness**: Do the fixes produce the expected output?
3. **Context Boundaries**: Does the rule respect protected regions exactly?
4. **Idempotency**: Is `fix(fix(document)) == fix(document)`?
5. **Performance**: Does the rule run fast enough on large documents?
6. **Edge Cases**: Does it handle Unicode, nested contexts, overlapping matches, etc.?

### Current Validation Approach (Failing)

The current system uses "ground truth" JSON files that specify:
```json
{
  "document_name": "TYPO-001_comprehensive",
  "sections": [
    {
      "description": "Simple quotes in normal text",
      "start_pos": 47,
      "end_pos": 77,
      "content": "This is a \"simple quote\" test.",
      "rule_behaviors": {
        "TYPO-001": {
          "should_match": true,
          "expected_matches": [
            {
              "start": 10,
              "end": 24,
              "text": "\"simple quote\"",
              "absolute_start": 57,
              "absolute_end": 71
            }
          ]
        }
      }
    }
  ]
}
```

### Why Current Validation Fails

1. **Position Calculation Errors**
   - Uses absolute byte positions that must be manually calculated
   - Positions drift when documents are edited
   - Unicode characters break byte/character position assumptions
   - No way to verify positions are correct

2. **Shallow Validation**
   - Only checks if fixes occur at expected positions
   - Doesn't verify the actual output text
   - Can pass even if fixes are wrong

3. **Manual Test Creation**
   - Each test requires calculating exact positions
   - Extremely error-prone and time-consuming
   - Doesn't scale to hundreds of rules

4. **Poor Debugging**
   - When tests fail, it's unclear why
   - No visualization of what the rule actually did
   - Hard to understand boundary violations

## Available Resources

### Code Structure

```
src/
  latex_perfectionist/
    core/
      types.py          # Defines Issue, Fix, RuleResult classes
    rules/
      compiled/
        rule_typo_001.py  # Example rule implementation
validation/
  automated_validator.py  # Current (broken) validator
  synthetic_ground_truth/
    *.json              # Ground truth files
```

### Key Data Types

```python
@dataclass
class Fix:
    start: int          # Byte position (inclusive)
    end: int            # Byte position (exclusive)  
    replacement: str    # New text

@dataclass
class Issue:
    type: str          # Category
    level: str         # Severity
    line: int          # Line number (1-based)
    message: str       # Description

@dataclass
class RuleResult:
    issues: List[Issue]
    fixes: List[Fix]
```

### Constraints

1. **Cannot modify rule structure** - Rules must continue returning `RuleResult`
2. **Must handle existing rules** - Solution must work with already-written rules
3. **Performance matters** - Validation should complete in seconds, not minutes
4. **Cross-platform** - Must work on Windows, Mac, Linux
5. **No external services** - Everything must run locally

## Objectives for New Validation System

### Must Have

1. **100% Deterministic**
   - Same input always produces same result
   - No flaky tests due to timing, ordering, etc.

2. **Test Actual Output**
   - Apply fixes and compare resulting document
   - Not just positions, but actual transformed text

3. **Automatic Idempotency Testing**
   - Verify that running rules multiple times converges
   - Catch oscillating or unstable fixes

4. **Precise Boundary Testing**
   - Systematically verify context boundaries
   - Test edge cases like `\texttt{"` or `"}` boundaries

5. **Excellent Debugging**
   - When tests fail, show exactly what went wrong
   - Character-level diffs if needed
   - Visual representation of issues

6. **Easy Test Creation**
   - No manual position calculation
   - Declarative format that's human-readable
   - Should take <1 minute to add a new test

### Nice to Have

1. **Property-Based Testing**
   - Generate random test cases automatically
   - Find edge cases we didn't think of

2. **Mutation Testing**
   - Verify tests catch deliberately broken rules

3. **Performance Benchmarking**
   - Track rule performance over time
   - Catch performance regressions

## Concrete Examples of Problems

### Example 1: Position Calculation Bug

Current test specifies:
```json
"absolute_start": 57,
"absolute_end": 71
```

But if the document has a UTF-8 character before position 57, the byte position doesn't match the character position, and the test fails mysteriously.

### Example 2: Boundary Detection Failure

Input: `Before \texttt{"code"} after`

The rule might:
- Correctly skip the quote inside `\texttt{}`
- But also skip the `}` character
- Or include the `{` character
- No way to verify exact boundary behavior

### Example 3: Fix Correctness Not Tested

Rule matches `"test"` at position 10-16.
Current validator only checks that a fix exists at position 10-16.
But the fix might be:
- `"test"` (correct)
- `"test"` (wrong quotes)  
- `«test»` (wrong style)
- `'test'` (completely wrong)

Current validator would pass all of these!

### Example 4: Idempotency Failure

Document: `Mix of "straight" and "curly" quotes`

First pass: `Mix of "straight" and "curly" quotes`
Second pass: `Mix of "straight" and "curly" quotes` (changes already-correct quotes)

This breaks idempotency but isn't tested.

## Success Criteria

A successful validation system must:

1. **Catch all rule bugs** - If a rule is broken, tests must fail
2. **Never have false failures** - Correct rules must always pass
3. **Provide clear debugging** - Failures must be easy to diagnose
4. **Scale efficiently** - Adding new rules/tests must be simple
5. **Run quickly** - Full validation in <10 seconds

## Technical Environment

- Python 3.8+
- Can use any pure Python libraries (pytest, hypothesis, etc.)
- Must work with existing rule structure
- Cannot require external tools (Docker, databases, etc.)

## The Challenge

Design a validation system that:

1. Solves all the problems listed above
2. Is elegant and maintainable
3. Makes writing tests enjoyable rather than painful
4. Provides confidence that rules work correctly
5. Scales to hundreds of rules without manual effort

The current approach of manually calculating positions and comparing them is fundamentally flawed. We need a completely different approach that tests behavior, not implementation details.

## Example Test Case (Ideal Format)

Here's what we envision an ideal test might look like:

```yaml
test: Quotes with verbatim environment
description: Ensure quotes are not changed inside verbatim blocks
input: |
  This is "before" the verbatim.
  \begin{verbatim}
  This is "inside" verbatim.
  \end{verbatim}
  This is "after" the verbatim.

expect:
  changes:
    - "before" -> "before"
    - "after" -> "after"
  unchanged:
    - "inside" (protected by verbatim)
    
  output: |
    This is "before" the verbatim.
    \begin{verbatim}
    This is "inside" verbatim.
    \end{verbatim}
    This is "after" the verbatim.

verify:
  idempotent: true
  performance: <50ms
```

This is just one possibility - we're open to any solution that meets our objectives.