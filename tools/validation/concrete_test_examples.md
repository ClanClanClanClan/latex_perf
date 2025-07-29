# Concrete Test Examples: What We Want vs What We Have

## Current Testing Approach (BAD)

```python
def test_typo_001_positions():
    text = 'He said "hello" to her.'
    result = rule.audit(text)
    
    # Manual position tracking - error prone!
    assert len(result.fixes) == 1
    assert result.fixes[0].start == 8
    assert result.fixes[0].end == 15
    assert result.fixes[0].replacement == '"hello"'
    
    # Problems:
    # 1. What if text has UTF-8 chars before the quote?
    # 2. What if we counted wrong?
    # 3. Doesn't test the actual OUTPUT
    # 4. Hard to debug when it fails
```

## Desired Testing Approach (GOOD)

```python
def test_typo_001_behavior():
    # Simple, clear test cases
    assert apply_rule('He said "hello" to her.') == 'He said "hello" to her.'
    assert apply_rule('Empty ""') == 'Empty ""'
    assert apply_rule('"Quote" at start') == '"Quote" at start'
    
    # Context exclusions - no changes expected
    assert apply_rule('\\texttt{"code"}') == '\\texttt{"code"}'  # NO CHANGE
    assert apply_rule('$x = "math"$') == '$x = "math"$'  # NO CHANGE
    assert apply_rule('% Comment "quote"') == '% Comment "quote"'  # NO CHANGE
    
    # Benefits:
    # 1. Tests actual behavior
    # 2. Easy to understand
    # 3. Easy to debug
    # 4. No position calculations
```

## Real-World Test Cases We Need

### 1. Simple Cases (Should Work)
```latex
Input:  She said "hello" to him.
Output: She said "hello" to him.

Input:  'Single quotes' work too.  
Output: 'Single quotes' work too.

Input:  Nested "outer 'inner' quotes" test.
Output: Nested "outer 'inner' quotes" test.
```

### 2. Context Exclusions (Should NOT Change)
```latex
# Verbatim environment
Input:  \begin{verbatim}
        Print "Hello World"
        \end{verbatim}
Output: \begin{verbatim}
        Print "Hello World"  ← NO CHANGE
        \end{verbatim}

# Math mode  
Input:  The formula $f(x) = "constant"$ is wrong.
Output: The formula $f(x) = "constant"$ is wrong.
                              ↑ NO CHANGE

# Code formatting
Input:  Use \texttt{"quotedString"} in code.
Output: Use \texttt{"quotedString"} in code.
                     ↑ NO CHANGE

# Comments
Input:  Normal "text" % but not "this"
Output: Normal "text" % but not "this"  
        ↑ CHANGED      ↑ NOT CHANGED
```

### 3. Edge Cases That Break Current Rules

#### Case 1: Quote at Exact Boundary
```latex
Input:  "\begin{verbatim}code\end{verbatim}"
Output: "\begin{verbatim}code\end{verbatim}"
        ↑ Should this change? It's OUTSIDE verbatim!
```

#### Case 2: Interleaved Contexts  
```latex
Input:  Start "quote with \texttt{embedded "code"} inside" end.
Output: Start "quote with \texttt{embedded "code"} inside" end.
              ↑ CHANGE              ↑ NO CHANGE    ↑ CHANGE?
```

#### Case 3: Incomplete Contexts
```latex
Input:  Broken "quote \begin{verbatim} oops no end
Output: ??? What should happen here?
```

#### Case 4: Unicode Confusion
```latex
Input:  "Hello" and "World"  # Mixed straight and smart quotes
Output: "Hello" and "World"  # All smart quotes
```

## Test Properties We Must Verify

### 1. Idempotency Test
```python
def test_idempotency(text):
    once = apply_rule(text)
    twice = apply_rule(once)
    assert once == twice  # Must be stable!
```

### 2. Context Boundary Test
```python
def test_context_boundaries():
    # Quotes immediately before/after context
    cases = [
        ('"\begin{verbatim}', True),   # Should change
        ('\begin{verbatim}"', False),  # Should NOT change  
        ('"\end{verbatim}', False),    # Should NOT change
        ('\end{verbatim}"', True),     # Should change
    ]
    
    for text, should_change in cases:
        result = apply_rule(text)
        if should_change:
            assert result != text
        else:
            assert result == text
```

### 3. Composition Test
```python
def test_rule_composition():
    # Multiple rules should compose correctly
    text = 'She said "hello..." to him.'
    
    # Apply both quote and ellipsis rules
    step1 = apply_typo_001(text)  # Fix quotes
    step2 = apply_typo_002(step1)  # Fix ellipsis
    
    # Should get both fixes
    assert step2 == 'She said "hello…" to him.'
```

### 4. Performance Test
```python
def test_performance():
    # Generate large document
    huge_doc = "Chapter 1\n" + ('He said "hello" to her. ' * 10000)
    
    start = time.time()
    result = apply_rule(huge_doc)
    duration = time.time() - start
    
    assert duration < 0.1  # Must be fast!
    assert result.count('"') == 10000  # All quotes fixed
```

## What Makes a Good Test

### Bad Test (Current Approach)
```python
def test_quotes():
    # Vague test name
    text = generate_random_latex()  # Random = not reproducible
    result = rule.audit(text)
    assert len(result.issues) > 0  # What are we testing?
```

### Good Test (What We Want)
```python
def test_quotes_not_changed_in_verbatim():
    # Clear test name explains intent
    
    # Explicit input/output
    input_text = '''
    \begin{verbatim}
    print("Hello World")
    \end{verbatim}
    '''
    
    expected = input_text  # Should not change
    actual = apply_rule(input_text)
    
    assert actual == expected
    # If fails, we know EXACTLY what went wrong
```

## The Ultimate Test: Real Paper

```latex
% A real LaTeX document section that exercises many edge cases
\documentclass{article}
\usepackage{listings}

\begin{document}
\section{Introduction}

The programmer said "Hello World" is the traditional first program.
In Python, you write \texttt{print("Hello World")} to display text.

\begin{lstlisting}[language=Python]
def greet(name):
    return f"Hello, {name}!"
\end{lstlisting}

% TODO: Add "more examples" later
Mathematics uses different conventions: $f: A \to B$ means "maps to".

\begin{verbatim}
The "raw" text here should never change!
\end{verbatim}

As Knuth said, "Premature optimization is the root of all evil"\footnote{But "profile first" is good advice}.

\end{document}
```

Expected output: Only quotes in normal text change, everything in special contexts remains untouched.

## Summary: What We Need

1. **Behavior-based tests**: Input → Expected Output
2. **Comprehensive coverage**: All contexts and edge cases  
3. **Easy debugging**: When test fails, immediately see why
4. **No manual calculations**: No position tracking
5. **Scalable approach**: Easy to add new test cases
6. **Fast execution**: Thousands of tests in seconds
7. **Deterministic**: Same input always gives same output

The validation system must make it trivial to write tests like:

```python
test("name", 
     input="any LaTeX text",
     output="expected result")
```

And automatically verify all the properties we care about.