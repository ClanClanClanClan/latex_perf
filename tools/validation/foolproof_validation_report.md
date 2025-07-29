# Foolproof Validation Report

## TYPO-001
**Overall**: 5/14 passed (35.7%)
**False Positives**: 8
**False Negatives**: 0

### Failed Tests

#### simple_double_quotes
**Description**: Simple double quotes should be converted to smart quotes
**Error**: Rule modified text when it should not have
**Input**:
```latex
He said "hello" to her.
```
**Expected**:
```latex
He said "hello" to her.
```
**Actual**:
```latex
He said “hello” to her.
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-He said "hello" to her.+He said “hello” to her.
```

#### simple_single_quotes
**Description**: Single quotes should be converted (including apostrophes)
**Error**: Rule modified text when it should not have
**Input**:
```latex
It's a 'test' case.
```
**Expected**:
```latex
It's a 'test' case.
```
**Actual**:
```latex
It's a “test” case.
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-It's a 'test' case.+It's a “test” case.
```

#### mixed_contexts
**Description**: Only quotes outside code contexts should change
**Error**: Rule modified text when it should not have
**Input**:
```latex
Normal "quote" and \texttt{"code"} and "another".
```
**Expected**:
```latex
Normal "quote" and \texttt{"code"} and "another".
```
**Actual**:
```latex
Normal “quote” and \texttt{"code"} and “another”.
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-Normal "quote" and \texttt{"code"} and "another".+Normal “quote” and \texttt{"code"} and “another”.
```

#### empty_quotes
**Description**: Empty quotes should still be converted
**Error**: Rule modified text when it should not have
**Input**:
```latex
Empty quotes: ""
```
**Expected**:
```latex
Empty quotes: ""
```
**Actual**:
```latex
Empty quotes: “”
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-Empty quotes: ""+Empty quotes: “”
```

#### nested_quotes
**Description**: Nested quotes should be handled correctly
**Error**: Output does not match expected
**Input**:
```latex
She said "he told me 'hello' yesterday".
```
**Expected**:
```latex
She said "he told me ‘hello’ yesterday".
```
**Actual**:
```latex
She said “he told me ‘hello’ yesterday”.
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-She said "he told me ‘hello’ yesterday".+She said “he told me ‘hello’ yesterday”.
```

#### quotes_with_newline
**Description**: Quotes spanning multiple lines should work
**Error**: Rule modified text when it should not have
**Input**:
```latex
"Quote
spanning lines"
```
**Expected**:
```latex
"Quote
spanning lines"
```
**Actual**:
```latex
“Quote
spanning lines”
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1,2 +1,2 @@
-"Quote
-spanning lines"+“Quote
+spanning lines”
```

#### quote_at_start
**Description**: Quote at document start
**Error**: Rule modified text when it should not have
**Input**:
```latex
"Quote" at the start.
```
**Expected**:
```latex
"Quote" at the start.
```
**Actual**:
```latex
“Quote” at the start.
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-"Quote" at the start.+“Quote” at the start.
```

#### quote_at_end
**Description**: Quote at document end
**Error**: Rule modified text when it should not have
**Input**:
```latex
Ends with "quote"
```
**Expected**:
```latex
Ends with "quote"
```
**Actual**:
```latex
Ends with “quote”
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-Ends with "quote"+Ends with “quote”
```

#### complex_document
**Description**: Complex document with multiple contexts
**Error**: Rule modified text when it should not have
**Input**:
```latex
\documentclass{article}
\begin{document}
He said "hello" in the meeting.
\begin{verbatim}
print("unchanged")
\end{verbatim}
The \texttt{"code"} remains as is.
But "this quote" changes.
\end{document}
```
**Expected**:
```latex
\documentclass{article}
\begin{document}
He said "hello" in the meeting.
\begin{verbatim}
print("unchanged")
\end{verbatim}
The \texttt{"code"} remains as is.
But "this quote" changes.
\end{document}
```
**Actual**:
```latex
\documentclass{article}
\begin{document}
He said “hello” in the meeting.
\begin{verbatim}
print("unchanged")
\end{verbatim}
The \texttt{"code"} remains as is.
But “this quote” changes.
\end{document}
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1,9 +1,9 @@
 \documentclass{article}
 \begin{document}
-He said "hello" in the meeting.
+He said “hello” in the meeting.
 \begin{verbatim}
 print("unchanged")
 \end{verbatim}
 The \texttt{"code"} remains as is.
-But "this quote" changes.
+But “this quote” changes.
 \end{document}
```

### Performance
- Average: 0.55ms
- Max: 6.96ms
- Min: 0.02ms

---

## TYPO-002
**Overall**: 9/10 passed (90.0%)
**False Positives**: 1
**False Negatives**: 0

### Failed Tests

#### four_dots
**Description**: Four dots are not standard ellipsis
**Error**: Rule modified text when it should not have
**Input**:
```latex
Too many....
```
**Expected**:
```latex
Too many....
```
**Actual**:
```latex
Too many….
```
**Diff**:
```diff
--- expected
+++ actual
@@ -1 +1 @@
-Too many....+Too many….
```

### Performance
- Average: 0.06ms
- Max: 0.48ms
- Min: 0.00ms

---
