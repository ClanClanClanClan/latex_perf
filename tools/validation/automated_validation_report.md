# Automated Validation Report

## TYPO-001 - TYPO-001_comprehensive
**Status**: ❌ FAILED
**Precision**: 37.5%
**Recall**: 42.9%

Total sections tested: 10
Actual matches found: 8

False Positives (5):
  - Position 910-917: '"
And "'
  - Position 555-562: ''hello''
  - Position 895-937: '"Quote at start"
And "quote
at line break"'
  - Position 543-573: '"he told me 'hello' yesterday"'
  - Position 464-473: '"another"'

False Negatives (4):
  - Quotes at line boundaries: '"quote
at line break"'
  - Mixed contexts - only non-code quotes should match: '"another"'
  - Quotes at line boundaries: '"Quote at start"'
  - Nested quotes with single inside double: '"he told me 'hello' yesterday"'

Section Results:
  Simple quotes in normal text: ✓
  Quotes inside verbatim environment: ✓
  Quotes inside inline math: ✓
  Quotes inside texttt (code formatting): ✓
  Mixed contexts - only non-code quotes should match: ✓
  Nested quotes with single inside double: ✓
  Quotes in code listing environment: ✓
  Quotes in LaTeX comments: ✓
  Empty quote marks: ✓
  Quotes at line boundaries: ✓

--------------------------------------------------

## TYPO-002 - TYPO-002_comprehensive
**Status**: ❌ FAILED
**Precision**: 75.0%
**Recall**: 75.0%

Total sections tested: 5
Actual matches found: 4

False Positives (1):
  - Position 365-368: '...'

False Negatives (1):
  - Multiple ellipses in one line: '...'

Section Results:
  Three dots in normal text: ✓
  Ellipsis in verbatim environment: ✓
  Ellipsis in math mode: ✓
  Period in file extension: ✓
  Multiple ellipses in one line: ✓

--------------------------------------------------
