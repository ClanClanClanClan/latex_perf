#!/usr/bin/env python3
"""
Concrete example of using the new foolproof validator.

This demonstrates how to:
1. Define tests using the new format
2. Run comprehensive validation
3. Debug failures effectively
"""

import sys
from pathlib import Path
sys.path.insert(0, 'src')

from new_validator_architecture import (
    FooledValidator, TestCase, TestType, ExpectedMatch, 
    ProtectedRegion, ValidationResult
)

# Example: Define comprehensive tests for TYPO-001 (smart quotes)
def create_typo_001_tests() -> list[TestCase]:
    """Create test cases for smart quote rule."""
    tests = []
    
    # Test 1: Basic quote replacement
    tests.append(TestCase(
        id="TYPO-001-basic",
        description="Basic straight to curly quote conversion",
        input_text='This is a "simple test" document.',
        test_type=TestType.FIX_CORRECTNESS,
        expected_output='This is a "simple test" document.',
        expected_matches=[
            ExpectedMatch(
                pattern='"simple test"',
                fix='"simple test"',
                count=1
            )
        ]
    ))
    
    # Test 2: Multiple quotes
    tests.append(TestCase(
        id="TYPO-001-multiple",
        description="Multiple quotes in one line",
        input_text='First "one" and second "two" here.',
        test_type=TestType.FIX_CORRECTNESS,
        expected_output='First "one" and second "two" here.',
        expected_matches=[
            ExpectedMatch(pattern='"one"', fix='"one"'),
            ExpectedMatch(pattern='"two"', fix='"two"')
        ]
    ))
    
    # Test 3: Verbatim boundary (critical test)
    tests.append(TestCase(
        id="TYPO-001-verbatim-boundary",
        description="Quotes at exact verbatim boundaries",
        input_text='''Before "this" quote.
\\begin{verbatim}
"This should not change"
\\end{verbatim}
After "this" quote.''',
        test_type=TestType.BOUNDARY,
        expected_matches=[
            ExpectedMatch(
                pattern='"this"',
                fix='"this"',
                before_marker='\\begin{verbatim}',
                count=1
            ),
            ExpectedMatch(
                pattern='"this"',
                fix='"this"',
                after_marker='\\end{verbatim}',
                count=1
            )
        ],
        expected_no_matches_in=[
            ProtectedRegion(
                start_marker='\\begin{verbatim}',
                end_marker='\\end{verbatim}',
                description='verbatim environment'
            )
        ]
    ))
    
    # Test 4: Math mode boundary
    tests.append(TestCase(
        id="TYPO-001-math-boundary",
        description="Quotes around inline math",
        input_text='The "equation" is $x = "y"$ where "y" is special.',
        test_type=TestType.BOUNDARY,
        expected_matches=[
            ExpectedMatch(pattern='"equation"', fix='"equation"'),
            ExpectedMatch(pattern='"y"', fix='"y"', after_marker='$')
        ],
        expected_no_matches_in=[
            ProtectedRegion(
                start_marker='$',
                end_marker='$',
                description='inline math'
            )
        ]
    ))
    
    # Test 5: Texttt boundary (code spans)
    tests.append(TestCase(
        id="TYPO-001-texttt-boundary",
        description="Quotes with \\texttt code spans",
        input_text='Use \\texttt{"quotedString"} in your code, not "quotedString".',
        test_type=TestType.BOUNDARY,
        expected_matches=[
            ExpectedMatch(
                pattern='"quotedString"',
                fix='"quotedString"',
                after_marker='}',
                count=1
            )
        ],
        expected_no_matches_in=[
            ProtectedRegion(
                start_marker='\\texttt{',
                end_marker='}',
                description='texttt command'
            )
        ]
    ))
    
    # Test 6: Idempotency - already correct quotes
    tests.append(TestCase(
        id="TYPO-001-idempotent-correct",
        description="Already has correct curly quotes",
        input_text='This already has "correct" quotes.',
        test_type=TestType.IDEMPOTENCY,
        expected_output='This already has "correct" quotes.'
    ))
    
    # Test 7: Idempotency - mixed quotes
    tests.append(TestCase(
        id="TYPO-001-idempotent-mixed",
        description="Mix of straight and curly quotes",
        input_text='Mix of "straight" and "curly" quotes.',
        test_type=TestType.IDEMPOTENCY,
        expected_output='Mix of "straight" and "curly" quotes.'
    ))
    
    # Test 8: Edge case - nested quotes
    tests.append(TestCase(
        id="TYPO-001-nested",
        description="Nested quotes with single inside double",
        input_text='She said "he told me \'hello\' yesterday".',
        test_type=TestType.FIX_CORRECTNESS,
        expected_output='She said "he told me 'hello' yesterday".',
        expected_matches=[
            ExpectedMatch(pattern='"he told me \'hello\' yesterday"'),
            ExpectedMatch(pattern="'hello'", fix="'hello'")
        ]
    ))
    
    # Test 9: Edge case - quote at document boundaries
    tests.append(TestCase(
        id="TYPO-001-document-edges",
        description="Quotes at start and end of document",
        input_text='"Start" in middle "End"',
        test_type=TestType.FIX_CORRECTNESS,
        expected_output='"Start" in middle "End"',
        expected_matches=[
            ExpectedMatch(pattern='"Start"'),
            ExpectedMatch(pattern='"End"')
        ]
    ))
    
    # Test 10: Performance test - large document
    large_text = '\n'.join([f'Line {i} has "quote {i}" here.' for i in range(1000)])
    tests.append(TestCase(
        id="TYPO-001-performance",
        description="Performance on 1000-line document",
        input_text=large_text,
        test_type=TestType.PERFORMANCE,
        timeout_ms=100  # Should process in under 100ms
    ))
    
    return tests


def demonstrate_debugging():
    """Show how debugging works with the new system."""
    
    # Create a test that will fail to demonstrate debugging
    failing_test = TestCase(
        id="DEMO-FAIL",
        description="Intentional failure to show debugging",
        input_text='Input "text" here.',
        test_type=TestType.FIX_CORRECTNESS,
        expected_output='Input "text" here.',  # Wrong expected output
        expected_matches=[
            ExpectedMatch(pattern='"text"', fix='"text"')
        ]
    )
    
    # Mock rule that produces different output
    def mock_rule(text, config):
        from latex_perfectionist.core.types import Issue, Fix, RuleResult
        
        # Find quotes and create fixes
        fixes = []
        import re
        for match in re.finditer(r'"([^"]+)"', text):
            fixes.append(Fix(
                start=match.start(),
                end=match.end(),
                replacement=f'"{match.group(1)}"'  # Using different quote style
            ))
        
        return RuleResult(issues=[], fixes=fixes)
    
    # Run validation
    validator = FooledValidator(Path('rules'))
    result = validator._run_test(failing_test, mock_rule)
    
    if not result.passed:
        print("=" * 60)
        print("DEBUGGING EXAMPLE - Test Failed (as expected)")
        print("=" * 60)
        print(result.get_failure_report())
        print("\n" + "=" * 60)


def demonstrate_test_specification():
    """Show the new declarative test format."""
    
    test_spec = '''
# TYPO-001 Test Specification

## Detection Tests

test: Quote in normal text
input: This is a "test" case.
expect:
  match: "test" -> "test"

test: Quote before verbatim
input: Say "hello" then \\begin{verbatim}"code"\\end{verbatim}
expect:
  match: "hello" -> "hello"
  no_match_in: verbatim

## Boundary Tests  

test: Quote touching texttt boundary
input: Before\\texttt{"inside"}after "outside" text.
expect:
  match: "outside" -> "outside"
  no_match_in: \\texttt{...}

test: Quote spanning contexts (should not match)
input: Start "quote \\texttt{code} continue" here.
expect:
  # Complex case - quote starts outside but contains protected region
  # This tests that the rule correctly handles partial matches
  behavior: no_match_or_partial_fix

## Idempotency Tests

test: Mixed quote styles
input: First "straight" then "curly" quotes.
expect:
  after_one_pass: First "straight" then "curly" quotes.
  idempotent: true

## Edge Cases

test: Empty quotes
input: This has "" empty quotes.
expect:
  match: "" -> ""

test: Unicode in quotes  
input: Unicode "café" and "π" work.
expect:
  match: "café" -> "café"
  match: "π" -> "π"
'''
    
    print("\nNEW DECLARATIVE TEST FORMAT")
    print("=" * 60)
    print(test_spec)
    print("=" * 60)


def main():
    """Run example validation."""
    
    print("FOOLPROOF VALIDATOR DEMONSTRATION")
    print("=" * 60)
    
    # 1. Show test creation
    print("\n1. Creating comprehensive test suite for TYPO-001...")
    tests = create_typo_001_tests()
    print(f"   Created {len(tests)} test cases covering:")
    for test in tests:
        print(f"   - {test.description} [{test.test_type.value}]")
    
    # 2. Show debugging capabilities
    print("\n2. Debugging capabilities...")
    demonstrate_debugging()
    
    # 3. Show new test format
    print("\n3. New declarative test format...")
    demonstrate_test_specification()
    
    # 4. Summary of improvements
    print("\n4. KEY IMPROVEMENTS")
    print("=" * 60)
    improvements = [
        "Position-independent validation using markers",
        "Actual fix output validation with diffs",
        "Automatic idempotency testing",
        "Systematic boundary testing with protected regions",
        "Performance benchmarking built-in",
        "Property-based test generation",
        "Character-level debugging for subtle issues",
        "Declarative test format that's easy to write"
    ]
    for i, improvement in enumerate(improvements, 1):
        print(f"{i}. {improvement}")
    
    print("\n" + "=" * 60)
    print("The new validator is foolproof because it:")
    print("- Tests what actually matters (output, not positions)")
    print("- Makes debugging trivial with detailed diffs")
    print("- Scales automatically with property-based testing")
    print("- Guarantees correctness through idempotency")
    print("- Catches boundary issues systematically")


if __name__ == "__main__":
    main()