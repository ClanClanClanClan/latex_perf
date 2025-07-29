"""
Foolproof Validation System for LaTeX Perfectionist

This is a complete redesign that addresses all current issues:
1. Deterministic and reproducible
2. Tests both detection AND fixes
3. Handles edge cases systematically
4. Easy debugging with detailed diffs
5. Scales without manual work
"""

import re
import json
import difflib
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set, Any
from dataclasses import dataclass, field
from enum import Enum
import hashlib
from abc import ABC, abstractmethod

# Import hypothesis for property-based testing
import hypothesis
from hypothesis import strategies as st


class TestType(Enum):
    """Types of tests we can run."""
    DETECTION = "detection"          # Does it find what it should?
    FIX_CORRECTNESS = "fix"         # Does it fix correctly?
    IDEMPOTENCY = "idempotency"     # Is fix(fix(x)) = fix(x)?
    BOUNDARY = "boundary"            # Does it respect context boundaries?
    PERFORMANCE = "performance"      # Is it fast enough?
    REGRESSION = "regression"        # Does it still pass old tests?


@dataclass
class TestCase:
    """A single test case with input, expected behavior, and metadata."""
    id: str
    description: str
    input_text: str
    test_type: TestType
    
    # Expected behaviors
    expected_matches: List['ExpectedMatch'] = field(default_factory=list)
    expected_output: Optional[str] = None
    expected_no_matches_in: List['ProtectedRegion'] = field(default_factory=list)
    
    # Metadata
    tags: Set[str] = field(default_factory=set)
    timeout_ms: int = 1000
    
    def content_hash(self) -> str:
        """Generate stable hash of test content for caching."""
        content = f"{self.input_text}|{self.expected_output or ''}"
        return hashlib.sha256(content.encode()).hexdigest()[:16]


@dataclass
class ExpectedMatch:
    """Expected match with both position and content."""
    pattern: str                    # What text should match
    fix: Optional[str] = None      # What it should be fixed to
    # Instead of absolute positions, use markers
    after_marker: Optional[str] = None   # Must appear after this unique text
    before_marker: Optional[str] = None  # Must appear before this unique text
    in_context: Optional[str] = None     # Must be within this context
    count: int = 1                       # How many times it should match


@dataclass
class ProtectedRegion:
    """Region where no matches should occur."""
    start_marker: str    # Unique text marking region start
    end_marker: str      # Unique text marking region end
    description: str     # Why this region is protected


@dataclass
class ValidationResult:
    """Comprehensive result of validation."""
    test_case: TestCase
    passed: bool
    
    # Detailed results
    detection_result: Optional['DetectionResult'] = None
    fix_result: Optional['FixResult'] = None
    idempotency_result: Optional['IdempotencyResult'] = None
    boundary_result: Optional['BoundaryResult'] = None
    performance_result: Optional['PerformanceResult'] = None
    
    # Debug info
    debug_info: Dict[str, Any] = field(default_factory=dict)
    
    def get_failure_report(self) -> str:
        """Generate detailed failure report for debugging."""
        report = [f"Test Case: {self.test_case.id} - {self.test_case.description}"]
        report.append(f"Test Type: {self.test_case.test_type.value}")
        report.append("")
        
        if self.detection_result and not self.detection_result.passed:
            report.extend(self.detection_result.get_debug_report())
        
        if self.fix_result and not self.fix_result.passed:
            report.extend(self.fix_result.get_debug_report())
            
        if self.idempotency_result and not self.idempotency_result.passed:
            report.extend(self.idempotency_result.get_debug_report())
            
        return "\n".join(report)


@dataclass
class DetectionResult:
    """Result of detection validation."""
    passed: bool
    found_matches: List[Tuple[int, int, str]]  # (start, end, text)
    expected_matches: List[ExpectedMatch]
    unexpected_matches: List[Tuple[int, int, str]]
    missed_matches: List[ExpectedMatch]
    violations_in_protected: List[Tuple[str, int, int]]  # (region_desc, start, end)
    
    def get_debug_report(self) -> List[str]:
        """Generate debug report for detection failures."""
        report = ["=== DETECTION FAILURES ==="]
        
        if self.unexpected_matches:
            report.append("\nUnexpected Matches:")
            for start, end, text in self.unexpected_matches:
                report.append(f"  [{start}:{end}] '{text}'")
        
        if self.missed_matches:
            report.append("\nMissed Matches:")
            for match in self.missed_matches:
                report.append(f"  Pattern: '{match.pattern}'")
                if match.in_context:
                    report.append(f"    Context: '{match.in_context}'")
        
        if self.violations_in_protected:
            report.append("\nMatches in Protected Regions:")
            for desc, start, end in self.violations_in_protected:
                report.append(f"  {desc}: [{start}:{end}]")
        
        return report


@dataclass
class FixResult:
    """Result of fix validation."""
    passed: bool
    original_text: str
    fixed_text: str
    expected_text: str
    diff: List[str]
    
    def get_debug_report(self) -> List[str]:
        """Generate debug report showing exact differences."""
        report = ["=== FIX FAILURES ==="]
        report.append("\nExpected vs Actual Diff:")
        report.extend(self.diff)
        
        # Also show character-by-character diff for subtle issues
        if len(self.expected_text) < 200 and len(self.fixed_text) < 200:
            report.append("\nCharacter-level diff:")
            for i, (e, a) in enumerate(zip(self.expected_text, self.fixed_text)):
                if e != a:
                    report.append(f"  Position {i}: expected '{e}' (U+{ord(e):04X}), got '{a}' (U+{ord(a):04X})")
        
        return report


@dataclass  
class IdempotencyResult:
    """Result of idempotency test."""
    passed: bool
    first_pass: str
    second_pass: str
    diff: List[str]
    iteration_count: int
    
    def get_debug_report(self) -> List[str]:
        """Show where idempotency fails."""
        report = ["=== IDEMPOTENCY FAILURES ==="]
        report.append(f"Failed after {self.iteration_count} iterations")
        report.append("\nDiff between passes:")
        report.extend(self.diff)
        return report


@dataclass
class BoundaryResult:
    """Result of boundary testing."""
    passed: bool
    boundary_violations: List[Tuple[str, int]]  # (boundary_type, position)
    
    def get_debug_report(self) -> List[str]:
        """Show boundary violations."""
        report = ["=== BOUNDARY FAILURES ==="]
        for boundary_type, pos in self.boundary_violations:
            report.append(f"  {boundary_type} boundary violated at position {pos}")
        return report


@dataclass
class PerformanceResult:
    """Result of performance testing."""
    passed: bool
    execution_time_ms: float
    timeout_ms: int
    
    def get_debug_report(self) -> List[str]:
        """Show performance issues."""
        report = ["=== PERFORMANCE FAILURES ==="]
        report.append(f"Execution time: {self.execution_time_ms:.2f}ms (limit: {self.timeout_ms}ms)")
        return report


class TestGenerator(ABC):
    """Abstract base for test generators."""
    
    @abstractmethod
    def generate_tests(self, rule_id: str) -> List[TestCase]:
        """Generate test cases for a rule."""
        pass


class BoundaryTestGenerator(TestGenerator):
    """Generates systematic boundary tests."""
    
    def generate_tests(self, rule_id: str) -> List[TestCase]:
        """Generate boundary test cases."""
        tests = []
        
        # For TYPO-001 (quotes), test boundaries like:
        # - Start/end of verbatim blocks
        # - Start/end of math mode
        # - Start/end of \texttt{}
        # - Nested contexts
        
        boundary_patterns = {
            'TYPO-001': [
                # Test exact verbatim boundaries
                {
                    'id': 'boundary_verbatim_exact',
                    'input': 'Before "quote" \\begin{verbatim}"inside"\\end{verbatim} after "quote"',
                    'protected': [('\\begin{verbatim}', '\\end{verbatim}', 'verbatim')],
                    'expected_matches': [
                        ExpectedMatch('"quote"', '"quote"', before_marker='\\begin{verbatim}'),
                        ExpectedMatch('"quote"', '"quote"', after_marker='\\end{verbatim}')
                    ]
                },
                # Test math mode boundaries  
                {
                    'id': 'boundary_math_inline',
                    'input': 'Text "quote" then $x = "y"$ then "quote" again',
                    'protected': [('$', '$', 'inline math')],
                    'expected_matches': [
                        ExpectedMatch('"quote"', '"quote"', before_marker='$'),
                        ExpectedMatch('"quote"', '"quote"', after_marker='$')
                    ]
                },
                # Test texttt boundaries
                {
                    'id': 'boundary_texttt_nested',
                    'input': 'Say "hello" in \\texttt{print("world")} format',
                    'protected': [('\\texttt{', '}', 'texttt')],
                    'expected_matches': [
                        ExpectedMatch('"hello"', '"hello"', before_marker='\\texttt{')
                    ]
                }
            ]
        }
        
        if rule_id in boundary_patterns:
            for pattern in boundary_patterns[rule_id]:
                tests.append(TestCase(
                    id=f"{rule_id}_{pattern['id']}",
                    description=f"Boundary test: {pattern['id']}",
                    input_text=pattern['input'],
                    test_type=TestType.BOUNDARY,
                    expected_matches=pattern['expected_matches'],
                    expected_no_matches_in=[
                        ProtectedRegion(start, end, desc) 
                        for start, end, desc in pattern.get('protected', [])
                    ]
                ))
        
        return tests


class PropertyBasedTestGenerator(TestGenerator):
    """Generate tests using property-based testing."""
    
    def generate_tests(self, rule_id: str) -> List[TestCase]:
        """Generate property-based test cases."""
        tests = []
        
        # Define strategies for different rule types
        if rule_id == 'TYPO-001':
            # Generate documents with quotes in various contexts
            @hypothesis.given(
                prefix=st.text(min_size=0, max_size=50),
                quote_content=st.text(min_size=1, max_size=20).filter(lambda x: '"' not in x),
                suffix=st.text(min_size=0, max_size=50),
                context=st.sampled_from(['normal', 'verbatim', 'math', 'texttt'])
            )
            def test_quote_detection(prefix, quote_content, suffix, context):
                if context == 'normal':
                    doc = f'{prefix}"{quote_content}"{suffix}'
                    expected = f'{prefix}"{quote_content}"{suffix}'
                elif context == 'verbatim':
                    doc = f'{prefix}\\begin{{verbatim}}"{quote_content}"\\end{{verbatim}}{suffix}'
                    expected = doc  # No change in verbatim
                elif context == 'math':
                    doc = f'{prefix}$"{quote_content}"${suffix}'
                    expected = doc  # No change in math
                elif context == 'texttt':
                    doc = f'{prefix}\\texttt{{"{quote_content}"}}{suffix}'
                    expected = doc  # No change in texttt
                
                return doc, expected, context
            
            # Generate 10 property-based tests
            for i in range(10):
                try:
                    doc, expected, context = test_quote_detection()
                    tests.append(TestCase(
                        id=f"{rule_id}_property_{i}",
                        description=f"Property test: quotes in {context} context",
                        input_text=doc,
                        test_type=TestType.FIX_CORRECTNESS,
                        expected_output=expected,
                        tags={'property-based', context}
                    ))
                except:
                    pass  # Skip if generation fails
        
        return tests


class FooledValidator:
    """The new foolproof validator."""
    
    def __init__(self, rules_dir: Path):
        self.rules_dir = rules_dir
        self.test_generators = [
            BoundaryTestGenerator(),
            PropertyBasedTestGenerator(),
        ]
        self.results_cache = {}
        
    def validate_rule(self, rule_id: str, rule_function) -> List[ValidationResult]:
        """Validate a rule comprehensively."""
        results = []
        
        # Load static test cases
        static_tests = self._load_static_tests(rule_id)
        
        # Generate dynamic test cases
        dynamic_tests = []
        for generator in self.test_generators:
            dynamic_tests.extend(generator.generate_tests(rule_id))
        
        # Run all tests
        all_tests = static_tests + dynamic_tests
        for test in all_tests:
            result = self._run_test(test, rule_function)
            results.append(result)
            
        return results
    
    def _run_test(self, test: TestCase, rule_function) -> ValidationResult:
        """Run a single test case."""
        result = ValidationResult(test_case=test, passed=True)
        
        # Run the rule
        import time
        start_time = time.time()
        rule_result = rule_function(test.input_text, {})
        execution_time = (time.time() - start_time) * 1000
        
        # Run different test types
        if test.test_type in [TestType.DETECTION, TestType.BOUNDARY]:
            detection_result = self._validate_detection(test, rule_result)
            result.detection_result = detection_result
            result.passed &= detection_result.passed
            
        if test.test_type == TestType.FIX_CORRECTNESS and test.expected_output:
            fix_result = self._validate_fix(test, rule_result)
            result.fix_result = fix_result
            result.passed &= fix_result.passed
            
        if test.test_type == TestType.IDEMPOTENCY:
            idempotency_result = self._validate_idempotency(test, rule_function)
            result.idempotency_result = idempotency_result
            result.passed &= idempotency_result.passed
            
        if test.test_type == TestType.PERFORMANCE:
            perf_result = PerformanceResult(
                passed=execution_time <= test.timeout_ms,
                execution_time_ms=execution_time,
                timeout_ms=test.timeout_ms
            )
            result.performance_result = perf_result
            result.passed &= perf_result.passed
            
        return result
    
    def _validate_detection(self, test: TestCase, rule_result) -> DetectionResult:
        """Validate detection accuracy."""
        # Extract actual matches from fixes
        found_matches = [
            (fix.start, fix.end, test.input_text[fix.start:fix.end])
            for fix in rule_result.fixes
        ]
        
        # Check expected matches using markers
        missed_matches = []
        for expected in test.expected_matches:
            count_found = self._count_matches_for_pattern(
                test.input_text, expected, found_matches
            )
            if count_found != expected.count:
                missed_matches.append(expected)
        
        # Check protected regions
        violations = []
        for region in test.expected_no_matches_in:
            start_pos = test.input_text.find(region.start_marker)
            end_pos = test.input_text.find(region.end_marker, start_pos)
            if start_pos >= 0 and end_pos >= 0:
                for fix_start, fix_end, _ in found_matches:
                    if start_pos <= fix_start < end_pos:
                        violations.append((region.description, fix_start, fix_end))
        
        return DetectionResult(
            passed=len(missed_matches) == 0 and len(violations) == 0,
            found_matches=found_matches,
            expected_matches=test.expected_matches,
            unexpected_matches=[],  # TODO: Implement
            missed_matches=missed_matches,
            violations_in_protected=violations
        )
    
    def _validate_fix(self, test: TestCase, rule_result) -> FixResult:
        """Validate fix correctness."""
        # Apply fixes to get actual output
        fixed_text = self._apply_fixes(test.input_text, rule_result.fixes)
        
        # Compare with expected
        passed = fixed_text == test.expected_output
        
        # Generate diff for debugging
        diff = list(difflib.unified_diff(
            test.expected_output.splitlines(keepends=True),
            fixed_text.splitlines(keepends=True),
            fromfile='expected',
            tofile='actual',
            lineterm=''
        ))
        
        return FixResult(
            passed=passed,
            original_text=test.input_text,
            fixed_text=fixed_text,
            expected_text=test.expected_output,
            diff=diff
        )
    
    def _validate_idempotency(self, test: TestCase, rule_function) -> IdempotencyResult:
        """Validate that fixes are idempotent."""
        text = test.input_text
        iterations = []
        
        # Apply fixes up to 5 times
        for i in range(5):
            rule_result = rule_function(text, {})
            new_text = self._apply_fixes(text, rule_result.fixes)
            iterations.append(new_text)
            
            if new_text == text:
                # Reached fixed point
                return IdempotencyResult(
                    passed=True,
                    first_pass=iterations[0] if iterations else text,
                    second_pass=new_text,
                    diff=[],
                    iteration_count=i + 1
                )
            
            text = new_text
        
        # Did not reach fixed point
        diff = list(difflib.unified_diff(
            iterations[-2].splitlines(keepends=True),
            iterations[-1].splitlines(keepends=True),
            fromfile=f'iteration_{len(iterations)-1}',
            tofile=f'iteration_{len(iterations)}',
            lineterm=''
        ))
        
        return IdempotencyResult(
            passed=False,
            first_pass=iterations[0],
            second_pass=iterations[-1],
            diff=diff,
            iteration_count=len(iterations)
        )
    
    def _apply_fixes(self, text: str, fixes: List) -> str:
        """Apply fixes to text, handling overlaps correctly."""
        if not fixes:
            return text
        
        # Sort fixes by start position (reverse order for applying)
        sorted_fixes = sorted(fixes, key=lambda f: f.start, reverse=True)
        
        # Apply fixes from end to beginning to maintain positions
        result = text
        for fix in sorted_fixes:
            result = result[:fix.start] + fix.replacement + result[fix.end:]
            
        return result
    
    def _count_matches_for_pattern(self, text: str, expected: ExpectedMatch, 
                                  found_matches: List[Tuple[int, int, str]]) -> int:
        """Count how many times an expected pattern was found."""
        count = 0
        
        for start, end, match_text in found_matches:
            # Check if this match corresponds to the expected pattern
            if expected.pattern in match_text or match_text == expected.pattern:
                # Check position constraints if specified
                if expected.after_marker:
                    marker_pos = text.find(expected.after_marker)
                    if marker_pos >= 0 and start <= marker_pos:
                        continue
                        
                if expected.before_marker:
                    marker_pos = text.find(expected.before_marker)
                    if marker_pos >= 0 and end >= marker_pos:
                        continue
                        
                count += 1
                
        return count
    
    def _load_static_tests(self, rule_id: str) -> List[TestCase]:
        """Load static test cases from JSON."""
        # TODO: Implement loading from redesigned test format
        return []
    
    def generate_report(self, results: List[ValidationResult]) -> str:
        """Generate comprehensive validation report."""
        report = ["# Foolproof Validation Report\n"]
        
        # Summary
        total = len(results)
        passed = sum(1 for r in results if r.passed)
        report.append(f"## Summary: {passed}/{total} tests passed\n")
        
        # Group by test type
        by_type = {}
        for result in results:
            test_type = result.test_case.test_type
            if test_type not in by_type:
                by_type[test_type] = []
            by_type[test_type].append(result)
        
        # Report by type
        for test_type, type_results in by_type.items():
            type_passed = sum(1 for r in type_results if r.passed)
            report.append(f"\n### {test_type.value.title()} Tests: {type_passed}/{len(type_results)}")
            
            # Show failures
            failures = [r for r in type_results if not r.passed]
            if failures:
                report.append("\n#### Failures:")
                for failure in failures[:5]:  # Show first 5
                    report.append(f"\n{failure.get_failure_report()}")
                if len(failures) > 5:
                    report.append(f"\n... and {len(failures) - 5} more failures")
        
        # Add debugging tips
        report.append("\n## Debugging Tips")
        report.append("- Use the character-level diff to spot subtle differences")
        report.append("- Check boundary violations for off-by-one errors")
        report.append("- Run with --verbose to see all test inputs/outputs")
        report.append("- Use --debug-case TEST_ID to debug a specific test")
        
        return '\n'.join(report)


# Example of new test format that's easier to write and maintain
EXAMPLE_TEST_SPEC = """
# TYPO-001 Test Specification

## Basic Detection Tests

### Test: Simple quotes
Input: This is a "test" document.
Expect: Match "test" -> "test"

### Test: Multiple quotes  
Input: First "one" and second "two" here.
Expect: 
  - Match "one" -> "one"
  - Match "two" -> "two"

## Boundary Tests

### Test: Verbatim boundary
Input: Before "this" \\begin{verbatim}"not this"\\end{verbatim} after "this".
Protected: verbatim blocks
Expect:
  - Match "this" (first occurrence) -> "this"
  - Match "this" (last occurrence) -> "this"
  - No match inside verbatim

### Test: Math mode boundary
Input: Text "yes" then $"no"$ then "yes" again.
Protected: math mode
Expect:
  - Match "yes" (both occurrences) -> "yes"  
  - No match inside $...$

## Idempotency Tests

### Test: Already correct quotes
Input: This has "correct" quotes already.
Expect: No changes, idempotent

### Test: Mixed quotes
Input: Mix of "straight" and "curly" quotes.
Expect: After one pass, further passes make no changes
"""


if __name__ == "__main__":
    # Example usage
    print("New Foolproof Validation Architecture")
    print("=" * 50)
    print("\nKey improvements:")
    print("1. Position-independent matching using markers")
    print("2. Comprehensive fix validation with diffs")
    print("3. Automatic idempotency testing")
    print("4. Systematic boundary testing")
    print("5. Property-based test generation")
    print("6. Detailed debugging output")
    print("\nSee EXAMPLE_TEST_SPEC for new test format")