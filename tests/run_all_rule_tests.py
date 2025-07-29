#!/usr/bin/env python3
"""
Comprehensive test runner for all LaTeX Perfectionist rules.
This script provides an easy way to run tests for all rules with various options.
"""

import sys
import subprocess
import argparse
from pathlib import Path
from typing import List, Dict, Tuple
import time
from datetime import datetime

# Define all rules and their corresponding test files
RULE_TEST_MAPPING = {
    # Rules with existing tests
    "dash_ranges": ["test_dash_ranges.py", "test_dash_ranges_property.py"],
    "double_periods": ["test_double_periods.py"],
    "expect_prob_brackets": ["test_expect_prob.py", "test_expect_prob_property.py"],
    "math_env_normaliser": ["test_mathenv_deterministic.py"],
    "nested_scripts": ["test_nested_scripts.py", "test_nested_scripts_property.py"],
    "tie_words": ["test_ties.py"],
    "math_canonical": ["test_math_canonical_hardcore.py"],
    "math_semantic_ast": ["test_math_semantic_ast_hardcore.py"],
    "math_operator_declaration": ["test_math_operator_declaration_hardcore.py"],
    "math_spacing_advanced": ["test_math_spacing_advanced_hardcore.py"],
    "microtype_validation": ["test_microtype_validation_hardcore.py"],
    "inclusive_language": ["test_inclusive_language_hardcore.py"],
    "typography_advanced": ["test_typography_advanced_hardcore.py"],
    "security": ["test_security_hardcore.py"],
    "multilingual": ["test_multilingual_hardcore.py"],
    
    # Rules with newly created tests
    "bibliography_validator": ["test_bibliography_validator.py", "test_bibliography_validator_hardcore.py"],
    "bibliography_services": ["test_bibliography_services_hardcore.py"],
    "config_schema": ["test_config_schema_hardcore.py"],
    "document_structure": ["test_document_structure.py"],
    "enhanced_math_normalizer": ["enhanced_math_tests.py"],  # May exist
    "float_validation": ["test_float_validation.py"],
    "graphics_accessibility": ["test_graphics_accessibility_hardcore.py"],
    "orthography_grammar": ["test_orthography_grammar_hardcore.py"],
    "preamble_analyzer": ["test_preamble_analyzer_hardcore.py"],
    "robust_rules": ["test_robust_rules_hardcore.py"],
}

# Test categories
TEST_CATEGORIES = {
    "unit": ["test_*.py"],
    "property": ["*_property.py", "property_*.py"],
    "hardcore": ["hardcore_*.py", "*_hardcore*.py", "*hardcore_*.py"],
    "integration": ["test_engine_integration.py", "test_orchestrator.py"],
    "all": ["test_*.py", "*_test*.py", "hardcore_*.py", "*hardcore*.py", "*property*.py"]
}


class TestRunner:
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.results: Dict[str, Dict] = {}
        self.start_time = None
        
    def run_tests_for_rule(self, rule_name: str, test_files: List[str]) -> Tuple[bool, str]:
        """Run tests for a specific rule."""
        if not test_files:
            return False, "No tests found"
        
        test_paths = []
        for test_file in test_files:
            test_path = Path("tests") / test_file
            if test_path.exists():
                test_paths.append(str(test_path))
        
        if not test_paths:
            return False, f"Test files not found: {test_files}"
        
        cmd = ["poetry", "run", "pytest", "-v"] + test_paths
        if self.verbose:
            cmd.append("-s")
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True)
            success = result.returncode == 0
            output = result.stdout if success else result.stderr
            return success, output
        except Exception as e:
            return False, str(e)
    
    def run_category_tests(self, category: str) -> Tuple[bool, str]:
        """Run tests by category."""
        if category not in TEST_CATEGORIES:
            return False, f"Unknown category: {category}"
        
        patterns = TEST_CATEGORIES[category]
        cmd = ["poetry", "run", "pytest", "-v", "tests/"]
        
        # Add patterns
        for pattern in patterns:
            cmd.extend(["-k", pattern.replace("*", "")])
        
        if self.verbose:
            cmd.append("-s")
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True)
            success = result.returncode == 0
            output = result.stdout if success else result.stderr
            return success, output
        except Exception as e:
            return False, str(e)
    
    def run_all_tests(self) -> None:
        """Run all tests and generate report."""
        self.start_time = time.time()
        print("🧪 LaTeX Perfectionist Test Runner")
        print("=" * 60)
        print(f"Started at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("=" * 60)
        
        # Test each rule
        total_rules = len(RULE_TEST_MAPPING)
        rules_with_tests = sum(1 for tests in RULE_TEST_MAPPING.values() if tests)
        rules_without_tests = total_rules - rules_with_tests
        
        print(f"\n📊 Test Coverage Summary:")
        print(f"  Total rules: {total_rules}")
        print(f"  Rules with tests: {rules_with_tests}")
        print(f"  Rules without tests: {rules_without_tests}")
        print()
        
        passed = 0
        failed = 0
        skipped = 0
        
        for rule_name, test_files in RULE_TEST_MAPPING.items():
            print(f"\n🔍 Testing rule: {rule_name}")
            print("-" * 40)
            
            if not test_files:
                print("  ⚠️  No tests found - SKIPPED")
                self.results[rule_name] = {"status": "skipped", "message": "No tests"}
                skipped += 1
                continue
            
            success, output = self.run_tests_for_rule(rule_name, test_files)
            
            if success:
                print("  ✅ PASSED")
                self.results[rule_name] = {"status": "passed", "output": output}
                passed += 1
            else:
                print("  ❌ FAILED")
                self.results[rule_name] = {"status": "failed", "output": output}
                failed += 1
                if self.verbose:
                    print(f"  Error output:\n{output}")
        
        self._print_summary(passed, failed, skipped)
    
    def run_specific_rules(self, rules: List[str]) -> None:
        """Run tests for specific rules."""
        self.start_time = time.time()
        print(f"🧪 Testing specific rules: {', '.join(rules)}")
        print("=" * 60)
        
        for rule in rules:
            if rule not in RULE_TEST_MAPPING:
                print(f"\n❌ Unknown rule: {rule}")
                continue
            
            print(f"\n🔍 Testing rule: {rule}")
            test_files = RULE_TEST_MAPPING[rule]
            
            if not test_files:
                print("  ⚠️  No tests found")
                continue
            
            success, output = self.run_tests_for_rule(rule, test_files)
            
            if success:
                print("  ✅ PASSED")
            else:
                print("  ❌ FAILED")
                if self.verbose:
                    print(f"  Error output:\n{output}")
    
    def _print_summary(self, passed: int, failed: int, skipped: int) -> None:
        """Print test summary."""
        elapsed = time.time() - self.start_time
        total = passed + failed + skipped
        
        print("\n" + "=" * 60)
        print("📈 FINAL SUMMARY")
        print("=" * 60)
        print(f"Total rules tested: {total}")
        print(f"  ✅ Passed: {passed}")
        print(f"  ❌ Failed: {failed}")
        print(f"  ⚠️  Skipped: {skipped}")
        print(f"\nTest coverage: {(passed / total * 100):.1f}%")
        print(f"Time elapsed: {elapsed:.2f}s")
        
        if failed > 0:
            print("\n⚠️  Failed rules:")
            for rule, result in self.results.items():
                if result["status"] == "failed":
                    print(f"  - {rule}")
        
        if skipped > 0:
            print("\n📝 Rules without tests:")
            for rule, result in self.results.items():
                if result["status"] == "skipped":
                    print(f"  - {rule}")


def main():
    parser = argparse.ArgumentParser(
        description="Run tests for LaTeX Perfectionist rules",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Run all tests
  python run_all_rule_tests.py
  
  # Run tests for specific rules
  python run_all_rule_tests.py --rules dash_ranges tie_words
  
  # Run tests by category
  python run_all_rule_tests.py --category property
  
  # Run with verbose output
  python run_all_rule_tests.py -v
  
  # Generate coverage report
  python run_all_rule_tests.py --coverage
"""
    )
    
    parser.add_argument(
        "--rules", 
        nargs="+", 
        help="Specific rules to test"
    )
    parser.add_argument(
        "--category",
        choices=list(TEST_CATEGORIES.keys()),
        help="Test category to run"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Verbose output"
    )
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="Generate coverage report"
    )
    parser.add_argument(
        "--list-rules",
        action="store_true",
        help="List all available rules"
    )
    
    args = parser.parse_args()
    
    if args.list_rules:
        print("Available rules:")
        for rule in sorted(RULE_TEST_MAPPING.keys()):
            tests = RULE_TEST_MAPPING[rule]
            status = "✅" if tests else "❌"
            print(f"  {status} {rule}")
        return
    
    runner = TestRunner(verbose=args.verbose)
    
    if args.coverage:
        # Run with coverage
        cmd = ["poetry", "run", "pytest", "--cov=latex_perfectionist", "--cov-report=html", "--cov-report=term", "tests/"]
        subprocess.run(cmd)
    elif args.category:
        success, output = runner.run_category_tests(args.category)
        if not success and args.verbose:
            print(output)
    elif args.rules:
        runner.run_specific_rules(args.rules)
    else:
        runner.run_all_tests()


if __name__ == "__main__":
    main()