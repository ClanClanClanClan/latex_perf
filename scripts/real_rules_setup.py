#!/usr/bin/env python3
"""
SETUP FOR REAL LATEX PERFECTIONIST RULES
=========================================

This sets up the test orchestrator to work with your actual rules
from latex_perfectionist/rules/ directory.

Your available rules:
- bibliography_validator
- dash_ranges 
- document_structure
- double_periods
- enhanced_math_normalizer
- expect_prob_brackets
- float_validation
- graphics_accessibility
- math_env_normaliser
- nested_scripts
- orthography_grammar
- preamble_analyzer (no audit function)
- robust_rules
- tie_words
"""

import sys
from pathlib import Path

def create_real_rules_orchestrator():
    """Create test orchestrator that works with real rules."""
    
    orchestrator_content = '''#!/usr/bin/env python3
"""
HARDCORE TEST ORCHESTRATOR - FOR REAL LATEX PERFECTIONIST RULES
===============================================================

This orchestrator works with your actual LaTeX Perfectionist rules
from the latex_perfectionist/rules/ directory.
"""

import sys
import os
import time
import threading
import traceback
import json
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, field
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse

# Add parent directory to path to find latex_perfectionist
current_dir = Path(__file__).parent
parent_dir = current_dir.parent
sys.path.insert(0, str(parent_dir))
sys.path.insert(0, str(current_dir))

@dataclass
class TestSuiteConfig:
    """Configuration for a test suite."""
    name: str
    module_name: str
    function_name: str
    enabled: bool = True
    parallel: bool = False
    timeout: int = 300

@dataclass
class TestSuiteResult:
    """Result from running a test suite."""
    suite_name: str
    success: bool
    duration: float
    tests_run: int = 0
    tests_passed: int = 0
    errors: List[str] = field(default_factory=list)
    details: Optional[Dict[str, Any]] = None

class HardcoreTestOrchestrator:
    """Main orchestrator for all hardcore test suites."""
    
    def __init__(self, verbose: bool = False, quick_mode: bool = False):
        self.verbose = verbose
        self.quick_mode = quick_mode
        self.results: List[TestSuiteResult] = []
        
        # Configuration for your actual rules
        self.cfg = {
            "orthography": {
                "en_dash_ranges": True,
                "smart_quotes": True,
            },
            "punctuation": {
                "abbreviations": [
                    "a.s.", "w.l.o.g.", "i.i.d.", "w.r.t.", "cf.", "e.g.", "i.e.", 
                    "etc.", "vs.", "resp.", "et al.", "viz.", "ibid.", "op. cit."
                ],
                "tie_words": [
                    "Figure", "Table", "Theorem", "Lemma", "Corollary", "Proposition",
                    "Definition", "Example", "Section", "Chapter", "Appendix",
                    "cf.", "Eq.", "eq.", "pp.", "p.", "Ch.", "Sec.", "Fig.", "Tab."
                ]
            },
            "math": {
                "expect_brackets": True,
                "prob_brackets": True,
                "raisebox_ex": "0.2ex",
                "normalize_environments": True,
            },
            "typography": {
                "nested_scripts": True,
                "script_threshold": 2,
            },
            "validation": {
                "float_validation": True,
                "bibliography_validation": True,
                "graphics_accessibility": True,
            },
            "structure": {
                "document_structure": True,
                "robust_rules": True,
            }
        }
        
        # Your actual available rules
        self.available_rules = [
            "bibliography_validator",
            "dash_ranges", 
            "document_structure",
            "double_periods",
            "enhanced_math_normalizer",
            "expect_prob_brackets",
            "float_validation",
            "graphics_accessibility",
            "math_env_normaliser",
            "nested_scripts",
            "orthography_grammar",
            "robust_rules",
            "tie_words"
            # Note: preamble_analyzer excluded as it has no audit() function
        ]
        
        # Discover available rules
        self.rules = self._discover_real_rules()
        
        # Configure test suites
        self.config = {
            "universal": TestSuiteConfig(
                name="Universal Rule Tests",
                module_name="ultimate_hardcore_suite", 
                function_name="main",
                enabled=True,
                parallel=False
            ),
            "punctuation": TestSuiteConfig(
                name="Punctuation & Typography",
                module_name="hardcore_punctuation_suite",
                function_name="run_hardcore_punctuation_tests", 
                enabled=True,
                parallel=True
            ),
            "mathematical": TestSuiteConfig(
                name="Mathematical Rules",
                module_name="hardcore_math_suite",
                function_name="run_hardcore_mathematical_tests",
                enabled=True,
                parallel=True
            ),
            "chaos": TestSuiteConfig(
                name="Chaos & Stress Testing",
                module_name="chaos_testing_framework",
                function_name="run_chaos_testing_suite",
                enabled=True,
                parallel=True
            ),
        }
        
        print(f"🎯 HARDCORE TEST ORCHESTRATOR INITIALIZED")
        print(f"📊 Discovered {len(self.rules)} real rules from latex_perfectionist.rules")
        print(f"🧪 Configured {len([c for c in self.config.values() if c.enabled])} test suites")
        if self.verbose:
            print(f"📋 Available rules: {', '.join(self.rules.keys())}")
    
    def _discover_real_rules(self) -> Dict[str, Any]:
        """Discover your actual LaTeX Perfectionist rules."""
        rules = {}
        
        for rule_name in self.available_rules:
            rule = self._load_real_rule(rule_name)
            if rule:
                rules[rule_name] = rule
                if self.verbose:
                    print(f"✅ Loaded real rule: {rule_name}")
            else:
                if self.verbose:
                    print(f"⚠️  Could not load rule: {rule_name}")
        
        return rules
    
    def _load_real_rule(self, rule_name: str) -> Optional[Any]:
        """Load a real rule from latex_perfectionist.rules."""
        try:
            # Try to import from latex_perfectionist.rules
            module = __import__(f"latex_perfectionist.rules.{rule_name}", fromlist=[rule_name])
            
            # Check if it has the audit function
            if hasattr(module, 'audit'):
                return module
            else:
                if self.verbose:
                    print(f"⚠️  Rule {rule_name} has no audit() function")
                return None
                
        except ImportError as e:
            if self.verbose:
                print(f"⚠️  Cannot import {rule_name}: {e}")
            return None
        except Exception as e:
            if self.verbose:
                print(f"❌ Error loading {rule_name}: {e}")
            return None
    
    def run_all_tests(self, selected_suites: Optional[List[str]] = None, 
                     max_workers: int = 4) -> Dict[str, Any]:
        """Run all configured test suites."""
        print("\\n🚀 STARTING HARDCORE TEST EXECUTION")
        print("=" * 60)
        
        start_time = time.time()
        
        # Filter suites if specific ones requested
        suites_to_run = {}
        if selected_suites:
            for suite_name in selected_suites:
                if suite_name in self.config:
                    suites_to_run[suite_name] = self.config[suite_name]
                else:
                    print(f"⚠️  Unknown suite: {suite_name}")
        else:
            suites_to_run = {k: v for k, v in self.config.items() if v.enabled}
        
        print(f"Running {len(suites_to_run)} test suites with {len(self.rules)} real rules...")
        
        if max_workers > 1 and len(suites_to_run) > 1:
            # Run in parallel
            results = self._run_parallel_tests(suites_to_run, max_workers)
        else:
            # Run sequentially
            results = self._run_sequential_tests(suites_to_run)
        
        # Store results
        self.results = results
        
        # Calculate summary
        total_duration = time.time() - start_time
        successful_suites = sum(1 for r in results if r.success)
        total_tests = sum(r.tests_run for r in results)
        total_passed = sum(r.tests_passed for r in results)
        
        # Print summary
        self._print_execution_summary(total_duration, successful_suites, total_tests, total_passed)
        
        return {
            'suites_run': len(results),
            'suites_passed': successful_suites,
            'total_tests': total_tests,
            'total_passed': total_passed,
            'duration': total_duration,
            'results': results
        }
    
    def _run_sequential_tests(self, suites: Dict[str, TestSuiteConfig]) -> List[TestSuiteResult]:
        """Run test suites sequentially."""
        results = []
        
        for suite_name, suite_config in suites.items():
            print(f"\\n🧪 Running {suite_config.name}...")
            result = self._run_single_suite(suite_name, suite_config)
            results.append(result)
            
            # Print immediate result
            status = "✅ PASS" if result.success else "❌ FAIL"
            duration_info = f"{result.duration:.1f}s"
            if result.tests_run > 0:
                duration_info += f" ({result.tests_passed}/{result.tests_run} tests)"
            print(f"   {status} - {duration_info}")
            
            if not result.success and result.errors:
                for error in result.errors[:2]:  # Show first 2 errors
                    print(f"     Error: {error}")
        
        return results
    
    def _run_parallel_tests(self, suites: Dict[str, TestSuiteConfig], 
                           max_workers: int) -> List[TestSuiteResult]:
        """Run test suites in parallel."""
        results = []
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Submit parallel tasks
            future_to_suite = {
                executor.submit(self._run_single_suite, name, config): name
                for name, config in suites.items()
                if config.parallel
            }
            
            # Run non-parallel suites first
            for name, config in suites.items():
                if not config.parallel:
                    print(f"\\n🧪 Running {config.name} (sequential)...")
                    result = self._run_single_suite(name, config)
                    results.append(result)
                    status = "✅ PASS" if result.success else "❌ FAIL"
                    print(f"   {status} - {result.duration:.1f}s")
            
            # Process parallel results as they complete
            for future in as_completed(future_to_suite):
                suite_name = future_to_suite[future]
                try:
                    result = future.result()
                    results.append(result)
                    
                    status = "✅ PASS" if result.success else "❌ FAIL"
                    print(f"🧪 {suites[suite_name].name}: {status} - {result.duration:.1f}s")
                    
                except Exception as e:
                    print(f"❌ {suite_name} failed with exception: {e}")
                    results.append(TestSuiteResult(
                        suite_name=suite_name,
                        success=False,
                        duration=0.0,
                        errors=[str(e)]
                    ))
        
        return results
    
    def _run_single_suite(self, suite_name: str, config: TestSuiteConfig) -> TestSuiteResult:
        """Run a single test suite."""
        start_time = time.time()
        
        try:
            # Import the test module
            module = __import__(config.module_name, fromlist=[config.function_name])
            test_function = getattr(module, config.function_name)
            
            # Prepare arguments based on function signature
            import inspect
            sig = inspect.signature(test_function)
            
            if len(sig.parameters) == 0:
                # Function takes no arguments (like main())
                result = test_function()
            elif len(sig.parameters) == 1:
                # Function takes config only
                result = test_function(self.cfg)
            else:
                # Function takes rules and config
                result = test_function(self.rules, self.cfg)
            
            duration = time.time() - start_time
            
            # Parse result based on what the function returned
            if isinstance(result, dict):
                # Extract test statistics from result
                tests_run = result.get('total_tests', 0)
                tests_passed = result.get('total_passed', 0) 
                success = result.get('success', tests_passed == tests_run if tests_run > 0 else True)
                
                return TestSuiteResult(
                    suite_name=suite_name,
                    success=success,
                    duration=duration,
                    tests_run=tests_run,
                    tests_passed=tests_passed,
                    details=result
                )
            else:
                # Function probably succeeded if no exception
                return TestSuiteResult(
                    suite_name=suite_name,
                    success=True,
                    duration=duration,
                    tests_run=1,
                    tests_passed=1
                )
                
        except Exception as e:
            duration = time.time() - start_time
            error_msg = str(e)
            
            if self.verbose:
                error_msg += f"\\n{traceback.format_exc()}"
            
            return TestSuiteResult(
                suite_name=suite_name,
                success=False,
                duration=duration,
                errors=[error_msg]
            )
    
    def _print_execution_summary(self, total_duration: float, successful_suites: int, 
                               total_tests: int, total_passed: int):
        """Print comprehensive execution summary."""
        print("\\n" + "=" * 80)
        print("🏆 HARDCORE TEST EXECUTION COMPLETE")
        print("=" * 80)
        
        print(f"\\n📊 EXECUTION SUMMARY:")
        print(f"  Total duration: {total_duration:.1f}s")
        print(f"  Test suites: {successful_suites}/{len(self.results)}")
        print(f"  Individual tests: {total_passed}/{total_tests}")
        print(f"  Real rules tested: {len(self.rules)}")
        
        if total_tests > 0:
            success_rate = total_passed / total_tests
            print(f"  Overall success rate: {success_rate:.1%}")
        
        print(f"\\n📋 SUITE BREAKDOWN:")
        for result in self.results:
            status = "✅" if result.success else "❌"
            test_info = ""
            if result.tests_run > 0:
                test_info = f" ({result.tests_passed}/{result.tests_run})"
            print(f"  {status} {result.suite_name:20s}: {result.duration:6.1f}s{test_info}")
            
            if result.errors and self.verbose:
                for error in result.errors[:2]:  # Show first 2 errors
                    print(f"      Error: {error}")
        
        # Overall verdict
        suite_success_rate = successful_suites / len(self.results) if self.results else 0
        
        if suite_success_rate >= 0.9 and (total_tests == 0 or total_passed / total_tests >= 0.9):
            print("\\n🎉 EXCELLENT! Your LaTeX Perfectionist rules are working great! 💪")
        elif suite_success_rate >= 0.7:
            print("\\n👍 GOOD! Most tests are passing, minor issues to address.")
        else:
            print("\\n⚠️  NEEDS ATTENTION! Several test suites need fixing.")
        
        # Save detailed results
        self._save_results()
    
    def _save_results(self):
        """Save detailed results to JSON file."""
        try:
            results_data = {
                'timestamp': time.time(),
                'config': {
                    'verbose': self.verbose,
                    'quick_mode': self.quick_mode,
                    'rules_discovered': len(self.rules),
                    'available_rules': list(self.rules.keys()),
                },
                'suites': []
            }
            
            for result in self.results:
                suite_data = {
                    'name': result.suite_name,
                    'success': result.success,
                    'duration': result.duration,
                    'tests_run': result.tests_run,
                    'tests_passed': result.tests_passed,
                    'errors': result.errors,
                }
                if result.details:
                    suite_data['details'] = result.details
                
                results_data['suites'].append(suite_data)
            
            results_path = current_dir / "test_results.json"
            with open(results_path, 'w') as f:
                json.dump(results_data, f, indent=2)
            
            if self.verbose:
                print(f"\\n💾 Detailed results saved to {results_path}")
                
        except Exception as e:
            if self.verbose:
                print(f"⚠️  Could not save results: {e}")

def main():
    """Main entry point for the test orchestrator."""
    parser = argparse.ArgumentParser(
        description="Hardcore Test Orchestrator for Real LaTeX Perfectionist Rules",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument("--verbose", "-v", action="store_true", 
                       help="Verbose output")
    parser.add_argument("--quick", action="store_true",
                       help="Quick mode (fewer test iterations)")
    parser.add_argument("--sequential", action="store_true",
                       help="Run tests sequentially (no parallel execution)")
    parser.add_argument("--max-workers", type=int, default=4,
                       help="Maximum parallel workers")
    parser.add_argument("--suites", nargs="+", 
                       choices=["universal", "punctuation", "mathematical", "chaos"],
                       help="Specific test suites to run")
    parser.add_argument("--verify", action="store_true",
                       help="Just verify setup without running tests")
    
    args = parser.parse_args()
    
    try:
        # Create orchestrator
        orchestrator = HardcoreTestOrchestrator(
            verbose=args.verbose,
            quick_mode=args.quick
        )
        
        if args.verify:
            print("\\n✅ VERIFICATION PASSED!")
            print(f"Orchestrator ready with {len(orchestrator.rules)} real LaTeX Perfectionist rules")
            print(f"Available rules: {', '.join(orchestrator.rules.keys())}")
            return
        
        # Run tests
        max_workers = 1 if args.sequential else args.max_workers
        results = orchestrator.run_all_tests(
            selected_suites=args.suites,
            max_workers=max_workers
        )
        
        # Exit with appropriate code
        success_rate = results['suites_passed'] / results['suites_run'] if results['suites_run'] > 0 else 0
        exit_code = 0 if success_rate >= 0.7 else 1
        sys.exit(exit_code)
        
    except KeyboardInterrupt:
        print("\\n⚠️  Test execution interrupted by user")
        sys.exit(130)
    except Exception as e:
        print(f"\\n❌ Orchestrator failed: {e}")
        if args.verbose:
            traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main()
'''
    
    return orchestrator_content

def main():
    """Set up the test suite to work with real LaTeX Perfectionist rules."""
    print("🔧 SETTING UP TESTS FOR REAL LATEX PERFECTIONIST RULES")
    print("=" * 60)
    
    current_dir = Path.cwd()
    
    # Check if we're in the right directory
    if not (current_dir.name == "tests" or (current_dir / "tests").exists()):
        print("❌ Please run this from the tests directory or project root")
        return
    
    if current_dir.name != "tests":
        current_dir = current_dir / "tests"
    
    # Check if latex_perfectionist exists
    parent_dir = current_dir.parent
    latex_perf_dir = parent_dir / "latex_perfectionist" / "rules"
    
    if not latex_perf_dir.exists():
        print(f"❌ Cannot find latex_perfectionist/rules/ directory")
        print(f"   Expected at: {latex_perf_dir}")
        print(f"   Current dir: {current_dir}")
        return
    
    print(f"✅ Found latex_perfectionist/rules at {latex_perf_dir}")
    
    # List actual rules found
    actual_rules = []
    for rule_file in latex_perf_dir.glob("*.py"):
        if rule_file.name != "__init__.py":
            rule_name = rule_file.stem
            actual_rules.append(rule_name)
    
    print(f"📋 Found {len(actual_rules)} rule files:")
    for rule in sorted(actual_rules):
        print(f"   - {rule}")
    
    # Create the real orchestrator
    orchestrator_content = create_real_rules_orchestrator()
    orchestrator_path = current_dir / "test_orchestrator.py"
    
    print(f"\\n🔄 Creating test orchestrator for real rules...")
    with open(orchestrator_path, 'w', encoding='utf-8') as f:
        f.write(orchestrator_content)
    
    print(f"✅ Updated {orchestrator_path}")
    
    print(f"\\n🎉 SETUP COMPLETE!")
    print(f"\\n🚀 Now run your tests:")
    print(f"   python3 run_hardcore_tests.py --verify    # Check setup")
    print(f"   python3 run_hardcore_tests.py             # Run all tests")
    print(f"   python3 run_hardcore_tests.py --quick     # Quick test")

if __name__ == "__main__":
    main()
