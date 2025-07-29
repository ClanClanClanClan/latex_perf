#!/usr/bin/env python3
"""
Enhanced Math Normalizer Integration Guide

This script demonstrates how to integrate the enhanced math environment normalizer
that handles custom preamble definitions into your existing LaTeX processing pipeline.

Usage:
    python3 enhanced_integration_guide.py [--demo] [--test] [--file input.tex]
"""

import sys
import argparse
from pathlib import Path
from typing import List, Set

# Assuming the enhanced normalizer is in your project
try:
    from latex_perfectionist.rules.enhanced_math_normalizer import (
        audit_with_preamble_support, 
        EnhancedAuditResult
    )
    from latex_perfectionist.rules.preamble_analyzer import (
        PreambleAnalyzer,
        CommandExpander,
        analyze_and_expand_document
    )
    ENHANCED_AVAILABLE = True
except ImportError:
    print("⚠️  Enhanced normalizer not available. Make sure it's in your project.")
    ENHANCED_AVAILABLE = False

# ═══════════════════════════════════════════════════════════════════════════════
# INTEGRATION FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════════

def process_latex_file(file_path: Path, use_enhanced: bool = True) -> dict:
    """
    Process a LaTeX file with optional enhanced normalization.
    
    Returns a dictionary with analysis results.
    """
    if not file_path.exists():
        return {"error": f"File not found: {file_path}"}
    
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        return {"error": f"Could not read file: {e}"}
    
    results = {
        "file": str(file_path),
        "content_length": len(content),
        "has_preamble": "\\documentclass" in content,
        "issues": [],
        "custom_definitions": {},
        "packages": [],
        "enhanced_used": use_enhanced and ENHANCED_AVAILABLE
    }
    
    if use_enhanced and ENHANCED_AVAILABLE:
        # Use enhanced normalizer
        try:
            enhanced_result = audit_with_preamble_support(content, {})
            
            results["issues"] = [
                {
                    "line": issue.line,
                    "type": issue.type,
                    "level": issue.level,
                    "message": issue.message
                }
                for issue in enhanced_result.issues
            ]
            
            results["custom_definitions"] = {
                "environments": list(enhanced_result.custom_environments_found),
                "commands": list(enhanced_result.custom_commands_found)
            }
            
            if enhanced_result.preamble_analysis:
                results["packages"] = list(enhanced_result.preamble_analysis.packages.keys())
                results["environment_aliases"] = enhanced_result.preamble_analysis.math_environment_aliases
                results["redefined_environments"] = enhanced_result.preamble_analysis.redefined_environments
            
            results["fixes_available"] = len(enhanced_result.fixes)
            
        except Exception as e:
            results["error"] = f"Enhanced analysis failed: {e}"
            # Fall back to basic analysis
            use_enhanced = False
    
    if not use_enhanced or not ENHANCED_AVAILABLE:
        # Use basic normalizer
        try:
            from latex_perfectionist.rules import math_env_normaliser as basic
            basic_result = basic.audit(content, {})
            
            results["issues"] = [
                {
                    "line": issue.line,
                    "type": issue.type,
                    "level": issue.level,
                    "message": issue.message
                }
                for issue in basic_result.issues
            ]
            
            results["fixes_available"] = len(basic_result.fixes)
            results["enhanced_used"] = False
            
        except Exception as e:
            results["error"] = f"Basic analysis also failed: {e}"
    
    return results

def analyze_preamble_only(content: str) -> dict:
    """Analyze only the preamble of a LaTeX document."""
    if not ENHANCED_AVAILABLE:
        return {"error": "Enhanced analyzer not available"}
    
    try:
        analyzer = PreambleAnalyzer()
        analysis = analyzer.analyze_document(content)
        
        return {
            "custom_environments": {
                name: {
                    "begin_code": env_def.begin_code,
                    "end_code": env_def.end_code,
                    "is_math": env_def.is_math,
                    "canonical_form": env_def.canonical_form
                }
                for name, env_def in analysis.custom_environments.items()
            },
            "custom_commands": {
                name: {
                    "definition": cmd_def.definition,
                    "creates_math_env": cmd_def.creates_math_env,
                    "canonical_form": cmd_def.canonical_form
                }
                for name, cmd_def in analysis.custom_commands.items()
            },
            "packages": {
                name: {
                    "math_environments": list(pkg_info.math_environments),
                    "options": pkg_info.options
                }
                for name, pkg_info in analysis.packages.items()
            },
            "math_environment_aliases": analysis.math_environment_aliases,
            "redefined_environments": analysis.redefined_environments
        }
    except Exception as e:
        return {"error": f"Preamble analysis failed: {e}"}

def expand_custom_commands(content: str) -> dict:
    """Expand custom commands in a LaTeX document."""
    if not ENHANCED_AVAILABLE:
        return {"error": "Enhanced analyzer not available"}
    
    try:
        expanded_content, analysis = analyze_and_expand_document(content)
        
        return {
            "original_length": len(content),
            "expanded_length": len(expanded_content),
            "expansion_occurred": content != expanded_content,
            "expanded_content": expanded_content,
            "custom_definitions_count": len(analysis.custom_environments) + len(analysis.custom_commands)
        }
    except Exception as e:
        return {"error": f"Command expansion failed: {e}"}

# ═══════════════════════════════════════════════════════════════════════════════
# DEMONSTRATION DOCUMENTS
# ═══════════════════════════════════════════════════════════════════════════════

DEMO_DOCUMENTS = {
    "basic_custom": r"""
\documentclass{article}
\newenvironment{myeq}{\begin{equation}}{\end{equation}}
\newcommand{\display}[1]{$$#1$$}
\begin{document}
\begin{myeq}
    E = mc^2
\end{myeq}
\display{F = ma}
$$ x^2 + y^2 = z^2 $$
\end{document}
""",
    
    "academic_paper": r"""
\documentclass{article}
\usepackage{amsmath,mathtools}
\newenvironment{theorem}[1]{\textbf{Theorem #1.}}{\qed}
\newcommand{\eq}[1]{\begin{equation}#1\end{equation}}
\newcommand{\important}[1]{$$\boxed{#1}$$}
\renewenvironment{align}{\begin{gather}}{\end{gather}}

\begin{document}
\begin{theorem}{Fundamental Theorem}
\eq{F = ma \label{eq:newton}}
\end{theorem}

\important{\int_0^\infty e^{-x^2} dx = \sqrt{\pi}}

\begin{align}
    a &= b \\
    c &= d
\end{align}
\end{document}
""",
    
    "physics_notation": r"""
\documentclass{article}
\usepackage{physics}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newenvironment{hamiltonian}{\begin{equation}H = }{\end{equation}}
\def\bigEq#1{$$\boxed{#1}$$}

\begin{document}
\begin{hamiltonian}
    \frac{p^2}{2m} + V(x)
\end{hamiltonian}

\bigEq{\bra{\psi} H \ket{\psi} = E \bra{\psi} \ket{\psi}}

$$ \int \psi^*(x) \psi(x) dx = 1 $$
\end{document}
"""
}

# ═══════════════════════════════════════════════════════════════════════════════
# MAIN FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════════

def run_demo():
    """Run demonstration of enhanced normalizer capabilities."""
    print("🚀 ENHANCED MATH NORMALIZER DEMONSTRATION")
    print("=" * 60)
    
    if not ENHANCED_AVAILABLE:
        print("❌ Enhanced normalizer not available!")
        return
    
    for name, content in DEMO_DOCUMENTS.items():
        print(f"\n📄 Demo: {name}")
        print("-" * 40)
        
        # Basic analysis
        try:
            result = audit_with_preamble_support(content, {})
            
            print(f"Issues found: {len(result.issues)}")
            for issue in result.issues:
                print(f"  - Line {issue.line}: {issue.message}")
            
            print(f"Custom environments: {result.custom_environments_found}")
            print(f"Custom commands: {result.custom_commands_found}")
            
            if result.preamble_analysis:
                print(f"Packages: {list(result.preamble_analysis.packages.keys())}")
                if result.preamble_analysis.redefined_environments:
                    print(f"Redefined environments: {result.preamble_analysis.redefined_environments}")
            
        except Exception as e:
            print(f"❌ Analysis failed: {e}")
    
    print("\n🎉 Demo completed!")

def run_integration_tests():
    """Run integration tests to verify everything works."""
    print("🧪 ENHANCED NORMALIZER INTEGRATION TESTS")
    print("=" * 50)
    
    if not ENHANCED_AVAILABLE:
        print("❌ Enhanced normalizer not available!")
        return False
    
    tests_passed = 0
    total_tests = 0
    
    # Test 1: Basic functionality
    total_tests += 1
    try:
        result = audit_with_preamble_support(DEMO_DOCUMENTS["basic_custom"], {})
        assert result.custom_environments_found
        assert result.custom_commands_found
        assert result.issues  # Should detect $$ issues
        print("✅ Test 1: Basic functionality")
        tests_passed += 1
    except Exception as e:
        print(f"❌ Test 1 failed: {e}")
    
    # Test 2: Preamble analysis
    total_tests += 1
    try:
        preamble_result = analyze_preamble_only(DEMO_DOCUMENTS["academic_paper"])
        assert "custom_environments" in preamble_result
        assert "custom_commands" in preamble_result
        assert "packages" in preamble_result
        print("✅ Test 2: Preamble analysis")
        tests_passed += 1
    except Exception as e:
        print(f"❌ Test 2 failed: {e}")
    
    # Test 3: Command expansion
    total_tests += 1
    try:
        expansion_result = expand_custom_commands(DEMO_DOCUMENTS["physics_notation"])
        assert expansion_result.get("expansion_occurred", False)
        print("✅ Test 3: Command expansion")
        tests_passed += 1
    except Exception as e:
        print(f"❌ Test 3 failed: {e}")
    
    print(f"\n📊 Results: {tests_passed}/{total_tests} tests passed")
    return tests_passed == total_tests

def process_file(file_path: str):
    """Process a specific LaTeX file."""
    path = Path(file_path)
    print(f"📄 Processing file: {path}")
    print("-" * 40)
    
    results = process_latex_file(path)
    
    if "error" in results:
        print(f"❌ Error: {results['error']}")
        return
    
    print(f"File size: {results['content_length']} characters")
    print(f"Has preamble: {results['has_preamble']}")
    print(f"Enhanced analyzer used: {results['enhanced_used']}")
    
    if results["issues"]:
        print(f"\n🔍 Issues found ({len(results['issues'])}):")
        for issue in results["issues"]:
            print(f"  - Line {issue['line']}: {issue['message']}")
    else:
        print("\n✅ No issues found!")
    
    if results["custom_definitions"]["environments"]:
        print(f"\n🏗️  Custom environments: {results['custom_definitions']['environments']}")
    
    if results["custom_definitions"]["commands"]:
        print(f"🔧 Custom commands: {results['custom_definitions']['commands']}")
    
    if results["packages"]:
        print(f"📦 Packages: {results['packages']}")
    
    print(f"\n🔧 Fixes available: {results['fixes_available']}")

def main():
    parser = argparse.ArgumentParser(
        description="Enhanced Math Normalizer Integration Guide",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 enhanced_integration_guide.py --demo
  python3 enhanced_integration_guide.py --test
  python3 enhanced_integration_guide.py --file paper.tex
        """
    )
    
    parser.add_argument("--demo", action="store_true", 
                       help="Run demonstration with sample documents")
    parser.add_argument("--test", action="store_true",
                       help="Run integration tests")
    parser.add_argument("--file", type=str,
                       help="Process a specific LaTeX file")
    
    args = parser.parse_args()
    
    if args.demo:
        run_demo()
    elif args.test:
        success = run_integration_tests()
        sys.exit(0 if success else 1)
    elif args.file:
        process_file(args.file)
    else:
        print("🎯 Enhanced Math Normalizer Integration Guide")
        print("=" * 50)
        print("Choose an option:")
        print("  --demo    Run demonstration")
        print("  --test    Run integration tests")
        print("  --file    Process a specific file")
        print("\nFor more help: python3 enhanced_integration_guide.py --help")

if __name__ == "__main__":
    main()