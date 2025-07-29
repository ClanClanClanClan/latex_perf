#!/usr/bin/env python3
"""
Comprehensive test cases for all identified gaps in rule testing.
These tests are designed to be adversarial and catch edge cases that could
occur in production environments processing millions of academic documents.
"""

import sys
import time
import random
import string
from typing import List, Dict, Any

# Test case structure
TestCase = Dict[str, Any]

def generate_typo_001_missing_tests() -> List[TestCase]:
    """Generate missing test cases for TYPO-001 (Smart Quotes)."""
    return [
        # Malicious Input Tests
        {
            'name': 'Stack overflow - deeply nested quotes',
            'input': '"' * 10000 + 'text' + '"' * 10000,
            'expect_error': False,  # Should handle gracefully
            'timeout_ms': 1000,
            'category': 'security'
        },
        {
            'name': 'ReDoS pattern - alternating quotes',
            'input': '"a' * 50000 + '"' * 50000,
            'expect_error': False,
            'timeout_ms': 1000,
            'category': 'security'
        },
        {
            'name': 'Memory exhaustion - 1GB quoted string',
            'input': '"' + 'a' * (1024 * 1024 * 1024) + '"',
            'expect_error': False,
            'memory_limit_mb': 100,
            'category': 'security'
        },
        
        # Unicode Edge Cases
        {
            'name': 'Mixed RTL/LTR with quotes',
            'input': 'English "עברית Hebrew" mixed "العربية Arabic" text',
            'expect_issues': True,
            'category': 'unicode'
        },
        {
            'name': 'Invisible Unicode in quotes',
            'input': '"text\u200B\u200C\u200D\uFEFF\u2060\u2061"',
            'expect_issues': True,
            'category': 'unicode'
        },
        {
            'name': 'Emoji boundaries with quotes',
            'input': 'He said "Hello 👋🏽👨‍👩‍👧‍👦" and "Test 🏳️‍🌈"',
            'expect_issues': True,
            'category': 'unicode'
        },
        {
            'name': 'Combining characters across quote boundary',
            'input': '"café" where é uses combining acute',
            'input_bytes': b'"caf\xc3\xa9" where \xc3\xa9 uses combining',
            'expect_issues': True,
            'category': 'unicode'
        },
        {
            'name': 'Zero-width joiners in quoted text',
            'input': '"أم‍‍ي" (Arabic with ZWJ)',
            'expect_issues': True,
            'category': 'unicode'
        },
        
        # Package Interaction Tests
        {
            'name': 'csquotes package commands',
            'input': '\\usepackage{csquotes}\n\\enquote{test} and \\foreignquote{german}{Test}',
            'expect_issues': False,  # Should not modify csquotes commands
            'category': 'packages'
        },
        {
            'name': 'babel shorthand quotes',
            'input': '\\usepackage[german]{babel}\n"\'Test"\' and "<Test>"',
            'expect_issues': False,  # Babel shorthands should be preserved
            'category': 'packages'
        },
        {
            'name': 'fontenc T1 encoding effects',
            'input': '\\usepackage[T1]{fontenc}\n"Test with — dashes"',
            'expect_issues': True,
            'category': 'packages'
        },
        {
            'name': 'inputenc utf8 with special chars',
            'input': '\\usepackage[utf8]{inputenc}\n"café", "naïve", and "Zürich"',
            'expect_issues': True,
            'category': 'packages'
        },
        
        # Context Boundary Tests
        {
            'name': 'Quote spanning environment boundary',
            'input': '"Start text \\begin{equation} x = y \\end{equation} end text"',
            'expect_issues': True,
            'category': 'context'
        },
        {
            'name': 'Quote in macro definition',
            'input': '\\newcommand{\\myquote}[1]{"#1"}\n\\myquote{test}',
            'expect_issues': True,  # First occurrence should be fixed
            'category': 'context'
        },
        {
            'name': 'Quote in bibliography database',
            'input': '@article{key2023,\n  title = "A "nested" title with {braces}",\n  author = "Smith, J."\n}',
            'expect_issues': True,
            'category': 'context'
        },
        {
            'name': 'Quote in TikZ node',
            'input': '\\node at (0,0) {"Label text"};',
            'expect_issues': True,
            'category': 'context'
        },
        {
            'name': 'Quote in beamer overlay',
            'input': '\\only<1->{"Revealed text"}',
            'expect_issues': True,
            'category': 'context'
        },
        
        # Performance Stress Tests
        {
            'name': 'Pathological alternating pattern',
            'input': ' "a" ' * 100000,  # 100k alternating quoted/unquoted
            'expect_issues': True,
            'timeout_ms': 5000,
            'category': 'performance'
        },
        {
            'name': 'Nested quotes 10 levels deep',
            'input': '"He said ' * 10 + 'STOP' + ' he said"' * 10,
            'expect_issues': True,
            'category': 'performance'
        },
        {
            'name': 'Unicode normalization stress',
            'input': '"' + ''.join([chr(0x0300 + i % 50) for i in range(10000)]) + '"',
            'expect_issues': True,
            'category': 'performance'
        },
        
        # Fix Function Edge Cases
        {
            'name': 'Quote at exact file boundary',
            'input': 'x' * 65535 + '"boundary"',  # Common buffer size boundary
            'expect_issues': True,
            'category': 'fix_safety'
        },
        {
            'name': 'Overlapping quote regions',
            'input': '"first "nested" quote" and "second"',
            'expect_issues': True,
            'category': 'fix_safety'
        },
        {
            'name': 'Quote fix changes line numbers',
            'input': '"Line 1\nLine 2\nLine 3"',
            'expect_issues': True,
            'expect_line_preservation': True,
            'category': 'fix_safety'
        }
    ]


def generate_typo_002_missing_tests() -> List[TestCase]:
    """Generate missing test cases for TYPO-002 (Punctuation with Quotes)."""
    return [
        # Complex Punctuation Patterns
        {
            'name': 'Multiple punctuation marks together',
            'input': 'He asked "Really?!".',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'He asked "Really?!."',
            'category': 'punctuation'
        },
        {
            'name': 'Ellipsis with quotes US',
            'input': 'He said "Wait..." and left.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'He said "Wait...." and left.',  # All dots inside
            'category': 'punctuation'
        },
        {
            'name': 'Semicolon placement US',
            'input': 'He said "Hello"; she replied.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'He said "Hello;" she replied.',
            'category': 'punctuation'
        },
        {
            'name': 'Colon placement UK',
            'input': 'The rule states: "Always be careful".',
            'locale': 'en-GB',
            'expect_issues': False,  # Colon before quote is correct
            'category': 'punctuation'
        },
        {
            'name': 'Interrobang handling',
            'input': 'She asked "What‽".',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'She asked "What‽."',
            'category': 'punctuation'
        },
        
        # Quote Type Interactions
        {
            'name': 'Mixed straight and curly quotes',
            'input': 'He said "Hello" but she said "Hi".',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'quote_types'
        },
        {
            'name': 'Guillemets with English punctuation',
            'input': 'He said «Hello».',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'He said «Hello.»',
            'category': 'quote_types'
        },
        {
            'name': 'German quotes with punctuation',
            'input': 'Er sagte „Hallo".',
            'locale': 'de-DE',
            'expect_issues': False,  # German uses logical punctuation
            'category': 'quote_types'
        },
        {
            'name': 'Triple nested quotes with punctuation',
            'input': 'She said "He told me \'They yelled "Stop!".\'."',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'quote_types'
        },
        {
            'name': 'CJK quotes with Western punctuation',
            'input': 'He said 「こんにちは」.',
            'locale': 'en-US',
            'expect_issues': False,  # Don't modify CJK quotes
            'category': 'quote_types'
        },
        
        # Locale Detection Edge Cases
        {
            'name': 'Ambiguous locale - equal markers',
            'input': 'The color and colour are different. He said "Hello".',
            'locale': 'auto',
            'expect_locale': 'en-US',  # Should default when ambiguous
            'category': 'locale'
        },
        {
            'name': 'Mid-document locale switch',
            'input': '\\selectlanguage{british}\n"Hello".\n\\selectlanguage{american}\n"Hi".',
            'locale': 'auto',
            'expect_issues': True,
            'category': 'locale'
        },
        {
            'name': 'False locale indicator in quote',
            'input': 'The British spelling "colour" appeared.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'The British spelling "colour."',
            'category': 'locale'
        },
        {
            'name': 'Babel package options cascade',
            'input': '\\usepackage[main=british,american]{babel}\nHe said "Hello".',
            'locale': 'auto',
            'expect_locale': 'en-GB',  # Main language takes precedence
            'category': 'locale'
        },
        
        # LaTeX Command Interactions
        {
            'name': 'Quote in citation',
            'input': 'See \\cite[especially "Chapter 1"]{smith2023}.',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'latex'
        },
        {
            'name': 'Quote in reference',
            'input': 'See Figure \\ref{fig:"test-image"}.',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'latex'
        },
        {
            'name': 'Quote in index with subentry',
            'input': '\\index{topic!subtopic@"Special Entry"}.',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'latex'
        },
        {
            'name': 'Quote in hyperref',
            'input': '\\href{http://example.com}{Click "here"}.',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'latex'
        },
        
        # Fix Safety Issues
        {
            'name': 'Fix breaking caption',
            'input': '\\caption{Test "image".}',
            'locale': 'en-US',
            'expect_issues': True,
            'test_compilation': True,  # Verify fixed version compiles
            'category': 'fix_safety'
        },
        {
            'name': 'Fix breaking fragile command',
            'input': '\\section{The "Problem".}',
            'locale': 'en-US',
            'expect_issues': True,
            'test_compilation': True,
            'category': 'fix_safety'
        },
        {
            'name': 'Fix creating unbalanced braces',
            'input': '\\textbf{Bold "text".}',
            'locale': 'en-US',
            'expect_issues': True,
            'verify_balanced': True,
            'category': 'fix_safety'
        }
    ]


def generate_typo_003_missing_tests() -> List[TestCase]:
    """Generate missing test cases for TYPO-003 (Spelling Variations)."""
    return [
        # False Positive Scenarios
        {
            'name': 'Technical color space term',
            'input': 'The color space uses a grey scale meter for measurements.',
            'locale': 'en-US',
            'expect_issues': False,  # Technical context
            'category': 'false_positives'
        },
        {
            'name': 'Proper nouns and names',
            'input': 'Dr. Grey from the Centre for Colour Studies in Oxford.',
            'locale': 'en-US',
            'expect_issues': False,  # Proper nouns
            'category': 'false_positives'
        },
        {
            'name': 'Domain-specific fiber optics',
            'input': 'The fiber optic cable carries data, while dietary fibre is important.',
            'locale': 'en-US',
            'expect_issues': True,  # Only 'fibre' should be flagged
            'expect_fixed': 'The fiber optic cable carries data, while dietary fiber is important.',
            'category': 'false_positives'
        },
        {
            'name': 'Software program vs event programme',
            'input': 'The computer program will be presented in the programme.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'The computer program will be presented in the program.',
            'category': 'false_positives'
        },
        
        # Compound Word Handling
        {
            'name': 'Hyphenated colour compounds',
            'input': 'The colour-coded system is centre-aligned.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'The color-coded system is center-aligned.',
            'category': 'compounds'
        },
        {
            'name': 'Inconsistent compound spellings',
            'input': 'The groundwater (or ground water) level is monitored.',
            'locale': 'en-US',
            'expect_issues': False,  # Both are valid
            'category': 'compounds'
        },
        {
            'name': 'Multi-word compounds',
            'input': 'The labour market analysis shows interesting patterns.',
            'locale': 'en-US',
            'expect_issues': True,
            'expect_fixed': 'The labor market analysis shows interesting patterns.',
            'category': 'compounds'
        },
        
        # Context-Sensitive Variants
        {
            'name': 'Program ambiguity - computer context',
            'input': 'The program executes the algorithm efficiently.',
            'locale': 'en-GB',
            'expect_issues': False,  # Computer program is 'program' in UK too
            'category': 'context'
        },
        {
            'name': 'Chemistry analyze vs general analyse',
            'input': 'We analyze the compound using spectroscopy.',
            'locale': 'en-GB',
            'expect_issues': False,  # Chemistry often uses US spelling
            'category': 'context'
        },
        {
            'name': 'Legal license vs licence',
            'input': 'The license to practice law requires proper licensing.',
            'locale': 'en-GB',
            'expect_issues': True,
            'category': 'context'
        },
        
        # Performance Issues
        {
            'name': 'High variant density document',
            'input': ' '.join([
                'color', 'centre', 'analyze', 'behaviour', 'realize', 'honour'
            ] * 2000),  # 12,000 variants
            'locale': 'en-US',
            'expect_issues': True,
            'timeout_ms': 5000,
            'category': 'performance'
        },
        {
            'name': 'Regex compilation overhead test',
            'input': 'Test color, colour, center, centre variants.',
            'locale': 'en-US',
            'measure_compilation': True,
            'category': 'performance'
        },
        
        # Locale Inheritance
        {
            'name': 'otherlanguage environment',
            'input': '\\begin{otherlanguage}{american}\nThe colour is red.\n\\end{otherlanguage}',
            'locale': 'en-GB',
            'expect_issues': True,
            'category': 'locale'
        },
        {
            'name': 'Include file locale propagation',
            'input': '\\input{american-chapter}\nThe colour remains British.',
            'locale': 'en-GB',
            'expect_issues': False,  # Main document locale prevails
            'category': 'locale'
        },
        {
            'name': 'Nested language environments',
            'input': '\\begin{otherlanguage}{british}\n\\begin{otherlanguage}{american}\ncolor\n\\end{otherlanguage}\ncolour\n\\end{otherlanguage}',
            'locale': 'en-US',
            'expect_issues': True,
            'category': 'locale'
        }
    ]


def generate_menv_001_missing_tests() -> List[TestCase]:
    """Generate missing test cases for MENV-001 (eqnarray replacement)."""
    return [
        # Complex eqnarray Content
        {
            'name': 'eqnarray with nested matrix',
            'input': '\\begin{eqnarray}\nx &=& \\begin{pmatrix} a & b \\\\ c & d \\end{pmatrix} \\\\\ny &=& \\begin{bmatrix} 1 \\\\ 2 \\end{bmatrix}\n\\end{eqnarray}',
            'expect_issues': True,
            'category': 'nested'
        },
        {
            'name': 'eqnarray with custom column spec',
            'input': '\\begin{eqnarray}[rcl]\nx &=& y + z\n\\end{eqnarray}',
            'expect_issues': True,
            'category': 'format'
        },
        {
            'name': 'eqnarray with vertical spacing',
            'input': '\\begin{eqnarray}\nx &=& y \\\\[10pt]\na &=& b \\\\[-5pt]\nc &=& d\n\\end{eqnarray}',
            'expect_issues': True,
            'preserve_spacing': True,
            'category': 'spacing'
        },
        {
            'name': 'eqnarray with qquad spacing',
            'input': '\\begin{eqnarray}\nx &=& y \\qquad \\text{(definition)} \\\\\na &=& b\n\\end{eqnarray}',
            'expect_issues': True,
            'category': 'spacing'
        },
        
        # Fix Correctness Issues
        {
            'name': 'Comment preservation in eqnarray',
            'input': '\\begin{eqnarray}\nx &=& y + z % important equation\\\\\na &=& b % trivial\n\\end{eqnarray}',
            'expect_issues': True,
            'preserve_comments': True,
            'category': 'preservation'
        },
        {
            'name': 'Whitespace-sensitive layout',
            'input': '\\begin{eqnarray}\nx     &=& y     + z \\\\\n\\end{eqnarray}',
            'expect_issues': True,
            'preserve_alignment': True,
            'category': 'preservation'
        },
        
        # Package Conflicts
        {
            'name': 'eqnarray without amsmath',
            'input': '% No \\usepackage{amsmath}\n\\begin{eqnarray}\nx &=& y\n\\end{eqnarray}',
            'expect_issues': True,
            'verify_package_requirement': True,
            'category': 'packages'
        },
        {
            'name': 'Custom eqnarray redefinition',
            'input': '\\renewenvironment{eqnarray}{\\begin{align}}{\\end{align}}\n\\begin{eqnarray}\nx &=& y\n\\end{eqnarray}',
            'expect_issues': False,  # Already redefined
            'category': 'packages'
        },
        {
            'name': 'eqnarray in compatibility mode',
            'input': '\\documentclass[fleqn]{article}\n\\begin{eqnarray}\nx &=& y\n\\end{eqnarray}',
            'expect_issues': True,
            'category': 'packages'
        }
    ]


def generate_menv_002_missing_tests() -> List[TestCase]:
    """Generate missing test cases for MENV-002 ($$ replacement)."""
    return [
        # Dollar Sign Ambiguities
        {
            'name': 'Currency usage',
            'input': 'The prices are $$1.99, $$2.99, and $$3.99.',
            'expect_issues': False,
            'category': 'ambiguity'
        },
        {
            'name': 'Shell variable in verbatim',
            'input': 'Run \\texttt{echo $$HOME} to see your home.',
            'expect_issues': False,
            'category': 'ambiguity'
        },
        {
            'name': 'Escaped dollar signs',
            'input': '\\$\\$ This is not math \\$\\$',
            'expect_issues': False,
            'category': 'ambiguity'
        },
        {
            'name': 'Dollar in listings',
            'input': '\\begin{lstlisting}[language=bash]\necho $$\n\\end{lstlisting}',
            'expect_issues': False,
            'category': 'ambiguity'
        },
        
        # Spacing Preservation
        {
            'name': 'Custom vertical spacing around $$',
            'input': 'Text above.\n\n\n$$x = y$$\n\n\nText below.',
            'expect_issues': True,
            'preserve_blank_lines': True,
            'category': 'spacing'
        },
        {
            'name': 'Inline comments in display math',
            'input': '$$ % Start display math\nx = y % the main equation\n$$ % End display math',
            'expect_issues': True,
            'preserve_comments': True,
            'category': 'spacing'
        },
        {
            'name': 'Horizontal spacing preservation',
            'input': 'Text $$   x = y   $$ more text.',
            'expect_issues': True,
            'category': 'spacing'
        },
        
        # Nested Environments
        {
            'name': '$$ inside theorem',
            'input': '\\begin{theorem}\nWe have $$x = y$$ by assumption.\n\\end{theorem}',
            'expect_issues': True,
            'category': 'nesting'
        },
        {
            'name': 'Multiple $$ on same line',
            'input': 'First $$a = b$$ and second $$c = d$$ equations.',
            'expect_issues': True,
            'category': 'nesting'
        },
        {
            'name': '$$ in table cell',
            'input': '\\begin{tabular}{c}\n$$x = y$$\n\\end{tabular}',
            'expect_issues': True,
            'category': 'nesting'
        }
    ]


def generate_menv_003_missing_tests() -> List[TestCase]:
    """Generate missing test cases for MENV-003 (orphaned aligned)."""
    return [
        # Parent Environment Detection
        {
            'name': 'aligned in subequations',
            'input': '\\begin{subequations}\n\\begin{aligned}\nx &= y \\\\\na &= b\n\\end{aligned}\n\\end{subequations}',
            'expect_issues': False,  # subequations is valid parent
            'category': 'parent'
        },
        {
            'name': 'aligned in custom environment',
            'input': '\\newenvironment{mymath}{\\begin{equation}}{\\end{equation}}\n\\begin{mymath}\n\\begin{aligned}\nx &= y\n\\end{aligned}\n\\end{mymath}',
            'expect_issues': False,
            'category': 'parent'
        },
        {
            'name': 'Deeply nested aligned',
            'input': '\\begin{proof}\n\\begin{enumerate}\n\\item First:\n\\begin{aligned}\nx &= y\n\\end{aligned}\n\\end{enumerate}\n\\end{proof}',
            'expect_issues': True,
            'category': 'parent'
        },
        
        # Fix Decision Logic
        {
            'name': 'Multiple labels requiring equation',
            'input': '\\begin{aligned}\nx &= y \\label{eq:1} \\\\\na &= b \\label{eq:2}\n\\end{aligned}',
            'expect_issues': True,
            'expect_equation_star': False,  # Need equation for labels
            'category': 'decision'
        },
        {
            'name': 'aligned with numberwithin',
            'input': '\\numberwithin{equation}{section}\n\\begin{aligned}\nx &= y\n\\end{aligned}',
            'expect_issues': True,
            'category': 'decision'
        },
        
        # Edge Cases
        {
            'name': 'Empty equation before aligned',
            'input': '\\begin{equation}\\end{equation}\n\\begin{aligned}\nx &= y\n\\end{aligned}',
            'expect_issues': True,
            'category': 'edge'
        },
        {
            'name': 'Commented parent environment',
            'input': '%\\begin{equation}\n\\begin{aligned}\nx &= y\n\\end{aligned}\n%\\end{equation}',
            'expect_issues': True,
            'category': 'edge'
        },
        {
            'name': 'aligned split across include',
            'input': '\\begin{aligned}\n\\input{equations}\n\\end{aligned}',
            'expect_issues': True,
            'category': 'edge'
        }
    ]


def generate_math_001_missing_tests() -> List[TestCase]:
    """Generate missing test cases for MATH-001 (decimal separators)."""
    return [
        # Complex Number Formats
        {
            'name': 'IP address v4',
            'input': 'Connect to server at 192.168.1.1 on port 8080.',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'formats'
        },
        {
            'name': 'IP address v6 with dots',
            'input': 'The IPv6 address is 2001:db8::8a2e:370:7334.',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'formats'
        },
        {
            'name': 'Time format 24-hour',
            'input': 'Das Meeting ist um 14.30 Uhr.',
            'locale': 'de-DE',
            'expect_issues': False,  # Time format
            'category': 'formats'
        },
        {
            'name': 'Scientific notation positive exponent',
            'input': 'Avogadro constant is 6.022E23 per mole.',
            'locale': 'de-DE',
            'expect_issues': False,  # Scientific notation
            'category': 'formats'
        },
        {
            'name': 'Scientific notation negative exponent',
            'input': 'The value is 1.23e-4 meters.',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'formats'
        },
        {
            'name': 'Version number multi-level',
            'input': 'Using Python 3.9.1.2 for testing.',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'formats'
        },
        {
            'name': 'pH range with dash',
            'input': 'Optimal pH range is 6.5-7.5 for growth.',
            'locale': 'de-DE',
            'expect_issues': False,  # Range, not decimal
            'category': 'formats'
        },
        {
            'name': 'Temperature range',
            'input': 'Temperature should be 20.0-25.0°C.',
            'locale': 'de-DE',
            'expect_issues': False,  # Ranges preserved
            'category': 'formats'
        },
        
        # Mathematical Context
        {
            'name': 'Decimal in subscript',
            'input': 'The value $x_{2.5}$ represents the median.',
            'locale': 'de-DE',
            'expect_issues': False,  # Math mode
            'category': 'math'
        },
        {
            'name': 'Decimal in superscript',
            'input': 'Calculate $2^{3.14}$ approximately.',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'math'
        },
        {
            'name': 'Decimal in macro argument',
            'input': '\\newcommand{\\const}{3.14}\nThe constant is \\const.',
            'locale': 'de-DE',
            'expect_issues': True,  # Only in definition
            'category': 'math'
        },
        {
            'name': 'siunitx package number',
            'input': '\\SI{3.14}{\\meter} is the measurement.',
            'locale': 'de-DE',
            'expect_issues': False,  # siunitx handles its own formatting
            'category': 'math'
        },
        {
            'name': 'pgfmath calculation',
            'input': '\\pgfmathsetmacro{\\result}{3.14 * 2}',
            'locale': 'de-DE',
            'expect_issues': False,  # Would break calculation
            'category': 'math'
        },
        
        # Locale Detection Accuracy
        {
            'name': 'Mathematical constant pi',
            'input': 'The value of π is approximately 3.14159265...',
            'locale': 'de-DE',
            'expect_issues': False,  # Universal constant
            'category': 'locale'
        },
        {
            'name': 'Bilingual document with tables',
            'input': 'English section: 3.14\n\\section{Deutsch}\nDer Wert ist 2.71.',
            'locale': 'auto',
            'expect_mixed_locales': True,
            'category': 'locale'
        },
        {
            'name': 'CSV data in document',
            'input': '\\begin{verbatim}\ndata.csv:\n1.23,4.56\n7.89,0.12\n\\end{verbatim}',
            'locale': 'de-DE',
            'expect_issues': False,  # Data format
            'category': 'locale'
        },
        
        # Fix Safety
        {
            'name': 'TikZ coordinate',
            'input': '\\draw (0,0) -- (3.14,2.71);',
            'locale': 'de-DE',
            'expect_issues': False,  # Would break TikZ
            'category': 'safety'
        },
        {
            'name': 'Array column specification',
            'input': '\\begin{array}{r@{.}l}\n3&14\n\\end{array}',
            'locale': 'de-DE',
            'expect_issues': False,
            'category': 'safety'
        },
        {
            'name': 'Decimal in file path',
            'input': '\\input{chapter2.3.tex}',
            'locale': 'de-DE',
            'expect_issues': False,  # File name
            'category': 'safety'
        }
    ]


def generate_stress_test_document(size_mb: int = 10) -> str:
    """Generate a large document for stress testing."""
    content = []
    target_size = size_mb * 1024 * 1024
    current_size = 0
    
    patterns = [
        'He said "hello world" to me. ',
        'The colour of the centre is gray. ',
        '\\begin{eqnarray}\nx &=& y + z\n\\end{eqnarray}\n',
        '$$E = mc^2$$\n',
        'The value is 3.14 which is important. ',
    ]
    
    while current_size < target_size:
        chunk = random.choice(patterns) * 100
        content.append(chunk)
        current_size += len(chunk)
    
    return ''.join(content)


def generate_malicious_patterns() -> List[str]:
    """Generate patterns designed to cause ReDoS or other failures."""
    return [
        # Exponential backtracking patterns
        '"' + 'a' * 50 + '"' * 50,
        '(' * 50 + ')' * 50,
        '\\begin{' + 'a' * 100 + '}',
        
        # Memory exhaustion patterns  
        '"' * 1000000,
        'x' * (1024 * 1024 * 100),  # 100MB string
        
        # Stack overflow patterns
        '\\begin{' * 10000 + 'env' + '}' * 10000,
        
        # Unicode abuse
        '\u0000' * 1000,  # Null bytes
        '\uffff' * 1000,  # Invalid Unicode
        
        # Path traversal attempts
        '\\input{../../../../etc/passwd}',
        '\\include{C:\\Windows\\System32\\config\\sam}',
    ]


if __name__ == '__main__':
    print("LaTeX Perfectionist Missing Test Cases")
    print("=" * 80)
    
    # Generate all missing tests
    all_tests = {
        'TYPO-001': generate_typo_001_missing_tests(),
        'TYPO-002': generate_typo_002_missing_tests(),
        'TYPO-003': generate_typo_003_missing_tests(),
        'MENV-001': generate_menv_001_missing_tests(),
        'MENV-002': generate_menv_002_missing_tests(),
        'MENV-003': generate_menv_003_missing_tests(),
        'MATH-001': generate_math_001_missing_tests(),
    }
    
    # Summary statistics
    total_tests = sum(len(tests) for tests in all_tests.values())
    print(f"\nTotal missing test cases identified: {total_tests}")
    
    for rule_id, tests in all_tests.items():
        categories = {}
        for test in tests:
            cat = test.get('category', 'other')
            categories[cat] = categories.get(cat, 0) + 1
        
        print(f"\n{rule_id}: {len(tests)} missing tests")
        for cat, count in sorted(categories.items()):
            print(f"  - {cat}: {count}")
    
    print("\n" + "=" * 80)
    print("These test cases should be implemented to ensure production readiness.")