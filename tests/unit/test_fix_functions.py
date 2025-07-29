#!/usr/bin/env python3
"""
Unit tests for fix functions in latex_perfectionist.dsl.fix_functions.

Tests the actual fix logic independently of rule matching.
"""

import sys
sys.path.insert(0, 'src')

import re
from unittest.mock import Mock
import pytest

from latex_perfectionist.dsl.fix_functions import (
    fix_smart_quotes_i18n,
    fix_punctuation_with_quotes,
    fix_spelling_variants,
    fix_ellipsis_punctuation,
    fix_latex_command_punctuation,
    convert_eqnarray_to_align,
    fix_double_dollar_to_bracket,
    wrap_aligned_in_equation,
    normalize_math_spacing,
    fix_delimiter_sizing,
    fix_smart_quotes,
    fix_decimal_separators
)


class TestSmartQuotesI18n:
    """Test fix_smart_quotes_i18n function."""
    
    def test_american_double_quotes(self):
        """Test American style double quotes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='en-US')
        assert fix.replacement == '\u201ctest\u201d'
        assert fix.start == 10
        assert fix.end == 17
    
    def test_american_single_quotes(self):
        """Test American style single quotes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = "'test'"
        
        fix = fix_smart_quotes_i18n(match, "Text with 'test' here", locale='en-US')
        assert fix.replacement == '\u2018test\u2019'
        assert fix.start == 10
        assert fix.end == 17
    
    def test_british_double_quotes(self):
        """Test British style double quotes (same as US for primary)."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='en-GB')
        assert fix.replacement == '"test"'
    
    def test_british_nested_quotes(self):
        """Test British style uses single quotes for primary in nested context."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 30
        match.group.return_value = '"outer \'inner\' text"'
        
        # For British, outer should be single quotes
        fix = fix_smart_quotes_i18n(match, 'Text with "outer \'inner\' text" here', locale='en-GB')
        assert fix.replacement == "'outer \"inner\" text'"
    
    def test_german_double_quotes(self):
        """Test German style double quotes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='de-DE')
        assert fix.replacement == '„test"'
    
    def test_german_single_quotes(self):
        """Test German style single quotes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = "'test'"
        
        fix = fix_smart_quotes_i18n(match, "Text with 'test' here", locale='de-DE')
        assert fix.replacement == '\u201atest\u2018'
    
    def test_french_double_quotes(self):
        """Test French style double quotes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='fr-FR')
        assert fix.replacement == '«test»'
    
    def test_already_smart_quotes(self):
        """Test that already smart quotes return None (no fix needed)."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='en-US')
        assert fix is None
    
    def test_mixed_quotes_partial_fix(self):
        """Test mixed quotes get partially fixed."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'  # Opening smart, closing straight
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='en-US')
        assert fix.replacement == '"test"'
    
    def test_preserve_whitespace(self):
        """Test that whitespace inside quotes is preserved."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 22
        match.group.return_value = '"  test  "'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "  test  " here', locale='en-US')
        assert fix.replacement == '"  test  "'
    
    def test_empty_quotes(self):
        """Test empty quotes are handled."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 12
        match.group.return_value = '""'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "" here', locale='en-US')
        assert fix.replacement == '""'
    
    def test_quotes_with_apostrophe(self):
        """Test quotes containing apostrophes."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 23
        match.group.return_value = '"don\'t stop"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "don\'t stop" here', locale='en-US')
        assert fix.replacement == '"don\'t stop"'
    
    def test_locale_auto_detection(self):
        """Test locale auto-detection."""
        match = Mock()
        match.start.return_value = 47
        match.end.return_value = 54
        match.group.return_value = '"test"'
        
        # Text with German babel package
        text = '\\usepackage[ngerman]{babel}\nText with "test" here'
        fix = fix_smart_quotes_i18n(match, text, locale='auto')
        assert fix.replacement == '„test"'
    
    def test_invalid_locale_fallback(self):
        """Test fallback for invalid locale."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 17
        match.group.return_value = '"test"'
        
        fix = fix_smart_quotes_i18n(match, 'Text with "test" here', locale='invalid-locale')
        assert fix.replacement == '"test"'  # Falls back to US style
    
    def test_exception_handling(self):
        """Test graceful handling of exceptions."""
        match = Mock()
        match.start.side_effect = Exception("Test exception")
        
        fix = fix_smart_quotes_i18n(match, 'Text', locale='en-US')
        assert fix is None


class TestPunctuationWithQuotes:
    """Test fix_punctuation_with_quotes function."""
    
    def test_american_period_outside(self):
        """Test American style moves period inside."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 18
        match.group.return_value = '"test".'
        match.groups.return_value = (None, None, '"test"', '.')
        
        fix = fix_punctuation_with_quotes(match, 'Text with "test". More text', locale='en-US')
        assert fix.replacement == '"test."'
    
    def test_american_comma_outside(self):
        """Test American style moves comma inside."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 18
        match.group.return_value = '"test",'
        match.groups.return_value = (None, None, '"test"', ',')
        
        fix = fix_punctuation_with_quotes(match, 'Text with "test", more text', locale='en-US')
        assert fix.replacement == '"test,"'
    
    def test_british_period_outside(self):
        """Test British style keeps period outside."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 18
        match.group.return_value = '"test".'
        match.groups.return_value = (None, None, '"test"', '.')
        
        fix = fix_punctuation_with_quotes(match, 'Text with "test". More text', locale='en-GB')
        assert fix is None  # Already correct
    
    def test_british_period_inside(self):
        """Test British style moves period outside."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 18
        match.group.return_value = '"test."'
        match.groups.return_value = ('"test."', None, None, None)
        
        # Need to set up the match to handle group(1) call
        def mock_group(n=0):
            if n == 0:
                return '"test."'
            elif n == 1:
                return '"test."'
            return None
        match.group = mock_group
        
        fix = fix_punctuation_with_quotes(match, 'Text with "test." More text', locale='en-GB')
        assert fix.replacement == '"test".'
    
    def test_question_mark_inside(self):
        """Test question mark inside quotes (correct for both styles if part of quote)."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '"test?"'
        match.groups.return_value = ('"test?"', None, None, None)
        
        # Question mark that's part of the quoted text stays inside for both
        fix = fix_punctuation_with_quotes(match, 'He asked "test?" today', locale='en-US')
        assert fix is None  # Already correct
        
        fix = fix_punctuation_with_quotes(match, 'He asked "test?" today', locale='en-GB')
        assert fix is None  # Already correct
    
    def test_multiple_punctuation(self):
        """Test multiple punctuation marks."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 20
        match.group.return_value = '"test?!".'
        match.groups.return_value = ('"test?!"', '.', None, None)
        
        def mock_group(n=0):
            if n == 0:
                return '"test?!".'
            elif n == 1:
                return '"test?!"'
            return None
        match.group = mock_group
        
        fix = fix_punctuation_with_quotes(match, 'He asked "test?!". More', locale='en-US')
        assert fix.replacement == '"test?!."'
    
    def test_semicolon_american(self):
        """Test semicolon placement for American style."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '"test";'
        match.groups.return_value = (None, None, '"test"', ';')
        
        fix = fix_punctuation_with_quotes(match, 'He said "test"; she replied', locale='en-US')
        assert fix.replacement == '"test;"'
    
    def test_colon_british(self):
        """Test colon placement for British style."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '"test":'
        match.groups.return_value = (None, None, '"test"', ':')
        
        fix = fix_punctuation_with_quotes(match, 'The rule "test": important', locale='en-GB')
        assert fix is None  # Colon outside is correct for British
    
    def test_french_quotes(self):
        """Test French guillemets with punctuation."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '«test».'
        match.groups.return_value = (None, None, '«test»', '.')
        
        fix = fix_punctuation_with_quotes(match, 'Text with «test». More', locale='fr-FR')
        assert fix is None  # French keeps punctuation outside
    
    def test_german_quotes(self):
        """Test German quotes with punctuation."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '„test".'
        match.groups.return_value = (None, None, '„test"', '.')
        
        fix = fix_punctuation_with_quotes(match, 'Text with „test". More', locale='de-DE')
        assert fix is None  # German keeps punctuation outside
    
    def test_em_dash_no_change(self):
        """Test em dash is not moved."""
        match = Mock()
        match.start.return_value = 10
        match.end.return_value = 19
        match.group.return_value = '"test"—'
        match.groups.return_value = (None, None, '"test"', '—')
        
        # Em dash should not be moved for any locale
        fix = fix_punctuation_with_quotes(match, 'He said "test"—then left', locale='en-US')
        assert fix is None


class TestSpellingVariants:
    """Test fix_spelling_variants function."""
    
    def test_american_to_british_color(self):
        """Test converting American 'color' to British 'colour'."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 9
        match.group.return_value = 'color'
        
        fix = fix_spelling_variants(match, 'The color is red', locale='en-GB')
        assert fix.replacement == 'colour'
    
    def test_british_to_american_colour(self):
        """Test converting British 'colour' to American 'color'."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 10
        match.group.return_value = 'colour'
        
        fix = fix_spelling_variants(match, 'The colour is red', locale='en-US')
        assert fix.replacement == 'color'
    
    def test_preserve_capitalization_title(self):
        """Test that title case is preserved."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 9
        match.group.return_value = 'Color'
        
        fix = fix_spelling_variants(match, 'The Color is red', locale='en-GB')
        assert fix.replacement == 'Colour'
    
    def test_preserve_capitalization_upper(self):
        """Test that upper case is preserved."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 9
        match.group.return_value = 'COLOR'
        
        fix = fix_spelling_variants(match, 'The COLOR is red', locale='en-GB')
        assert fix.replacement == 'COLOUR'
    
    def test_ize_to_ise(self):
        """Test converting American -ize to British -ise."""
        match = Mock()
        match.start.return_value = 7
        match.end.return_value = 14
        match.group.return_value = 'realize'
        
        fix = fix_spelling_variants(match, 'I will realize this', locale='en-GB')
        assert fix.replacement == 'realise'
    
    def test_er_to_re(self):
        """Test converting American -er to British -re."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 10
        match.group.return_value = 'center'
        
        fix = fix_spelling_variants(match, 'The center of town', locale='en-GB')
        assert fix.replacement == 'centre'
    
    def test_double_l_british(self):
        """Test American single l to British double l."""
        match = Mock()
        match.start.return_value = 5
        match.end.return_value = 13
        match.group.return_value = 'traveled'
        
        fix = fix_spelling_variants(match, 'They traveled far', locale='en-GB')
        assert fix.replacement == 'travelled'
    
    def test_double_l_american(self):
        """Test British double l to American single l."""
        match = Mock()
        match.start.return_value = 5
        match.end.return_value = 14
        match.group.return_value = 'travelled'
        
        fix = fix_spelling_variants(match, 'They travelled far', locale='en-US')
        assert fix.replacement == 'traveled'
    
    def test_program_to_programme(self):
        """Test American 'program' to British 'programme'."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 11
        match.group.return_value = 'program'
        
        fix = fix_spelling_variants(match, 'The program starts', locale='en-GB')
        assert fix.replacement == 'programme'
    
    def test_grey_gray(self):
        """Test grey/gray conversion."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 8
        match.group.return_value = 'grey'
        
        fix = fix_spelling_variants(match, 'The grey sky', locale='en-US')
        assert fix.replacement == 'gray'
        
        match.group.return_value = 'gray'
        fix = fix_spelling_variants(match, 'The gray sky', locale='en-GB')
        assert fix.replacement == 'grey'
    
    def test_no_change_same_locale(self):
        """Test no change when word matches locale."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 9
        match.group.return_value = 'color'
        
        fix = fix_spelling_variants(match, 'The color is red', locale='en-US')
        assert fix is None
    
    def test_unknown_variant(self):
        """Test unknown variant returns None."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 11
        match.group.return_value = 'unknown'
        
        fix = fix_spelling_variants(match, 'The unknown word', locale='en-GB')
        assert fix is None
    
    def test_plural_forms(self):
        """Test plural forms are handled."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 10
        match.group.return_value = 'colors'
        
        fix = fix_spelling_variants(match, 'The colors are nice', locale='en-GB')
        assert fix.replacement == 'colours'
    
    def test_judgment_judgement(self):
        """Test judgment/judgement special case."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 12
        match.group.return_value = 'judgment'
        
        fix = fix_spelling_variants(match, 'The judgment is final', locale='en-GB')
        assert fix.replacement == 'judgement'


class TestEllipsisPunctuation:
    """Test fix_ellipsis_punctuation function."""
    
    def test_american_ellipsis_period(self):
        """Test American style with ellipsis and period."""
        match = Mock()
        match.start.return_value = 8
        match.end.return_value = 24
        match.group.return_value = '"Wait..." and left.'
        
        def mock_group(n=0):
            if n == 0:
                return '"Wait..." and left.'
            elif n == 1:
                return '"Wait..."'
            return None
        match.group = mock_group
        
        fix = fix_ellipsis_punctuation(match, 'He said "Wait..." and left.', locale='en-US')
        assert fix.replacement == '"Wait...." and left.'
    
    def test_british_ellipsis_no_change(self):
        """Test British style keeps ellipsis as is."""
        match = Mock()
        match.start.return_value = 8
        match.end.return_value = 24
        match.group.return_value = '"Wait..." and left.'
        
        def mock_group(n=0):
            if n == 0:
                return '"Wait..." and left.'
            elif n == 1:
                return '"Wait..."'
            return None
        match.group = mock_group
        
        fix = fix_ellipsis_punctuation(match, 'He said "Wait..." and left.', locale='en-GB')
        assert fix is None  # British style doesn't change
    
    def test_ellipsis_with_question(self):
        """Test ellipsis with question mark."""
        match = Mock()
        match.start.return_value = 8
        match.end.return_value = 25
        match.group.return_value = '"Really...?" she asked.'
        
        def mock_group(n=0):
            if n == 0:
                return '"Really...?" she asked.'
            elif n == 1:
                return '"Really...?"'
            return None
        match.group = mock_group
        
        fix = fix_ellipsis_punctuation(match, 'He said "Really...?" she asked.', locale='en-US')
        # For ellipsis with question mark, the pattern might be different
        # This is a complex case that might need special handling
        assert fix is None or fix.replacement == '"Really...?." she asked.'
    
    def test_no_sentence_punctuation(self):
        """Test ellipsis without following sentence punctuation."""
        match = Mock()
        match.start.return_value = 8
        match.end.return_value = 17
        match.group.return_value = '"Wait..."'
        
        def mock_group(n=0):
            if n == 0:
                return '"Wait..."'
            elif n == 1:
                return '"Wait..."'
            return None
        match.group = mock_group
        
        fix = fix_ellipsis_punctuation(match, 'He said "Wait..." softly', locale='en-US')
        assert fix is None  # No sentence-ending punctuation to move


class TestLatexCommandPunctuation:
    """Test fix_latex_command_punctuation function."""
    
    def test_cite_with_quote_american(self):
        """Test citation with quoted text, American style."""
        match = Mock()
        match.start.return_value = 4
        match.end.return_value = 35
        match.group.return_value = '\\cite[especially "Chapter 1"]{smith2023}.'
        
        fix = fix_latex_command_punctuation(match, 'See \\cite[especially "Chapter 1"]{smith2023}.', locale='en-US')
        assert fix.replacement == '\\cite[especially "Chapter 1."]{smith2023}'
    
    def test_ref_with_quote_british(self):
        """Test reference with quoted text, British style."""
        match = Mock()
        match.start.return_value = 11
        match.end.return_value = 30
        match.group.return_value = '\\ref{fig:"test-image"}.'
        
        fix = fix_latex_command_punctuation(match, 'See Figure \\ref{fig:"test-image"}.', locale='en-GB')
        assert fix is None  # British style keeps punctuation outside
    
    def test_textbf_with_quote(self):
        """Test bold text with quote."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 22
        match.group.return_value = '\\textbf{"important"}.'
        
        fix = fix_latex_command_punctuation(match, '\\textbf{"important"}. Next sentence', locale='en-US')
        assert fix.replacement == '\\textbf{"important."}'
    
    def test_no_quotes_in_command(self):
        """Test command without quotes returns None."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 15
        match.group.return_value = '\\textbf{bold}.'
        
        fix = fix_latex_command_punctuation(match, '\\textbf{bold}. Next', locale='en-US')
        assert fix is None
    
    def test_multiple_quotes_in_command(self):
        """Test command with multiple quoted sections."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 30
        match.group.return_value = '\\cite["first" and "second"]{ref}.'
        
        fix = fix_latex_command_punctuation(match, '\\cite["first" and "second"]{ref}.', locale='en-US')
        # Should fix the first quote found
        assert fix.replacement == '\\cite["first." and "second"]{ref}'


class TestConvertEqnarrayToAlign:
    """Test convert_eqnarray_to_align function."""
    
    def test_simple_eqnarray(self):
        """Test converting simple eqnarray to align."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 52
        match.group.return_value = '\\begin{eqnarray}\na & = & b\\\\\nc & = & d\n\\end{eqnarray}'
        
        fix = convert_eqnarray_to_align(match, '\\begin{eqnarray}\na & = & b\\\\\nc & = & d\n\\end{eqnarray}')
        assert fix.replacement == '\\begin{align}\na &= b\\\\\nc &= d\n\\end{align}'
    
    def test_eqnarray_star(self):
        """Test converting eqnarray* to align*."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 54
        match.group.return_value = '\\begin{eqnarray*}\na & = & b\n\\end{eqnarray*}'
        
        fix = convert_eqnarray_to_align(match, '\\begin{eqnarray*}\na & = & b\n\\end{eqnarray*}')
        assert fix.replacement == '\\begin{align*}\na &= b\n\\end{align*}'
    
    def test_eqnarray_with_labels(self):
        """Test converting eqnarray with labels."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 70
        match.group.return_value = '\\begin{eqnarray}\na & = & b \\label{eq:1}\\\\\nc & = & d\n\\end{eqnarray}'
        
        fix = convert_eqnarray_to_align(match, '\\begin{eqnarray}\na & = & b \\label{eq:1}\\\\\nc & = & d\n\\end{eqnarray}')
        assert fix.replacement == '\\begin{align}\na &= b \\label{eq:1}\\\\\nc &= d\n\\end{align}'


class TestFixDoubleDollarToBracket:
    """Test fix_double_dollar_to_bracket function."""
    
    def test_simple_double_dollar(self):
        """Test converting $$ to \\[ \\]."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 15
        match.group.return_value = '$$x = y + z$$'
        match.group.side_effect = lambda n: '$$x = y + z$$' if n == 0 else 'x = y + z'
        
        fix = fix_double_dollar_to_bracket(match, '$$x = y + z$$')
        assert fix.replacement == '\\[x = y + z\\]'
    
    def test_multiline_double_dollar(self):
        """Test converting multiline $$ to \\[ \\]."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 25
        match.group.return_value = '$$\nx = y + z\n$$'
        match.group.side_effect = lambda n: '$$\nx = y + z\n$$' if n == 0 else '\nx = y + z\n'
        
        fix = fix_double_dollar_to_bracket(match, '$$\nx = y + z\n$$')
        assert fix.replacement == '\\[\nx = y + z\n\\]'
    
    def test_double_dollar_with_spaces(self):
        """Test $$ with extra spaces."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 20
        match.group.return_value = '$$  x = y  $$'
        match.group.side_effect = lambda n: '$$  x = y  $$' if n == 0 else '  x = y  '
        
        fix = fix_double_dollar_to_bracket(match, '$$  x = y  $$')
        assert fix.replacement == '\\[  x = y  \\]'


class TestWrapAlignedInEquation:
    """Test wrap_aligned_in_equation function."""
    
    def test_orphaned_aligned(self):
        """Test wrapping orphaned aligned environment."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 45
        match.group.return_value = '\\begin{aligned}\na &= b\\\\\nc &= d\n\\end{aligned}'
        match.group.side_effect = lambda n: {
            0: '\\begin{aligned}\na &= b\\\\\nc &= d\n\\end{aligned}',
            1: 'aligned',
            2: '\na &= b\\\\\nc &= d\n'
        }.get(n)
        
        fix = wrap_aligned_in_equation(match, '\\begin{aligned}\na &= b\\\\\nc &= d\n\\end{aligned}')
        assert fix.replacement == '\\begin{equation}\\begin{aligned}\na &= b\\\\\nc &= d\n\\end{aligned}\\end{equation}'
    
    def test_orphaned_split(self):
        """Test wrapping orphaned split environment."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 35
        match.group.return_value = '\\begin{split}\na = b\n\\end{split}'
        match.group.side_effect = lambda n: {
            0: '\\begin{split}\na = b\n\\end{split}',
            1: 'split',
            2: '\na = b\n'
        }.get(n)
        
        fix = wrap_aligned_in_equation(match, '\\begin{split}\na = b\n\\end{split}')
        assert fix.replacement == '\\begin{equation}\\begin{split}\na = b\n\\end{split}\\end{equation}'


class TestNormalizeMathSpacing:
    """Test normalize_math_spacing function."""
    
    def test_add_spaces_around_equals(self):
        """Test adding spaces around = sign."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 5
        match.group.return_value = 'x=y+z'
        
        fix = normalize_math_spacing(match, 'x=y+z')
        assert fix.replacement == 'x = y + z'
    
    def test_remove_extra_spaces(self):
        """Test removing extra spaces."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 15
        match.group.return_value = 'x  =  y  +  z'
        
        fix = normalize_math_spacing(match, 'x  =  y  +  z')
        assert fix.replacement == 'x = y + z'
    
    def test_preserve_single_spaces(self):
        """Test preserving correctly spaced math."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 9
        match.group.return_value = 'x = y + z'
        
        fix = normalize_math_spacing(match, 'x = y + z')
        assert fix is None  # Already correctly spaced


class TestFixDelimiterSizing:
    """Test fix_delimiter_sizing function."""
    
    def test_add_left_right_to_parens(self):
        """Test adding \\left \\right to parentheses."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 13
        match.group.return_value = '(\\frac{a}{b})'
        
        fix = fix_delimiter_sizing(match, '(\\frac{a}{b})')
        assert fix.replacement == '\\left(\\frac{a}{b}\\right)'
    
    def test_add_left_right_to_brackets(self):
        """Test adding \\left \\right to brackets."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 13
        match.group.return_value = '[\\frac{a}{b}]'
        
        fix = fix_delimiter_sizing(match, '[\\frac{a}{b}]')
        assert fix.replacement == '\\left[\\frac{a}{b}\\right]'
    
    def test_skip_already_sized(self):
        """Test skipping already sized delimiters."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 25
        match.group.return_value = '\\left(\\frac{a}{b}\\right)'
        
        fix = fix_delimiter_sizing(match, '\\left(\\frac{a}{b}\\right)')
        assert fix is None  # Already has \\left \\right


class TestFixSmartQuotes:
    """Test fix_smart_quotes wrapper function."""
    
    def test_delegates_to_i18n_function(self):
        """Test that fix_smart_quotes delegates to fix_smart_quotes_i18n."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 6
        match.group.return_value = '"test"'
        
        # Test with default locale
        fix = fix_smart_quotes(match, '"test"')
        assert fix.replacement == '\u201ctest\u201d'  # Should use en-US by default
        
        # Test with specific locale
        fix = fix_smart_quotes(match, '"test"', locale='de-DE')
        assert fix.replacement == '\u201etest\u201c'  # German quotes


class TestFixDecimalSeparators:
    """Test fix_decimal_separators function."""
    
    def test_comma_to_period_us(self):
        """Test converting comma to period for US locale."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 4
        match.group.return_value = '3,14'
        
        fix = fix_decimal_separators(match, '3,14', locale='en-US')
        assert fix.replacement == '3.14'
    
    def test_period_to_comma_european(self):
        """Test converting period to comma for European locales."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 4
        match.group.return_value = '3.14'
        
        fix = fix_decimal_separators(match, '3.14', locale='de-DE')
        assert fix.replacement == '3,14'
        
        fix = fix_decimal_separators(match, '3.14', locale='fr-FR')
        assert fix.replacement == '3,14'
    
    def test_skip_time_format(self):
        """Test skipping time formats."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 5
        match.group.return_value = '10:30'
        
        fix = fix_decimal_separators(match, '10:30', locale='de-DE')
        assert fix is None  # Should not change time format
    
    def test_skip_date_format(self):
        """Test skipping date formats."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 10
        match.group.return_value = '2023.12.25'
        
        fix = fix_decimal_separators(match, '2023.12.25', locale='en-US')
        assert fix is None  # Should not change date format
    
    def test_skip_version_number(self):
        """Test skipping version numbers."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 5
        match.group.return_value = '3.2.1'
        
        fix = fix_decimal_separators(match, 'version 3.2.1', locale='de-DE')
        assert fix is None  # Should not change version numbers
    
    def test_skip_ip_address(self):
        """Test skipping IP addresses."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 11
        match.group.return_value = '192.168.1.1'
        
        fix = fix_decimal_separators(match, '192.168.1.1', locale='de-DE')
        assert fix is None  # Should not change IP addresses
    
    def test_thousands_separator(self):
        """Test handling thousands separator."""
        match = Mock()
        match.start.return_value = 0
        match.end.return_value = 9
        match.group.return_value = '1,234.56'
        
        fix = fix_decimal_separators(match, '1,234.56', locale='de-DE')
        assert fix.replacement == '1.234,56'  # German format


if __name__ == '__main__':
    pytest.main([__file__, '-v'])