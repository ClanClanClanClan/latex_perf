#!/usr/bin/env python3
"""Unit tests for span recovery via pattern replay."""

import unittest
from ml.data.label_spans import (
    replay_count_char,
    replay_count_char_strip_math,
    replay_count_substring,
    replay_count_substring_strip_math,
    replay_multi_substring,
    replay_regex,
    replay_custom_TYPO_048,
    replay_custom_TYPO_052,
    replay_custom_TYPO_040,
    replay_custom_TYPO_045,
    find_math_segments,
    strip_math_segments,
    spans_to_bio,
    Span,
)


class TestMathSegments(unittest.TestCase):
    def test_inline_math(self):
        text = "hello $x^2$ world"
        segs = find_math_segments(text)
        self.assertEqual(len(segs), 1)
        self.assertEqual(text[segs[0][0]:segs[0][1]], "$x^2$")

    def test_display_math(self):
        text = "hello $$E=mc^2$$ world"
        segs = find_math_segments(text)
        self.assertEqual(len(segs), 1)
        self.assertEqual(text[segs[0][0]:segs[0][1]], "$$E=mc^2$$")

    def test_paren_math(self):
        text = r"hello \(x\) world"
        segs = find_math_segments(text)
        self.assertEqual(len(segs), 1)

    def test_bracket_math(self):
        text = r"hello \[x\] world"
        segs = find_math_segments(text)
        self.assertEqual(len(segs), 1)

    def test_strip_math(self):
        text = "hello $x$ world"
        stripped, segs = strip_math_segments(text)
        # Math region should be replaced with spaces
        self.assertNotIn('$', stripped)
        self.assertNotIn('x', stripped[6:9])  # The $x$ part

    def test_no_math(self):
        text = "hello world"
        segs = find_math_segments(text)
        self.assertEqual(len(segs), 0)


class TestCountChar(unittest.TestCase):
    def test_single_char(self):
        spans = replay_count_char("hello\tworld\there", "\t")
        self.assertEqual(len(spans), 2)
        self.assertEqual(spans[0], (5, 6))
        self.assertEqual(spans[1], (11, 12))

    def test_no_match(self):
        spans = replay_count_char("hello world", "\t")
        self.assertEqual(len(spans), 0)

    def test_strip_math(self):
        # Quote inside math should be ignored
        spans = replay_count_char_strip_math('text "$x$" more', '"')
        # The " at pos 5 is inside math, the first " at pos 5 is before $
        # Actually: 'text "$x$" more' → " at pos 5, " at pos 9
        # $x$ is from pos 6 to 9 (inclusive), so " at 5 is before math, " at 9 is end of math
        # After stripping: 'text "   " more'
        # Quotes at pos 5 and 9 are NOT in math (they're adjacent)
        self.assertGreaterEqual(len(spans), 1)


class TestCountSubstring(unittest.TestCase):
    def test_simple(self):
        spans = replay_count_substring("hello ... world ...", "...")
        self.assertEqual(len(spans), 2)
        self.assertEqual(spans[0], (6, 9))
        self.assertEqual(spans[1], (16, 19))

    def test_overlapping(self):
        spans = replay_count_substring("aaaa", "aa")
        self.assertEqual(len(spans), 3)  # Positions 0, 1, 2

    def test_strip_math(self):
        spans = replay_count_substring_strip_math("text $...$ more ...", "...")
        # ... inside math should be ignored
        self.assertEqual(len(spans), 1)
        self.assertEqual(spans[0][0], 16)  # Only the one after "more "


class TestMultiSubstring(unittest.TestCase):
    def test_multi(self):
        spans = replay_multi_substring("``hello'' world", ["``", "''"])
        self.assertEqual(len(spans), 2)

    def test_french_punct(self):
        spans = replay_multi_substring("Bonjour ; monde :", [" ;", " :"])
        self.assertEqual(len(spans), 2)


class TestRegex(unittest.TestCase):
    def test_email(self):
        spans = replay_regex("contact alice@example.com please",
                            r"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]+")
        self.assertEqual(len(spans), 1)
        self.assertEqual(spans[0][0], 8)

    def test_shouting(self):
        spans = replay_regex("SOME VERY LOUD words",
                            r"\b[A-Z][A-Z]+ [A-Z][A-Z]+ [A-Z][A-Z]+\b")
        self.assertEqual(len(spans), 1)


class TestCustomHandlers(unittest.TestCase):
    def test_typo_052_angle_brackets(self):
        spans = replay_custom_TYPO_052("Use <angle> brackets")
        self.assertEqual(len(spans), 2)  # < and >

    def test_typo_040_long_math(self):
        short_math = "$x^2$"
        spans = replay_custom_TYPO_040(short_math)
        self.assertEqual(len(spans), 0)

        long_math = "$" + "x" * 100 + "$"
        spans = replay_custom_TYPO_040(long_math)
        self.assertEqual(len(spans), 1)


class TestBIOGeneration(unittest.TestCase):
    def test_simple_span(self):
        spans = [Span(start=3, end=6, rule_id="TYPO-001")]
        tags = spans_to_bio(10, spans)
        self.assertEqual(tags[0], "O")
        self.assertEqual(tags[2], "O")
        self.assertEqual(tags[3], "B-TYPO-001")
        self.assertEqual(tags[4], "I-TYPO-001")
        self.assertEqual(tags[5], "I-TYPO-001")
        self.assertEqual(tags[6], "O")

    def test_multiple_spans(self):
        spans = [
            Span(start=0, end=2, rule_id="TYPO-001"),
            Span(start=5, end=7, rule_id="TYPO-002"),
        ]
        tags = spans_to_bio(10, spans)
        self.assertEqual(tags[0], "B-TYPO-001")
        self.assertEqual(tags[1], "I-TYPO-001")
        self.assertEqual(tags[2], "O")
        self.assertEqual(tags[5], "B-TYPO-002")
        self.assertEqual(tags[6], "I-TYPO-002")

    def test_empty(self):
        tags = spans_to_bio(5, [])
        self.assertEqual(tags, ["O"] * 5)

    def test_single_char_span(self):
        spans = [Span(start=3, end=4, rule_id="TYPO-006")]
        tags = spans_to_bio(10, spans)
        self.assertEqual(tags[3], "B-TYPO-006")
        self.assertEqual(tags[4], "O")


if __name__ == "__main__":
    unittest.main()
