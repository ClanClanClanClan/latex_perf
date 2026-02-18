#!/usr/bin/env python3
"""Unit tests for feature extraction."""

import unittest
from ml.data.feature_extract import (
    tokenize_lite,
    TokenKind,
    char_class,
    compute_in_math_array,
    compute_line_features,
    extract_ngram_features,
    assign_token_kinds,
    extract_features_for_document,
)


class TestTokenizer(unittest.TestCase):
    def test_simple_text(self):
        tokens = tokenize_lite("hello world")
        self.assertEqual(len(tokens), 3)  # word, space, word
        self.assertEqual(tokens[0].kind, TokenKind.Word)
        self.assertEqual(tokens[0].text, "hello")
        self.assertEqual(tokens[1].kind, TokenKind.Space)
        self.assertEqual(tokens[2].kind, TokenKind.Word)

    def test_latex_command(self):
        tokens = tokenize_lite("\\alpha")
        self.assertEqual(len(tokens), 1)
        self.assertEqual(tokens[0].kind, TokenKind.Command)
        self.assertEqual(tokens[0].text, "\\alpha")

    def test_math_delimiters(self):
        tokens = tokenize_lite("$x$")
        kinds = [t.kind for t in tokens]
        self.assertIn(TokenKind.MathDelim, kinds)

    def test_brackets(self):
        tokens = tokenize_lite("{text}")
        self.assertEqual(tokens[0].kind, TokenKind.BracketOpen)
        self.assertEqual(tokens[-1].kind, TokenKind.BracketClose)

    def test_newline(self):
        tokens = tokenize_lite("hello\nworld")
        kinds = [t.kind for t in tokens]
        self.assertIn(TokenKind.Newline, kinds)


class TestCharClass(unittest.TestCase):
    def test_letter(self):
        self.assertEqual(char_class('a'), "letter")
        self.assertEqual(char_class('Z'), "letter")

    def test_digit(self):
        self.assertEqual(char_class('0'), "digit")

    def test_whitespace(self):
        self.assertEqual(char_class(' '), "whitespace")
        self.assertEqual(char_class('\t'), "whitespace")

    def test_newline(self):
        self.assertEqual(char_class('\n'), "newline")

    def test_punctuation(self):
        self.assertEqual(char_class('.'), "punctuation")
        self.assertEqual(char_class(','), "punctuation")


class TestMathTracking(unittest.TestCase):
    def test_inline_math(self):
        text = "abc $x$ def"
        in_math = compute_in_math_array(text)
        self.assertFalse(in_math[0])  # 'a'
        self.assertTrue(in_math[4])   # '$'
        self.assertTrue(in_math[5])   # 'x'
        self.assertTrue(in_math[6])   # '$'
        self.assertFalse(in_math[8])  # 'd'

    def test_no_math(self):
        text = "hello world"
        in_math = compute_in_math_array(text)
        self.assertTrue(all(not m for m in in_math))


class TestLineFeatures(unittest.TestCase):
    def test_single_line(self):
        feats = compute_line_features("hello")
        self.assertEqual(len(feats), 5)
        self.assertEqual(feats[0]["line_idx"], 0)
        self.assertEqual(feats[0]["line_length"], 5)
        self.assertEqual(feats[2]["pos_in_line"], 2)

    def test_indented_line(self):
        feats = compute_line_features("  hello")
        self.assertEqual(feats[0]["leading_whitespace"], 2)


class TestNgrams(unittest.TestCase):
    def test_middle_position(self):
        feats = extract_ngram_features("abcde", 2)
        self.assertEqual(feats["unigram"], "c")
        self.assertEqual(feats["trigram"], "bcd")


class TestFeatureExtraction(unittest.TestCase):
    def test_basic(self):
        features = extract_features_for_document("hello")
        self.assertEqual(len(features), 5)
        self.assertEqual(features[0]["char"], "h")
        self.assertEqual(features[0]["char_class"], "letter")
        self.assertFalse(features[0]["in_math"])

    def test_empty(self):
        features = extract_features_for_document("")
        self.assertEqual(len(features), 0)


if __name__ == "__main__":
    unittest.main()
