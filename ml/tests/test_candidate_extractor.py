#!/usr/bin/env python3
"""Comprehensive test suite for the v2 candidate extractor.

Tests cover: set invariants, recall guarantees, per-rule regression,
label assignment, and edge cases (unicode, overlap, performance).
"""

import json
import time
import unittest
from typing import Dict, List, Set

from ml.data.candidate_extractor import (
    ALL_V2_RULES,
    AMBIGUOUS_RULES,
    DETERMINISTIC_RULES,
    Candidate,
    classify_rules,
    extract_all_candidates,
    extract_candidates,
    label_candidates,
)
from ml.data.label_spans import Span, replay_pattern

VPD_PATH = "specs/rules/vpd_patterns.json"


class TestBase(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(VPD_PATH) as f:
            cls.vpd: Dict = json.load(f)


# ═══════════════════════════════════════════════════════════════════════════════
# 1. Core invariant tests
# ═══════════════════════════════════════════════════════════════════════════════


class TestRuleSets(TestBase):
    """Verify the rule partition is correct and consistent."""

    def test_deterministic_rules_set(self):
        """DETERMINISTIC_RULES has exactly 8 members with the right IDs."""
        expected = {
            "TYPO-002", "TYPO-003", "TYPO-004", "TYPO-013",
            "TYPO-030", "TYPO-043", "TYPO-047", "TYPO-061",
        }
        self.assertEqual(DETERMINISTIC_RULES, expected)
        self.assertEqual(len(DETERMINISTIC_RULES), 8)

    def test_ambiguous_rules_set(self):
        """AMBIGUOUS_RULES has exactly 8 members with the right IDs."""
        expected = {
            "TYPO-001", "TYPO-005", "TYPO-012", "TYPO-028",
            "TYPO-048", "TYPO-052", "TYPO-056", "TYPO-062",
        }
        self.assertEqual(AMBIGUOUS_RULES, expected)
        self.assertEqual(len(AMBIGUOUS_RULES), 8)

    def test_no_overlap(self):
        """DETERMINISTIC_RULES and AMBIGUOUS_RULES must be disjoint."""
        overlap = DETERMINISTIC_RULES & AMBIGUOUS_RULES
        self.assertEqual(overlap, set(), f"Overlap found: {overlap}")

    def test_all_v2_is_union(self):
        """ALL_V2_RULES == DETERMINISTIC_RULES | AMBIGUOUS_RULES."""
        self.assertEqual(ALL_V2_RULES, DETERMINISTIC_RULES | AMBIGUOUS_RULES)
        self.assertEqual(len(ALL_V2_RULES), 16)

    def test_classify_rules_returns_same(self):
        """classify_rules() utility returns the canonical sets."""
        det, amb = classify_rules()
        self.assertIs(det, DETERMINISTIC_RULES)
        self.assertIs(amb, AMBIGUOUS_RULES)

    def test_all_rules_in_vpd(self):
        """Every v2 rule must have a pattern entry in vpd_patterns.json."""
        for rule_id in ALL_V2_RULES:
            self.assertIn(rule_id, self.vpd,
                          f"{rule_id} missing from vpd_patterns.json")
            self.assertIn("pattern", self.vpd[rule_id],
                          f"{rule_id} has no 'pattern' key")


# ═══════════════════════════════════════════════════════════════════════════════
# 2. Recall guarantee tests
# ═══════════════════════════════════════════════════════════════════════════════


class TestRecallGuaranteeDeterministic(TestBase):
    """For every deterministic rule, candidates must cover ALL gold spans.

    This is the foundational property of the v2 pipeline: if the candidate
    extractor misses a gold span, the pipeline has a structural false negative
    that no downstream classifier can recover.
    """

    # Texts designed to exercise each deterministic rule.
    RULE_TEXTS = {
        "TYPO-002": "en--dash and another--one here",
        "TYPO-003": "em---dash plus---two of them",
        "TYPO-004": "say ``hi'' and ``bye'' please",
        "TYPO-013": "a single `tick here and `another",
        "TYPO-030": "four----hyphens and----again",
        "TYPO-043": "\u201cSmart\u201d and \u2018single\u2019 curly",
        "TYPO-047": "\\section*{Intro} and \\section*{End}",
        "TYPO-061": "dimension 3\u00d75 matrix and 2\u00d72 block",
    }

    def test_recall_guarantee_all_deterministic(self):
        for rule_id in sorted(DETERMINISTIC_RULES):
            with self.subTest(rule_id=rule_id):
                text = self.RULE_TEXTS[rule_id]
                pattern_def = self.vpd[rule_id]["pattern"]
                gold_spans = replay_pattern(text, rule_id, pattern_def)
                self.assertGreater(len(gold_spans), 0,
                                   f"Test text for {rule_id} produced no gold spans")

                candidates = extract_candidates(text, rule_id, self.vpd)
                cand_spans = {(c.start, c.end) for c in candidates}

                for gs, ge in gold_spans:
                    self.assertIn((gs, ge), cand_spans,
                                  f"{rule_id}: gold span ({gs},{ge}) = "
                                  f"{text[gs:ge]!r} not in candidates")

    def test_recall_multi_occurrence_typo_004(self):
        """TYPO-004 with interleaved `` and '' in complex layout."""
        text = "A ``B'' C ``D'' E ``F''"
        gold = replay_pattern(text, "TYPO-004", self.vpd["TYPO-004"]["pattern"])
        cands = extract_candidates(text, "TYPO-004", self.vpd)
        cand_spans = {(c.start, c.end) for c in cands}
        for gs, ge in gold:
            self.assertIn((gs, ge), cand_spans)
        # Should have 6 candidates: 3 pairs of `` and ''
        self.assertEqual(len(cands), 6)

    def test_recall_typo_002_adjacent_hyphens(self):
        """-- inside longer hyphen runs still detected."""
        text = "a--b---c----d"
        gold = replay_pattern(text, "TYPO-002", self.vpd["TYPO-002"]["pattern"])
        cands = extract_candidates(text, "TYPO-002", self.vpd)
        cand_spans = {(c.start, c.end) for c in cands}
        for gs, ge in gold:
            self.assertIn((gs, ge), cand_spans)


class TestRecallGuaranteeAmbiguous(TestBase):
    """Ambiguous rules: candidates must cover both positive and negative sites."""

    RULE_TEXTS = {
        # TYPO-001: straight quotes -- violation in text, but also inside math
        "TYPO-001": 'She said "hello" and $x="y"$ done',
        # TYPO-005: ... ellipsis outside math, also inside
        "TYPO-005": "Wait... and $a...b$ more...",
        # TYPO-012: digit followed by ' (foot mark vs apostrophe)
        "TYPO-012": "He is 6'2\" tall and got 3's on tests",
        # TYPO-028: $$ display math
        "TYPO-028": "before $$x=1$$ and $$y=2$$ after",
        # TYPO-048: en-dash outside math
        "TYPO-048": "pages 1\u20132 and $a\u2013b$",
        # TYPO-052: angle brackets outside math
        "TYPO-052": "a<b>c and $x<y$",
        # TYPO-056: accent macros like \'{a}
        "TYPO-056": "caf\\'{e} and na\\\"ive",
        # TYPO-062: \\ not followed by [ or *
        "TYPO-062": "line1\\\\\nline2\\\\[5pt] and \\\\*",
    }

    def test_recall_guarantee_all_ambiguous(self):
        for rule_id in sorted(AMBIGUOUS_RULES):
            with self.subTest(rule_id=rule_id):
                text = self.RULE_TEXTS[rule_id]
                pattern_def = self.vpd[rule_id]["pattern"]
                gold_spans = replay_pattern(text, rule_id, pattern_def)

                candidates = extract_candidates(text, rule_id, self.vpd)
                cand_spans = {(c.start, c.end) for c in candidates}

                for gs, ge in gold_spans:
                    self.assertIn((gs, ge), cand_spans,
                                  f"{rule_id}: gold span ({gs},{ge}) = "
                                  f"{text[gs:ge]!r} not in candidates")


# ═══════════════════════════════════════════════════════════════════════════════
# 3. Per-rule regression tests
# ═══════════════════════════════════════════════════════════════════════════════


class TestPerRuleRegression(TestBase):
    """Hardcoded expected outputs for specific inputs."""

    def test_typo_001_straight_quotes(self):
        """'"hello"' -> 2 candidates at the quote positions."""
        text = '"hello"'
        cands = extract_candidates(text, "TYPO-001", self.vpd)
        starts = [c.start for c in cands]
        self.assertEqual(len(cands), 2, f"Expected 2, got {len(cands)}: {cands}")
        self.assertIn(0, starts)
        self.assertIn(6, starts)
        # Each candidate spans exactly 1 character
        for c in cands:
            self.assertEqual(c.end - c.start, 1)

    def test_typo_002_double_hyphen(self):
        """'a--b---c' -> candidates for -- (the --- also contains --)."""
        text = "a--b---c"
        cands = extract_candidates(text, "TYPO-002", self.vpd)
        # At minimum there's a -- at pos 1; --- at pos 4 contains overlapping --
        self.assertGreaterEqual(len(cands), 1)
        # The explicit -- at position 1 must be found
        found_pos1 = any(c.start == 1 and c.end == 3 for c in cands)
        self.assertTrue(found_pos1, f"No candidate at [1,3) in {cands}")

    def test_typo_003_triple_hyphen(self):
        """'a---b' -> 1 candidate for ---."""
        text = "a---b"
        cands = extract_candidates(text, "TYPO-003", self.vpd)
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0].start, 1)
        self.assertEqual(cands[0].end, 4)

    def test_typo_004_backticks(self):
        """'say ``hi'' please' -> candidates for `` and ''."""
        text = "say ``hi'' please"
        cands = extract_candidates(text, "TYPO-004", self.vpd)
        texts_found = [text[c.start:c.end] for c in cands]
        self.assertIn("``", texts_found)
        self.assertIn("''", texts_found)
        self.assertEqual(len(cands), 2)

    def test_typo_013_single_backtick(self):
        """'say `hi please' -> 1 candidate (single backtick, not double)."""
        text = "say `hi please"
        cands = extract_candidates(text, "TYPO-013", self.vpd)
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0].start, 4)
        self.assertEqual(cands[0].end, 5)

    def test_typo_013_excludes_double_backtick(self):
        """`` should NOT produce TYPO-013 candidates."""
        text = "say ``hi'' please"
        cands = extract_candidates(text, "TYPO-013", self.vpd)
        self.assertEqual(len(cands), 0,
                         f"Double backtick should not fire TYPO-013: {cands}")

    def test_typo_028_dollar_dollar(self):
        """'before $$x$$ after' -> 2 candidates (opening $$ and closing $$)."""
        text = "before $$x$$ after"
        cands = extract_candidates(text, "TYPO-028", self.vpd)
        self.assertEqual(len(cands), 2)
        texts_found = [text[c.start:c.end] for c in cands]
        self.assertTrue(all(t == "$$" for t in texts_found))
        self.assertEqual(cands[0].start, 7)
        self.assertEqual(cands[1].start, 10)

    def test_typo_030_four_hyphens(self):
        """'a----b' -> candidate for ----."""
        text = "a----b"
        cands = extract_candidates(text, "TYPO-030", self.vpd)
        self.assertGreaterEqual(len(cands), 1)
        found = any(c.start == 1 and c.end == 5 for c in cands)
        self.assertTrue(found, f"No candidate at [1,5) in {cands}")

    def test_typo_052_angle_brackets(self):
        """'a<b>c' outside math -> candidates for < and >."""
        text = "a<b>c"
        cands = extract_candidates(text, "TYPO-052", self.vpd)
        chars_found = {text[c.start:c.end] for c in cands}
        self.assertIn("<", chars_found)
        self.assertIn(">", chars_found)
        self.assertEqual(len(cands), 2)

    def test_typo_052_in_math(self):
        """'$a<b$' -> < is inside math, so no candidate."""
        text = "$a<b$"
        cands = extract_candidates(text, "TYPO-052", self.vpd)
        # < is inside math $...$, so strip_math_segments should remove it
        self.assertEqual(len(cands), 0,
                         f"< inside math should not produce candidates: {cands}")

    def test_typo_062_backslash(self):
        """'\\\\textbf{hi}' -> candidate for \\\\."""
        text = "\\\\textbf{hi}"
        cands = extract_candidates(text, "TYPO-062", self.vpd)
        # \\ followed by 't' (not [ or *) -> should fire
        self.assertGreaterEqual(len(cands), 1)
        found = any(c.start == 0 and c.end == 2 for c in cands)
        self.assertTrue(found, f"No candidate at [0,2) in {cands}")

    def test_typo_062_backslash_with_bracket_no_fire(self):
        """\\\\[ should NOT fire TYPO-062."""
        text = "\\\\[5pt]"
        cands = extract_candidates(text, "TYPO-062", self.vpd)
        self.assertEqual(len(cands), 0,
                         f"\\\\[ should not fire TYPO-062: {cands}")

    def test_typo_062_backslash_with_star_no_fire(self):
        """\\\\* should NOT fire TYPO-062."""
        text = "\\\\*"
        cands = extract_candidates(text, "TYPO-062", self.vpd)
        self.assertEqual(len(cands), 0,
                         f"\\\\* should not fire TYPO-062: {cands}")


# ═══════════════════════════════════════════════════════════════════════════════
# 4. Label assignment tests
# ═══════════════════════════════════════════════════════════════════════════════


class TestLabelCandidates(TestBase):
    """Verify label_candidates matches gold spans correctly."""

    def _make_candidates(self, rule_id: str, spans: List) -> List[Candidate]:
        return [Candidate(rule_id=rule_id, start=s, end=e) for s, e in spans]

    def test_label_candidates_positive_match(self):
        """Gold span matches candidate -> is_positive=True."""
        cands = self._make_candidates("TYPO-001", [(0, 1), (6, 7)])
        gold = [Span(start=0, end=1, rule_id="TYPO-001")]
        labeled = label_candidates(cands, gold)
        self.assertTrue(labeled[0].is_positive)
        self.assertFalse(labeled[1].is_positive)

    def test_label_candidates_negative(self):
        """Candidate not in gold -> is_positive=False."""
        cands = self._make_candidates("TYPO-001", [(0, 1), (5, 6)])
        gold = [Span(start=99, end=100, rule_id="TYPO-001")]
        labeled = label_candidates(cands, gold)
        self.assertFalse(labeled[0].is_positive)
        self.assertFalse(labeled[1].is_positive)

    def test_label_candidates_mixed(self):
        """Mix of positive and negative candidates."""
        cands = self._make_candidates("TYPO-002", [(1, 3), (5, 7), (10, 12)])
        gold = [
            Span(start=1, end=3, rule_id="TYPO-002"),
            Span(start=10, end=12, rule_id="TYPO-002"),
        ]
        labeled = label_candidates(cands, gold)
        self.assertTrue(labeled[0].is_positive)
        self.assertFalse(labeled[1].is_positive)
        self.assertTrue(labeled[2].is_positive)

    def test_label_candidates_dict_spans(self):
        """Gold spans as dicts (not Span objects)."""
        cands = self._make_candidates("TYPO-003", [(1, 4)])
        gold_dicts = [{"rule_id": "TYPO-003", "start": 1, "end": 4}]
        labeled = label_candidates(cands, gold_dicts)
        self.assertTrue(labeled[0].is_positive)

    def test_label_candidates_empty_gold(self):
        """No gold spans -> all candidates negative."""
        cands = self._make_candidates("TYPO-001", [(0, 1), (5, 6), (10, 11)])
        labeled = label_candidates(cands, [])
        for c in labeled:
            self.assertFalse(c.is_positive,
                             f"Candidate {c} should be negative with empty gold")

    def test_label_candidates_preserves_order(self):
        """Labeled list has same length and order as input."""
        cands = self._make_candidates("TYPO-002", [(3, 5), (0, 2), (8, 10)])
        gold = [Span(start=0, end=2, rule_id="TYPO-002")]
        labeled = label_candidates(cands, gold)
        self.assertEqual(len(labeled), len(cands))
        for orig, lab in zip(cands, labeled):
            self.assertEqual(orig.start, lab.start)
            self.assertEqual(orig.end, lab.end)
            self.assertEqual(orig.rule_id, lab.rule_id)

    def test_label_candidates_wrong_rule_id_no_match(self):
        """Gold span for different rule_id does NOT label candidate positive."""
        cands = self._make_candidates("TYPO-001", [(0, 1)])
        gold = [Span(start=0, end=1, rule_id="TYPO-002")]
        labeled = label_candidates(cands, gold)
        self.assertFalse(labeled[0].is_positive)

    def test_label_candidates_exact_boundary_required(self):
        """Off-by-one in start or end should not match."""
        cands = self._make_candidates("TYPO-001", [(5, 6)])
        # Same rule, overlapping but not exact
        gold = [
            Span(start=4, end=6, rule_id="TYPO-001"),
            Span(start=5, end=7, rule_id="TYPO-001"),
            Span(start=4, end=5, rule_id="TYPO-001"),
        ]
        labeled = label_candidates(cands, gold)
        self.assertFalse(labeled[0].is_positive,
                         "Off-by-one spans should not match")


# ═══════════════════════════════════════════════════════════════════════════════
# 5. Edge cases
# ═══════════════════════════════════════════════════════════════════════════════


class TestEdgeCases(TestBase):
    """Tricky inputs: empty, Unicode, long, overlapping, etc."""

    def test_empty_text(self):
        """Empty string -> zero candidates for every rule."""
        for rule_id in sorted(ALL_V2_RULES):
            with self.subTest(rule_id=rule_id):
                cands = extract_candidates("", rule_id, self.vpd)
                self.assertEqual(len(cands), 0,
                                 f"{rule_id} produced candidates on empty text")

    def test_no_matching_rules(self):
        """Text with no violations of any active rule -> zero candidates."""
        clean_text = "This is perfectly clean LaTeX with no violations."
        cands = extract_all_candidates(clean_text, self.vpd)
        self.assertEqual(len(cands), 0,
                         f"Clean text produced {len(cands)} candidates: "
                         f"{[(c.rule_id, clean_text[c.start:c.end]) for c in cands[:5]]}")

    def test_overlapping_candidates_different_rules(self):
        """Text where multiple rules fire at overlapping positions."""
        # -- triggers TYPO-002; --- triggers TYPO-003; ---- triggers TYPO-030
        text = "a----b"
        all_cands = extract_all_candidates(text, self.vpd,
                                           rules={"TYPO-002", "TYPO-003", "TYPO-030"})
        rules_seen = {c.rule_id for c in all_cands}
        # All three rules should find something in this text
        self.assertIn("TYPO-030", rules_seen)
        # Verify candidates from different rules can overlap
        positions = [(c.rule_id, c.start, c.end) for c in all_cands]
        self.assertGreater(len(positions), 1,
                           f"Expected overlapping candidates, got {positions}")

    def test_very_long_text(self):
        """10KB document doesn't crash and runs in reasonable time."""
        # Build a 10KB text with scattered violations
        chunk = 'Normal text here. "quote" and a--dash. '
        text = chunk * (10240 // len(chunk) + 1)
        self.assertGreater(len(text), 10000)

        start_time = time.monotonic()
        cands = extract_all_candidates(text, self.vpd)
        elapsed = time.monotonic() - start_time

        self.assertGreater(len(cands), 0, "10KB text with violations should have candidates")
        self.assertLess(elapsed, 10.0, f"Took {elapsed:.2f}s on 10KB text -- too slow")

    def test_unicode_text(self):
        """LaTeX with Unicode characters (accents, CJK) doesn't crash."""
        text = (
            "R\u00e9sum\u00e9 with caf\u00e9. "
            "\u4e16\u754c\u4f60\u597d. "
            "\u00fcber and \u00f1o\u00f1o. "
            "Normal text here."
        )
        # Should not raise
        cands = extract_all_candidates(text, self.vpd)
        # No violations expected in this text
        # (no --, no ``, no $$, etc.)
        self.assertIsInstance(cands, list)

    def test_unicode_multiplication_sign(self):
        """TYPO-061 fires on Unicode multiplication sign outside math."""
        text = "a 3\u00d74 matrix"
        cands = extract_candidates(text, "TYPO-061", self.vpd)
        self.assertGreaterEqual(len(cands), 1)

    def test_candidate_offsets_valid(self):
        """All (start, end) satisfy 0 <= start < end <= len(text)."""
        text = 'He said "hello" and she--replied ``ok'' $a<b$ $$x$$'
        cands = extract_all_candidates(text, self.vpd)
        for c in cands:
            self.assertGreaterEqual(c.start, 0,
                                    f"Negative start: {c}")
            self.assertGreater(c.end, c.start,
                               f"end <= start: {c}")
            self.assertLessEqual(c.end, len(text),
                                 f"end > len(text): {c}")

    def test_no_duplicate_candidates(self):
        """No (rule_id, start, end) appears twice."""
        text = 'a--b "c" d---e ``f'' $$g$$ h<i>j'
        cands = extract_all_candidates(text, self.vpd)
        seen = set()
        for c in cands:
            key = (c.rule_id, c.start, c.end)
            self.assertNotIn(key, seen,
                             f"Duplicate candidate: {key}")
            seen.add(key)

    def test_extract_all_with_rule_filter(self):
        """Only specified rules produce candidates."""
        text = 'a--b "c" d---e'
        subset = {"TYPO-002"}
        cands = extract_all_candidates(text, self.vpd, rules=subset)
        for c in cands:
            self.assertEqual(c.rule_id, "TYPO-002",
                             f"Unexpected rule {c.rule_id} with filter {subset}")
        # Same text with only TYPO-003 should give different results
        cands_003 = extract_all_candidates(text, self.vpd, rules={"TYPO-003"})
        for c in cands_003:
            self.assertEqual(c.rule_id, "TYPO-003")

    def test_extract_all_default_uses_all_v2(self):
        """Default (rules=None) uses ALL_V2_RULES."""
        text = 'a--b "c"'
        cands = extract_all_candidates(text, self.vpd)
        rules_seen = {c.rule_id for c in cands}
        # At least TYPO-002 (--) and TYPO-001 (") should appear
        self.assertIn("TYPO-002", rules_seen)
        self.assertIn("TYPO-001", rules_seen)

    def test_extract_all_sorted_by_start_then_rule(self):
        """extract_all_candidates returns sorted by (start, rule_id)."""
        text = 'a--b---c "d"'
        cands = extract_all_candidates(text, self.vpd)
        for i in range(1, len(cands)):
            prev = (cands[i - 1].start, cands[i - 1].rule_id)
            curr = (cands[i].start, cands[i].rule_id)
            self.assertLessEqual(prev, curr,
                                 f"Not sorted: {prev} > {curr}")

    def test_candidate_immutability(self):
        """Candidate is frozen -- attribute assignment should raise."""
        c = Candidate(rule_id="TYPO-001", start=0, end=1)
        with self.assertRaises(AttributeError):
            c.start = 5  # type: ignore[misc]

    def test_candidate_invalid_span_raises(self):
        """Candidate with start > end or negative start raises ValueError."""
        with self.assertRaises(ValueError):
            Candidate(rule_id="TYPO-001", start=5, end=3)
        with self.assertRaises(ValueError):
            Candidate(rule_id="TYPO-001", start=-1, end=2)

    def test_missing_rule_in_vpd_skipped(self):
        """extract_all_candidates skips rules not in vpd_patterns."""
        fake_rules = {"TYPO-999"}
        cands = extract_all_candidates("some text", self.vpd, rules=fake_rules)
        self.assertEqual(len(cands), 0)

    def test_single_char_text(self):
        """Single character texts don't crash."""
        for ch in ['"', '-', '`', '$', '<', '\\', '\u00d7', '\u2013']:
            with self.subTest(ch=repr(ch)):
                cands = extract_all_candidates(ch, self.vpd)
                self.assertIsInstance(cands, list)

    def test_all_candidates_is_positive_defaults_false(self):
        """Freshly extracted candidates have is_positive=False."""
        text = 'a--b "c"'
        cands = extract_all_candidates(text, self.vpd)
        for c in cands:
            self.assertFalse(c.is_positive,
                             f"Freshly extracted candidate should not be positive: {c}")

    def test_consecutive_violations_same_rule(self):
        """Multiple adjacent violations of the same rule are individually tracked."""
        # Three consecutive ``...'' pairs
        text = "``a'' ``b'' ``c''"
        cands = extract_candidates(text, "TYPO-004", self.vpd)
        self.assertEqual(len(cands), 6,
                         f"Expected 6 candidates (3x`` + 3x''), got {len(cands)}: {cands}")

    def test_typo_052_mixed_math_and_text(self):
        """Angle brackets in math suppressed, in text not."""
        text = "a<b and $x<y$ and c>d"
        cands = extract_candidates(text, "TYPO-052", self.vpd)
        # Only the text-mode < at pos 1 and > at pos 20 should fire
        for c in cands:
            snippet = text[c.start:c.end]
            self.assertIn(snippet, {"<", ">"})
        # Verify no candidate falls inside the math region
        # Math is at positions 10..14 ($x<y$)
        for c in cands:
            self.assertFalse(10 <= c.start < 14,
                             f"Candidate inside math: {c}")

    def test_typo_062_at_end_of_text(self):
        """\\\\ at the very end of text (no character after) should fire."""
        text = "end\\\\"
        cands = extract_candidates(text, "TYPO-062", self.vpd)
        self.assertGreaterEqual(len(cands), 1,
                                f"\\\\ at end-of-text should fire TYPO-062")

    def test_typo_028_nested_dollar(self):
        """Ensure $$ is found even with surrounding single $."""
        text = "a $x$ b $$y$$ c $z$"
        cands = extract_candidates(text, "TYPO-028", self.vpd)
        self.assertEqual(len(cands), 2)
        for c in cands:
            self.assertEqual(text[c.start:c.end], "$$")

    def test_typo_001_no_candidates_in_math(self):
        """Straight quotes inside math should not produce TYPO-001 candidates."""
        text = '$x = "y"$'
        cands = extract_candidates(text, "TYPO-001", self.vpd)
        self.assertEqual(len(cands), 0,
                         f"Quotes in math should be suppressed: {cands}")


if __name__ == "__main__":
    unittest.main()
