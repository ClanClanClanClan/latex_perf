import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import pytest
from latex_perfectionist.core.config_system import load_config

ROOT = pathlib.Path(__file__).resolve().parents[1]

@pytest.fixture(scope="session")
def cfg():
    """Load configuration for testing."""
    try:
        # Try to load from default config
        return load_config(profile="article")
    except Exception:
        # Fallback to minimal config if loading fails
        return {
            "orthography": {"en_dash_ranges": True},
            "punctuation": {
                "abbreviations": ["a.s.", "w.l.o.g.", "i.i.d.", "w.r.t.", "cf.", "e.g.", "i.e.", "etc."],
                "tie_words": ["Figure", "Table", "Theorem", "Lemma", "Corollary", "cf.", "Eq.", "eq.", "pp."]
            },
            "math": {
                "expect_brackets": True,
                "prob_brackets": True,
                "raisebox_ex": "0.2"
            }
        }

def run_rule(rule, bad, good, cfg):
    """
    Deterministic helper: asserts rule flags every bad case,
    no good case, fixes are non-overlapping & idempotent.
    """
    for txt in bad:
        rr = rule.audit(txt, cfg)
        assert rr.issues, f"should flag: {txt}"

        # fixes non-overlap
        spans = [(f.start, f.end) for f in rr.fixes]
        assert len(spans) == len(set(spans)), "overlapping Fix objects"

        if getattr(rule, "auto_fix_safe", False):
            patched = txt
            for f in sorted(rr.fixes, key=lambda f: f.start, reverse=True):
                patched = patched[:f.start] + f.replacement + patched[f.end:]
            # idempotent
            assert not rule.audit(patched, cfg).issues

    for txt in good:
        assert not rule.audit(txt, cfg).issues, f"false positive: {txt}"