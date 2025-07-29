"""Shared generators for Hypothesis tests."""
from hypothesis import strategies as st

# random whitespace (incl. 0 chars)
ws    = st.from_regex(r"[ \t]{0,3}")
digits = st.text("0123456789", min_size=1, max_size=3)