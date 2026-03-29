#!/usr/bin/env python3
"""Per-character parser-state annotations for LaTeX documents.

Computes annotations for each character position:
  - in_math: inside $...$, $$...$$, \\(...\\), \\[...\\], or math environments
  - in_verbatim: inside \\begin{verbatim}...\\end{verbatim} or \\verb|...|
  - in_comment: after % to end-of-line (not \\%)
  - env_depth: \\begin{...}/\\end{...} nesting depth (int)

These are used as oracle features for the diagnostic experiment (v1.5)
and as explicit input features for the candidate classifier (v2).

Usage:
    from ml.data.parser_state import compute_parser_state
    state = compute_parser_state(text)
    state.in_math[42]      # True if char 42 is inside math mode
    state.in_verbatim[42]  # True if char 42 is inside verbatim
"""

import re
from dataclasses import dataclass
from typing import List, Tuple

from ml.data.label_spans import find_math_segments


# Named math environments not covered by find_math_segments()
# (which only handles $, $$, \(, \[).
_MATH_ENV_NAMES = [
    'equation', r'equation\*',
    'align', r'align\*',
    'gather', r'gather\*',
    'multline', r'multline\*',
    'flalign', r'flalign\*',
    'alignat', r'alignat\*',
    'eqnarray', r'eqnarray\*',
    'math', 'displaymath',
    'split',  # only inside other envs, but safe to mark as math
]


@dataclass
class ParserState:
    """Per-character parser-state annotations."""
    in_math: List[bool]
    in_verbatim: List[bool]
    in_comment: List[bool]
    env_depth: List[int]

    def __len__(self):
        return len(self.in_math)


def _find_verbatim_segments(text: str) -> List[Tuple[int, int]]:
    r"""Find all verbatim segments in text.

    Handles:
      - \begin{verbatim}...\end{verbatim}
      - \begin{verbatim*}...\end{verbatim*}
      - \begin{lstlisting}...\end{lstlisting}
      - \begin{minted}...\end{minted}  (with optional args)
      - \verb|...|  (any single delimiter char)

    Returns list of (start, end) character offsets.
    """
    segments = []

    # Block verbatim environments
    env_names = ['verbatim', r'verbatim\*', 'lstlisting', 'minted']
    for env in env_names:
        # Match \begin{env}...\end{env} (possibly with optional args after \begin)
        pat = re.compile(
            r'\\begin\{' + env + r'\}.*?\\end\{' + env.replace(r'\*', '*') + r'\}',
            re.DOTALL,
        )
        for m in pat.finditer(text):
            segments.append((m.start(), m.end()))

    # Inline \verb: \verb<delim>...<delim>
    # The delimiter is the character immediately after \verb (any non-letter)
    n = len(text)
    i = 0
    while i < n - 5:
        if text[i:i+5] == '\\verb' and i + 5 < n and not text[i+5].isalpha():
            delim = text[i + 5]
            j = text.find(delim, i + 6)
            if j != -1:
                segments.append((i, j + 1))
                i = j + 1
                continue
        i += 1

    return segments


def _find_comment_segments(text: str) -> List[Tuple[int, int]]:
    r"""Find all comment segments (% to end-of-line, excluding \%).

    Returns list of (start, end) character offsets.
    End is the position of the newline (exclusive), or len(text).
    """
    segments = []
    n = len(text)
    i = 0
    while i < n:
        if text[i] == '%':
            # Check for escaped percent: \%
            if i > 0 and text[i - 1] == '\\':
                # But \\% is a newline followed by %, so check for \\
                if i >= 2 and text[i - 2] == '\\':
                    pass  # \\% → comment starts
                else:
                    i += 1
                    continue  # \% → escaped, not a comment
            # Find end of line
            eol = text.find('\n', i)
            if eol == -1:
                eol = n
            segments.append((i, eol))
            i = eol + 1
        else:
            i += 1
    return segments


def _segments_to_mask(length: int, segments: List[Tuple[int, int]]) -> List[bool]:
    """Convert list of (start, end) segments to per-character boolean mask."""
    mask = [False] * length
    for start, end in segments:
        for i in range(max(0, start), min(end, length)):
            mask[i] = True
    return mask


def _find_named_math_segments(text: str) -> List[Tuple[int, int]]:
    r"""Find named math environments: \begin{equation}...\end{equation}, etc.

    Complements find_math_segments() which only handles $, $$, \(, \[.
    """
    segments = []
    for env in _MATH_ENV_NAMES:
        # env may contain \* for starred variants — keep as regex literal * match
        pat = re.compile(
            r'\\begin\{' + env + r'\}.*?\\end\{' + env + r'\}',
            re.DOTALL,
        )
        for m in pat.finditer(text):
            segments.append((m.start(), m.end()))
    return segments


def _compute_env_depth(text: str) -> List[int]:
    r"""Compute per-character \begin{...}/\end{...} nesting depth.

    Scans for \begin{...} (depth++) and \end{...} (depth--).
    Depth never goes below 0 (handles unmatched \end gracefully).
    """
    n = len(text)
    depth = [0] * n
    current = 0
    # Find all \begin{...} and \end{...} and sort by position
    begin_pat = re.compile(r'\\begin\{[^}]+\}')
    end_pat = re.compile(r'\\end\{[^}]+\}')

    events: List[Tuple[int, int, int]] = []  # (pos, end_pos, delta)
    for m in begin_pat.finditer(text):
        events.append((m.start(), m.end(), +1))
    for m in end_pat.finditer(text):
        events.append((m.start(), m.end(), -1))
    events.sort()

    current = 0
    prev_pos = 0
    for pos, end_pos, delta in events:
        # Fill from prev_pos to pos with current depth
        for i in range(prev_pos, min(pos, n)):
            depth[i] = current
        # The \begin{...} or \end{...} token itself gets the NEW depth
        if delta > 0:
            current += 1
        else:
            current = max(0, current - 1)
        for i in range(pos, min(end_pos, n)):
            depth[i] = current
        prev_pos = end_pos
    # Fill remaining
    for i in range(prev_pos, n):
        depth[i] = current
    return depth


def compute_parser_state(text: str) -> ParserState:
    """Compute per-character parser-state annotations for a LaTeX document.

    Returns ParserState with per-character annotations of len(text):
      - in_math: inside math mode ($, $$, \\(, \\[, equation, align, etc.)
      - in_verbatim: inside verbatim/lstlisting/minted/\\verb
      - in_comment: after % to end-of-line
      - env_depth: \\begin/\\end nesting depth (int)
    """
    n = len(text)

    # Compute segments
    math_segs = find_math_segments(text)  # $, $$, \(, \[
    named_math_segs = _find_named_math_segments(text)  # equation, align, etc.
    verb_segs = _find_verbatim_segments(text)
    comment_segs = _find_comment_segments(text)

    # Convert to masks
    in_math = _segments_to_mask(n, math_segs + named_math_segs)
    in_verbatim = _segments_to_mask(n, verb_segs)
    in_comment = _segments_to_mask(n, comment_segs)
    env_depth = _compute_env_depth(text)

    return ParserState(
        in_math=in_math,
        in_verbatim=in_verbatim,
        in_comment=in_comment,
        env_depth=env_depth,
    )


def parser_state_for_window(
    doc_state: ParserState,
    window_start: int,
    window_end: int,
) -> ParserState:
    """Extract parser state for a character window within a document."""
    return ParserState(
        in_math=doc_state.in_math[window_start:window_end],
        in_verbatim=doc_state.in_verbatim[window_start:window_end],
        in_comment=doc_state.in_comment[window_start:window_end],
        env_depth=doc_state.env_depth[window_start:window_end],
    )
