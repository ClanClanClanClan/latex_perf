# Adversarial UTF-8 / offset-misalignment regression corpus

`cjk_offset_torture.tex` is a **permanent regression fixture** for the fix-output
corruption class first found in STYLE-033 (v27.1.8): a fix producer that derives
its `Cst_edit` byte offsets from a **length-changing** transform of the source
(`strip_comments`, `strip_math_segments`) and emits them against the *original*
string — landing edits mid-multibyte-character once an earlier comment/math span
has shrunk the text, producing invalid UTF-8.

The file deliberately interleaves multibyte CJK glyphs with:
- `%`-comment lines that contain CJK *after* the `%` (shifts `strip_comments` offsets),
- inline and display `$…$` math containing CJK (shifts `strip_math_segments` offsets),
- a wide spread of common producer triggers (mid-text `%`, double space after
  period, space before `\cite`/`;`/`:`, `~~`, bare `&`, straight quotes, en/em
  dashes, fullwidth punctuation, `=>`/`\times`/`\div`, …),

so that any producer using the unsafe offset pattern lands an edit inside a CJK
character. `scripts/tools/check_apply_fixes_safety.py` scans `corpora/lint/**`,
iterates `--apply-fixes` to a fixpoint, and fails if the output is not valid
UTF-8 — so this fixture turns that gate into a standing guard for the whole
producer set. (Verified: simulating the pre-fix STYLE-033 logic against this file
yields invalid UTF-8 at byte 312.)

All 120 producers were audited clean for this class in v27.1.8/v27.1.9; the safe
patterns are: match the **original** source for edit offsets, filter via
`find_math_ranges`/`find_exempt_ranges`, and skip multibyte sequences in byte
scans. See the `fix_output_safety` memory note.
