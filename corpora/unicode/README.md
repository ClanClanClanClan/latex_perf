# `corpora/unicode` — fixtures for the REQUIRED `unicode-smoke` check

Fourteen minimal documents, one per Unicode defect class, plus a pure-ASCII
negative control. They are the input to `scripts/smoke_rules_unicode.sh`, driven
by `specs/rules/unicode_golden.yaml`, which is what the required `unicode-smoke`
status check runs.

**Why they exist.** `specs/rules/unicode_golden.yaml` was deleted on 2026-02-16
(`f24fc191`), and its last tracked content was a bare `cases:` with no entries —
so the check was vacuous before the deletion and took its `SKIP … exit 0` branch
for 185 days after it. Twenty CHAR/ENC/CJK/SPC/TYPO rule IDs had no regression
coverage at all while a required check reported green.

**Design rules for anything added here.**

- One defect class per file, wrapped in a minimal `article` document. Keep the
  prose free of anything that trips an unrelated rule — the CJK fixture
  deliberately avoids the *word* "CJK" so the acronym rule stays quiet, and the
  leader fixture avoids `\dots` so the spacing rule stays quiet.
- Every expectation in the golden must be **observed** against the running
  service in the `pilot` profile, never predicted.
- Prefer a `forbid` list that asserts confusable families do not bleed into each
  other (the three invisible-character rules; the four symbol rules). That half
  catches over-firing, which `expect` alone cannot.
- `clean_ascii_control.tex` must stay pure ASCII and must forbid every ID the
  other fixtures expect. It is the over-rejection guard; do not weaken it.
- Never encode a finding you believe is wrong. Two known gaps are documented at
  the head of the golden rather than asserted — `TYPO-043` fires outside
  verbatim despite its title, and `ENC-003` did not fire on U+2018/2019/201C/201D.
