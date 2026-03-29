# Pilot L0 Validators — TODO

Scope: Implement and validate pilot L0 lexical rules in runtime (now 20 rules).

Rule IDs (current)
- TYPO-001 — ASCII straight quotes → curly (Error)
- TYPO-002 — Double hyphen → en-dash (Warning)
- TYPO-003 — Triple hyphen → em-dash (Warning)
- TYPO-004 — TeX ``…'' quotes → curly (Warning)
- TYPO-005 — Ellipsis ... → \\dots (Warning)
- TYPO-006 — Tab U+0009 forbidden (Error)
- TYPO-007 — Trailing spaces at EOL (Info→Warning)
- TYPO-008 — >2 consecutive blank lines (Info→Warning)
- TYPO-009 — ~ at line start (Warning)
- TYPO-010 — Space before punctuation (Info→Warning)
- TYPO-011 — Multiple consecutive spaces in text (Info→Warning)
- TYPO-012 — Space before closing bracket ) ] } (Warning)
- TYPO-013 — Non‑breaking space after single‑letter words (Info→Warning)
- TYPO-014 — Inconsistent quotation mark style (Warning)
- TYPO-015 — LaTeX command spacing may need adjustment (Info→Warning)
- TYPO-016 — Excessive exclamation marks (Info→Warning)
- TYPO-017 — Excessive question marks (Info→Warning)
- TYPO-018 — Double space after sentence punctuation (Warning)
- TYPO-019 — Leading spaces at start of line (Info→Warning)
- TYPO-020 — Consecutive commas (Warning)

Tasks
- [x] Golden inputs for each rule in `corpora/lint/pilot_v1/`
- [x] REST smoke for each rule (enable with `L0_VALIDATORS=pilot`)
- [x] Latency smoke on `/expand` with acceptance gate
- [ ] FP review with small real-world corpus
- [ ] Perf smoke (full-doc + 4 KB window) with pilot enabled
- [x] Document caveats (e.g., Info mapped to Warning in runtime for now)

Notes
- Runtime implementation is string-level; token-aware variants will follow post L0 tokenizer rewire.
- Keep feature-flagged via `L0_VALIDATORS` until post-pilot gate.
