# Corpus licensing + curation (v26.2)

v26.2 introduces 3 new corpus directories; this doc governs their
licensing and curation.

## New corpora

- `corpora/compile_contract/` — 5+ sample projects for PR A2 testing
  (simple, multi-file, with-bib, with-missing-ref, with-cycle)
- `corpora/roundtrip/` — 100+ files for CST round-trip testing (PR B2)
- `corpora/regression/` — subset of existing corpus for v26.1 vs v26.2
  differential testing (PR C)

## Licensing policy

All new corpus files MUST be one of:
1. **Synthetic** — authored by us specifically for testing, no external
   source. Commit with an `AUTHORS` comment at top identifying this.
2. **Public-domain LaTeX examples** — classical distribution (e.g.
   TeX sample documents, TUGboat articles pre-1990, anything marked
   Public Domain). Credit the original author.
3. **Permissively-licensed** (MIT, Apache, CC-BY, CC-BY-SA) — add
   `.LICENSE` next to the file.
4. **Author-donated** — explicit grant from a user/academic. Preserve
   their email in the corpus file's header and an entry in
   `corpora/AUTHORS.md`.

**NEVER include:**
- GPL'd LaTeX files (incompatible with our MIT licensing).
- Third-party papers without the author's explicit permission.
- Files scraped from arXiv / journal websites without verified license.

## Curation process

1. Author / identify source.
2. Verify licensing.
3. Scrub sensitive content (author names if donor requested, institution
   details if flagged).
4. Ensure file is in scope of current CST subset (§2.6 of plan). If
   out of scope, file it under `corpora/out_of_scope/` with a note.
5. Commit with a descriptive path (`corpora/roundtrip/math_heavy.tex`
   not `corpora/roundtrip/file_042.tex`).
6. Add to corresponding test's input list.

## Corpus manifest

`corpora/MANIFEST.md` lists every file with its licensing, source,
and purpose. PR A2 / B2 / C each append relevant entries.

Template row:
```markdown
## corpora/roundtrip/math_heavy.tex
- License: CC-BY 4.0
- Source: TUGboat 2012, issue 3, article by Jane Doe (donated 2026-04-15)
- Purpose: exercises math environments (align, gather, matrix)
- In subset: yes
```

## Fixture hygiene

- Keep files under 100KB each (corpus test runtime budget).
- Total corpus under 20MB (cloneable on slow connections).
- UTF-8 encoding; no BOMs; no mixed encodings.
- Normalize line endings to LF at commit time (`.gitattributes` enforces).

## Auditing

- PR A2: verify new files have MANIFEST entries.
- PR B2: verify new files are in CST subset OR flagged out-of-scope.
- PR C: verify differential-test corpus is a strict subset of
  `corpora/regression/` (no new files between v26.1 and v26.2 corpora
  for this specific comparison).
