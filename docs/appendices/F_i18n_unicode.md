# Appendix F — Internationalisation & Unicode Strategy

Per v25 master plan §15, Table F (97 pages).

## F.1 Language Support Matrix

| ISO 639-1 | Language | Pack Status | Validators | Notes |
|-----------|----------|-------------|------------|-------|
| en | English | Live | 37 | Primary language |
| fr | French | Live | 12 | Guillemets, spacing |
| de | German | Live | 8 | Eszett, quotation |
| es | Spanish | Live | 6 | Inverted punctuation |
| ja | Japanese | Live | 5 | CJK + ruby |
| zh | Chinese | Live | 5 | CJK + punctuation |
| ar | Arabic | Live | 4 | RTL + diacritics |
| pt | Portuguese | Stubbed | — | — |
| it | Italian | Stubbed | — | — |
| nl | Dutch | Stubbed | — | — |
| ru | Russian | Stubbed | — | — |
| ko | Korean | Stubbed | — | — |
| pl | Polish | Stubbed | — | — |
| sv | Swedish | Stubbed | — | — |
| tr | Turkish | Stubbed | — | — |
| vi | Vietnamese | Stubbed | — | — |
| uk | Ukrainian | Stubbed | — | — |
| th | Thai | Stubbed | — | — |
| cs | Czech | Stubbed | — | — |
| ro | Romanian | Stubbed | — | — |
| el | Greek | Stubbed | — | — |

**Target**: 21 languages by v25 GA (Week 156).

## F.2 Language Detection (`language_detect.ml`)

**Algorithm**: Heuristic detection from LaTeX preamble:

1. Check `\usepackage[lang]{babel}` — 65-language babel→ISO mapping
2. Check `\usepackage{polyglossia}` + `\setmainlanguage{...}`
3. Check CJK package usage (`CJKutf8`, `xeCJK`, `luatexja`)
4. Fallback: `"en"` (English)

**Known limitation**: CJK in comments can trigger heuristic detection (documented in tests).

## F.3 Unicode Text Segmentation (`unicode_split.ml`)

**Library**: Uutf (already a dependency).

### F.3.1 Character Classification

```ocaml
type uchar_category =
  | Letter      (* Latin, Greek, Cyrillic *)
  | Digit       (* 0-9, Arabic-Indic *)
  | Whitespace  (* space, tab, newline, NBSP, ideographic space *)
  | Punctuation (* ASCII punct, CJK symbols, fullwidth punct *)
  | CJK         (* Unified Ideographs, Hiragana, Katakana *)
  | Arabic      (* Arabic script + supplements *)
  | Other
```

### F.3.2 Word Segmentation

- **Latin/Greek/Cyrillic/Arabic**: Word = consecutive letters (break on whitespace/punctuation)
- **CJK**: Each character = its own word (no whitespace word boundaries in CJK)
- **Mixed**: Transitions between scripts create word boundaries

### F.3.3 Sentence Segmentation

Sentence terminators: `.` (U+002E), `!` (U+0021), `?` (U+003F), `。` (U+3002), `！` (U+FF01), `？` (U+FF1F), `۔` (U+06D4)

Boundary: terminator followed by whitespace.

### F.3.4 Proof

`proofs/SplitPreservesOrder.v` — sorted segments have strictly increasing start positions; total content length distributes over append.

## F.4 L0 Tokenizer UTF-8 Support

`tokenizer_lite.ml` handles multi-byte UTF-8:

- ASCII bytes (< 0x80): fast path via `is_letter`
- Lead bytes (≥ 0x80): decode full codepoint via `decode_uchar_at`
- Letter codepoints: accumulate into `Word` token (mixed ASCII+accented in one token)
- CJK codepoints: individual `Word` per character
- Other: `Symbol` token

**Invariant**: Command names (`\cmd`) remain ASCII-only — correct per LaTeX spec.

## F.5 Per-Language Rule Gating

Rules can be tagged with ISO 639-1 codes in `rules_v3.yaml`:

```yaml
- id: LANG-003
  languages: ["fr", "de"]
  message: "Wrong quotation style"
```

`run_all_for_language` dispatcher: auto-detects language or accepts explicit parameter. Rules with empty `languages` list are universal.

## F.6 CJK-Specific Rules

| Rule ID | Description |
|---------|-------------|
| CJK-001 | Missing CJK font package |
| CJK-003 | Incorrect CJK punctuation spacing |
| CJK-009 | CJK text in math mode |
| CJK-011 | Mixed CJK/Latin without proper spacing |
| CJK-013 | Ruby annotation syntax error |

## F.7 RTL-Specific Rules

| Rule ID | Description |
|---------|-------------|
| RTL-001 | Missing bidi package for RTL text |
| RTL-002 | Incorrect RTL/LTR boundary markers |

## F.8 Corpus Strategy

**Golden corpus**: 12 YAML suites, 329 test cases across 6 language packs (en, fr, de, es, ja, zh).

**External corpora**: Locked via `corpora.lock` (SHA-256 + URL). CI job `fetch_corpora` retrieves them.

## F.9 Unicode Scope

**In scope for v25**:
- UTF-8 encoding detection and validation
- NFC normalisation awareness (detect non-NFC input)
- Unicode letter classification for tokenization
- CJK/Arabic/RTL script detection

**Out of scope for v25** (per spec):
- Full Unicode equivalence beyond NFC
- Unicode collation
- Complex text layout (ligatures, contextual shaping)
- Emoji handling
