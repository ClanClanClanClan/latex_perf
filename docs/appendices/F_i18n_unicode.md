# Appendix F -- Internationalisation & Unicode Strategy

Revision 2026-04-05. Authoritative policy for text handling, normalisation,
bidirectional text, and locale-specific linting.

Design intent: achieve broad language coverage with param-by-language-code
behaviour while keeping the core deterministic and fast.

---

## F-1 Principles

1. **Predictability first.** Prefer NFC normalisation and explicit macros over
   ambiguous look-alikes.
2. **Context matters.** Verbatim, math, and code environments are sanctuaries --
   no normalisation or spacing fixes inside them.
3. **Local policy knobs.** Language-code parameters (`en`, `fr`, `ja`, `ar`)
   toggle locale rules and spacing policies.
4. **Proof-friendly.** Every normalisation rule has a semantics-preservation
   lemma or is marked non-semantic (style-only).

---

## F-2 Normalisation Policy

- **Default:** NFC on text segments; do not apply NFKC globally.
- **Exceptions:** Inside `verbatim`, `lstlisting`, `minted`, and math
  environments, skip normalisation; only validate encoding.
- **Homoglyph policing:** Detect risky codepoints (Greek mu vs micro sign);
  suggest safe replacements; never auto-replace in code blocks.

Rationale: NFC preserves grapheme equivalence without dropping distinctions
that matter in identifiers.

---

## F-3 Language Detection (`language_detect.ml`)

### F-3.1 Algorithm

Detection follows a priority chain with four stages:

```
1. \usepackage[lang]{babel}     --> babel_to_iso mapping (65 entries)
2. \usepackage{polyglossia}     --> \setmainlanguage{} / \setdefaultlanguage{}
3. CJK heuristic                --> scan for CJK/Hangul/Katakana/Arabic bytes
4. Fallback                     --> "en"
```

### F-3.2 Babel-to-ISO Mapping

The `babel_to_iso` table in `language_detect.ml` contains 65 entries covering
all major LaTeX babel language names:

```ocaml
(* latex-parse/src/language_detect.ml -- 65-entry babel mapping *)
let babel_to_iso = [
  (* Romance *)
  ("french", "fr"); ("francais", "fr"); ("frenchb", "fr");
  ("acadian", "fr"); ("spanish", "es"); ("castilian", "es");
  ("portuguese", "pt"); ("brazilian", "pt"); ("italian", "it");
  ("romanian", "ro"); ("catalan", "ca");
  (* Germanic *)
  ("english", "en"); ("british", "en"); ("american", "en");
  ("UKenglish", "en"); ("USenglish", "en"); ("australian", "en");
  ("german", "de"); ("ngerman", "de"); ("ogerman", "de");
  ("austrian", "de"); ("dutch", "nl"); ("swedish", "sv");
  ("norsk", "no"); ("danish", "da"); ("icelandic", "is");
  (* Slavic *)
  ("russian", "ru"); ("ukrainian", "uk"); ("polish", "pl");
  ("czech", "cs"); ("slovak", "sk"); ("serbian", "sr");
  ("croatian", "hr"); ("slovenian", "sl"); ("bulgarian", "bg");
  (* CJK *)
  ("japanese", "ja"); ("chinese", "zh"); ("korean", "ko");
  (* RTL *)
  ("arabic", "ar"); ("hebrew", "he"); ("farsi", "fa");
  (* Greek *)
  ("greek", "el"); ("polutonikogreek", "el");
  (* Indic *)
  ("hindi", "hi"); ("tamil", "ta"); ("bengali", "bn");
  (* Other *)
  ("turkish", "tr"); ("finnish", "fi"); ("hungarian", "hu");
  ("estonian", "et"); ("latvian", "lv"); ("lithuanian", "lt");
  ("thai", "th"); ("vietnamese", "vi"); ("welsh", "cy");
  ("irish", "ga"); ("scottish", "gd");
  (* ... plus dialect variants *)
]
```

The table is loaded into a `Hashtbl` at module initialisation. Lookup is
case-insensitive via `String.lowercase_ascii`.

### F-3.3 Babel Detection

```ocaml
let detect_babel preamble =
  let re = Str.regexp {|\\usepackage\[\([^]]*\)\]{babel}|} in
  (* Parse comma-separated options; last one is the main language *)
  match List.rev (String.split_on_char ',' opts) with
  | main :: _ -> resolve_babel_name (String.trim main)
  | [] -> None
```

Babel convention: when multiple languages are listed, the *last* option is the
main document language.

### F-3.4 Polyglossia Detection

```ocaml
let detect_polyglossia preamble =
  let re1 = Str.regexp {|\\setdefaultlanguage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  let re2 = Str.regexp {|\\setmainlanguage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  (* Try re1, then re2; resolve via babel_to_iso *)
```

Handles optional square-bracket arguments (e.g., `\setdefaultlanguage[variant=british]{english}`).

### F-3.5 CJK Heuristic

When no explicit language declaration is found, the detector scans for script-
specific byte patterns in the full document:

```ocaml
let detect_cjk_heuristic s =
  if has_hangul s   then Some "ko"   (* U+AC00-U+D7AF: 0xEA-0xED lead bytes *)
  else if has_katakana s then Some "ja" (* U+30A0-U+30FF: 0xE3 0x82-0x83 *)
  else if has_cjk_codepoints s then Some "zh" (* U+4E00-U+9FFF: 0xE4-0xE9 *)
  else if has_arabic s then Some "ar"  (* U+0600-U+06FF: 0xD8-0xDB *)
  else None
```

Priority: Hangul > Katakana > CJK Unified > Arabic.

**Known limitation:** CJK codepoints appearing in comments trigger the heuristic.
This is documented in tests and accepted as a low-impact edge case.

### F-3.6 Main Entry Point

```ocaml
let detect_language ?(default = "en") (s : string) : string =
  let preamble = extract_preamble s in
  match detect_babel preamble with
  | Some lang -> lang
  | None ->
    match detect_polyglossia preamble with
    | Some lang -> lang
    | None ->
      match detect_cjk_heuristic s with
      | Some lang -> lang
      | None -> default
```

---

## F-4 Unicode Text Segmentation (`unicode_split.ml`)

### F-4.1 Character Classification

The `classify_uchar` function maps Unicode scalar values to seven broad
categories:

```ocaml
(* latex-parse/src/unicode_split.ml *)
type uchar_category =
  | Letter       (* Latin A-Z/a-z, Extended Latin, Greek, Cyrillic *)
  | Digit        (* ASCII 0-9, Arabic-Indic 0660-0669 *)
  | Whitespace   (* Space, Tab, LF, CR, NBSP U+00A0, Ideographic space U+3000 *)
  | Punctuation  (* ASCII punct, CJK symbols 3000-303F, Fullwidth FF01-FF0F *)
  | CJK          (* Unified Ideographs, Extensions A/B, Hiragana, Katakana *)
  | Arabic       (* Arabic script U+0600-06FF, Supplements, Presentation Forms *)
  | Other

let classify_uchar (u : Uchar.t) : uchar_category =
  let cp = Uchar.to_int u in
  (* CJK ranges checked first for fast-path on CJK-heavy documents *)
  if cp >= 0x4E00 && cp <= 0x9FFF then CJK
  else if cp >= 0x3400 && cp <= 0x4DBF then CJK    (* Extension A *)
  else if cp >= 0x20000 && cp <= 0x2A6DF then CJK   (* Extension B *)
  else if cp >= 0xF900 && cp <= 0xFAFF then CJK     (* Compat *)
  else if cp >= 0x3000 && cp <= 0x303F then Punctuation (* CJK Symbols *)
  else if cp >= 0x3040 && cp <= 0x309F then CJK     (* Hiragana *)
  else if cp >= 0x30A0 && cp <= 0x30FF then CJK     (* Katakana *)
  else if cp >= 0x0600 && cp <= 0x06FF then Arabic
  (* ... Latin, Greek, Cyrillic, digits, whitespace, punctuation ... *)
```

### F-4.2 Word Segmentation

`split_words` partitions text into `word_segment` records:

```ocaml
type word_segment = {
  w_text  : string;
  w_start : int;   (* byte offset *)
  w_end   : int;   (* byte offset *)
}
```

Segmentation rules:

| Script class | Word boundary |
|-------------|---------------|
| Latin / Greek / Cyrillic | Consecutive letters form one word; break on whitespace/punctuation |
| CJK | Each character is its own word (no whitespace boundaries in CJK) |
| Arabic | Consecutive Arabic characters form one word; break on whitespace |
| Mixed scripts | Script transitions create word boundaries |

Implementation uses the `Uutf` library for proper UTF-8 decoding via
incremental decoder.

### F-4.3 Sentence Segmentation

`split_sentences` identifies sentence boundaries using Unicode-aware terminators:

```ocaml
let is_sentence_end (u : Uchar.t) : bool =
  let cp = Uchar.to_int u in
  cp = 0x2E     (* . *)   || cp = 0x21     (* ! *)   || cp = 0x3F (* ? *)
  || cp = 0x3002 (* CJK period *)
  || cp = 0xFF01 (* fullwidth ! *)
  || cp = 0xFF1F (* fullwidth ? *)
  || cp = 0x06D4 (* Arabic period *)
```

Boundary rule: sentence terminator followed by whitespace.

```ocaml
type sentence_segment = {
  s_text  : string;
  s_start : int;
  s_end   : int;
}
```

### F-4.4 Roundtrip Property

The concatenation roundtrip property is the OCaml witness for
`proofs/SplitPreservesOrder.v`:

```ocaml
let words_preserve_content (s : string) : bool =
  let words = split_words s in
  let joined = concat_words words in
  strip joined = strip s
  (* strip removes whitespace/punctuation *)
```

Formal proof: sorted segments have strictly increasing start positions; total
content length distributes over append.

---

## F-5 High-Throughput Sentence Splitter (`sentence_split.ml`)

A separate, simpler sentence splitter optimised for throughput (target: 50 MiB/s):

```ocaml
(* latex-parse/src/sentence_split.ml *)
type sentence = {
  text      : string;
  start_pos : int;
  end_pos   : int;
  word_count: int;
}

let split (s : string) : sentence list =
  (* Heuristic: ". " followed by uppercase letter *)
```

This is used by L4 style validators (STYLE-017 sentence length, STYLE-021 passive
voice) where full Unicode sentence segmentation is not needed.

---

## F-6 L0 Tokenizer UTF-8 Support (`tokenizer_lite.ml`)

The tokenizer handles mixed ASCII/Unicode input:

| Input byte range | Handling |
|-----------------|----------|
| `< 0x80` | ASCII fast path via `is_letter` |
| `>= 0x80` (lead byte) | Decode full codepoint via `decode_uchar_at` |
| Unicode letter (non-CJK) | Accumulate into multi-byte `Word` token |
| CJK codepoint | Individual `Word` per character |
| Other non-ASCII | `Symbol` token |

**Invariant:** Command names (`\cmd`) remain ASCII-only, per the LaTeX spec.

Token types:

```ocaml
type kind =
  | Word | Space | Newline | Command | Bracket_open
  | Bracket_close | Quote | Symbol
```

---

## F-7 Per-Language Rule Gating

### F-7.1 Rule Type Extension

Rules carry an optional language list in `validators_common.ml`:

```ocaml
type rule = {
  id        : string;
  run       : string -> result option;
  languages : string list;
    (** ISO 639-1 codes. Empty = universal (fires on all documents).
        Non-empty = only fires when document language matches. *)
}

let mk_rule id run = { id; run; languages = [] }
let mk_lang_rule id run langs = { id; run; languages = langs }
```

### F-7.2 Dispatch

The `run_all_for_language` dispatcher:
1. Auto-detects document language via `language_detect.ml`
2. Filters rules: universal rules always run; language-specific rules run only
   when the document language matches
3. Accepts an explicit language parameter to override auto-detection

### F-7.3 Language Pack Registry

```ocaml
(* latex-parse/src/language_detect.ml *)
let live_packs    = ["en"; "fr"; "de"; "es"; "ja"; "zh"; "ar"]
let stubbed_packs = ["ko"; "ru"; "pl"; "pt"; "cs"; "el"; "ro"; "he";
                     "hi"; "tr"; "nl"; "cy"; "sv"; "it"]
let all_packs = live_packs @ stubbed_packs  (* 21 total *)
```

---

## F-8 Language Support Matrix

| ISO | Language | Pack Status | Live Validators | Notes |
|-----|----------|-------------|-----------------|-------|
| en | English | Live | 37 | Primary language |
| fr | French | Live | 12 | Guillemets, NBSP before `;:!?` |
| de | German | Live | 8 | Eszett, quotation marks |
| es | Spanish | Live | 6 | Inverted punctuation |
| ja | Japanese | Live | 5 | CJK + ruby annotations |
| zh | Chinese | Live | 5 | CJK + full-width punctuation |
| ar | Arabic | Live | 4 | RTL + diacritics |
| pt | Portuguese | Stubbed | -- | -- |
| it | Italian | Stubbed | -- | -- |
| nl | Dutch | Stubbed | -- | IJ digraph capitalisation |
| ru | Russian | Stubbed | -- | NBSP before em-dash |
| ko | Korean | Stubbed | -- | Hangul syllable boundaries |
| pl | Polish | Stubbed | -- | NBSP before abbreviations |
| sv | Swedish | Stubbed | -- | -- |
| tr | Turkish | Stubbed | -- | Dotless i handling |
| vi | Vietnamese | Stubbed | -- | Combining marks |
| uk | Ukrainian | Stubbed | -- | -- |
| th | Thai | Stubbed | -- | No word boundaries |
| cs | Czech | Stubbed | -- | No thin space before C |
| ro | Romanian | Stubbed | -- | -- |
| el | Greek | Stubbed | -- | Polytonic/monotonic |

Target: 21 languages by v25 GA (Week 156).

---

## F-9 Locale-Specific Spacing and Punctuation

| Locale | Rule | Policy |
|--------|------|--------|
| French | NBSP before `; : ! ?` | Insert U+00A0 before high punctuation |
| French | Thin NBSP around Euro | `5\,\texteuro` or NNBSP |
| Russian | NBSP before em-dash | Non-breaking space before `---` |
| Polish | NBSP before abbreviations | `r.` `nr` `s.` require NBSP before |
| Czech/Slovak | No thin space before C | `20\,^\circ C` not `20 ^\circ C` |
| Dutch | IJ/ij digraph capitalisation | `IJ` at sentence start, not `Ij` |
| CJK | Full-width punctuation in CJK runs | Use full-width comma/period in CJK text |
| CJK | No Western space between CJK glyphs | Remove inter-character spaces |

Each rule is surfaced as a locale-aware validator with appropriate layer
preconditions (L0 for character-level, L4 for text-level heuristics).

---

## F-10 CJK-Specific Rules

| Rule ID | Description | Check |
|---------|-------------|-------|
| CJK-001 | Missing CJK font package | Regex: CJK chars without `xeCJK`/`CJKutf8`/`luatexja` |
| CJK-003 | Incorrect CJK punctuation spacing | Full-width vs half-width detection |
| CJK-009 | CJK text in math mode | CJK codepoints inside `$...$` |
| CJK-011 | Mixed CJK/Latin without proper spacing | Missing `\,` or xeCJK auto-spacing |
| CJK-013 | Ruby annotation syntax error | `\ruby{}{}` argument validation |

---

## F-11 RTL-Specific Rules

| Rule ID | Description | Check |
|---------|-------------|-------|
| RTL-001 | Missing bidi package for RTL text | Arabic/Hebrew chars without `bidi`/`polyglossia` |
| RTL-002 | Incorrect RTL/LTR boundary markers | Missing `\textLR`/`\textRL` at script transitions |

---

## F-12 Bidirectional Text Policy

- Enforce isolation marks where LTR acronyms appear in RTL runs and vice versa.
- Reject stray Unicode embedding controls (U+202A--U+202E) outside explicit
  bidi contexts.
- Provide `\textLR`/`\textRL` helper recommendations.

---

## F-13 Corpus Strategy

### F-13.1 Golden Corpus

12 YAML test suites, 329 test cases across the 7 live language packs:

- `tests/golden/en/` -- English baseline (largest suite)
- `tests/golden/fr/` -- French spacing and guillemets
- `tests/golden/de/` -- German quotation marks
- `tests/golden/es/` -- Spanish inverted punctuation
- `tests/golden/ja/` -- Japanese CJK handling
- `tests/golden/zh/` -- Chinese CJK handling
- `tests/golden/ar/` -- Arabic RTL

### F-13.2 External Corpora

Locked via `corpora.lock` (SHA-256 + URL). CI job `fetch_corpora` retrieves
them deterministically.

---

## F-14 Unicode Scope

### In Scope for v25

- UTF-8 encoding detection and validation
- NFC normalisation awareness (detect non-NFC input)
- Unicode letter classification for tokenization (via `classify_uchar`)
- CJK/Arabic/RTL script detection (via `detect_cjk_heuristic`)
- Word and sentence segmentation (via `unicode_split.ml`)
- 7 live language packs with locale-specific validators

### Out of Scope for v25

- Full Unicode equivalence beyond NFC (NFKC, NFD)
- Unicode collation (sorting by locale)
- Complex text layout (ligatures, contextual shaping)
- Emoji handling
- Full grapheme cluster segmentation (using ICU BreakIterator)
- Indic script conjunct validation (ZWJ/ZWNJ)

---

## F-15 Libraries and Implementation Notes

| Dependency | Role | Version |
|-----------|------|---------|
| `Uutf` | UTF-8 encoding/decoding | Part of opam lockfile |
| `Str` | Regex for preamble parsing | OCaml stdlib |

All Unicode classification is implemented with pure OCaml range checks -- no
OS-level ICU dependency. This ensures deterministic behaviour across platforms.

---

## F-16 Edge Cases (Documented)

1. **CJK in comments triggers heuristic:** The `detect_cjk_heuristic` function
   scans the entire document, including comments. A purely-English document with
   CJK in comments may be misclassified. Workaround: use explicit `\usepackage[english]{babel}`.

2. **Mixed RTL numbers inside LTR equations:** Arabic-Indic digits (U+0660--U+0669)
   inside math mode retain their LTR directionality per LaTeX convention.

3. **Non-breaking hyphen in URLs:** Allowed inside `\url{}` but flagged in plain
   text. The `in_verbatim` parser-state feature prevents false positives.

4. **French guillemets inside code comments:** Ignored by design -- comments are
   excluded from all locale validators.

---

## F-17 Glossary

| Term | Definition |
|------|-----------|
| NFC | Canonical Decomposition followed by Canonical Composition |
| NFKC | Compatibility variant of NFC |
| Kinsoku shori | Japanese typesetting line-break prohibition rules |
| Bidi isolate | Unicode isolate marks (U+2066--U+2069) limiting directionality scope |
| NBSP | Non-Breaking Space (U+00A0) |
| NNBSP | Narrow No-Break Space (U+202F) -- used in French typography |
| Grapheme cluster | User-perceived character (may be multiple codepoints) |
| Babel | LaTeX package for multilingual typesetting |
| Polyglossia | Modern multilingual package for XeLaTeX/LuaLaTeX |

---

End of Appendix F.
