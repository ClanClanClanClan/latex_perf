# CST round-trip edge cases (v26.2 PR B2)

Synthetic inputs that stress `Cst_of_ast`'s byte-losslessness. Each
file here is a hand-crafted corner case chosen because it exercises
one of the harder regions of the AST→CST conversion:

- Empty file, whitespace-only, single-character
- BOM, CRLF line endings, mixed line endings
- Unclosed math, unclosed braces, unclosed environment
- Nested groups of depth > 10
- Verbatim with all delimiters
- Unicode categories: composed & decomposed forms
- Comments with weird characters
- Commands with many optional and mandatory args

All files here are used by `latex-parse/src/test_cst_roundtrip.ml` in
addition to the broader `corpora/lint/` sweep. For each file we assert:

```
Cst.serialize (Cst_of_ast.of_source src) = src
```

See `docs/CST_ROUNDTRIP_SCOPE.md` for what losslessness means at
higher levels of abstraction (structure-lossless subset vs.
byte-lossless everything).
