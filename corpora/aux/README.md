# `.aux` corpus fixtures (v26.3 §3 items F + G)

Synthetic minimal `.aux` files for the three supported engines. Each
file contains the expected core macros (`\newlabel`, `\bibcite`,
`\bibstyle`, `\bibdata`, `\@writefile`) plus engine-specific tokens
that `aux_state.ml` recognises without warning.

| File | Engine | Engine-specific tokens |
|---|---|---|
| `pdflatex_minimal.aux` | pdflatex | (none) |
| `xelatex_minimal.aux` | xelatex | `\xetexversion`, `\xetexrevision` |
| `lualatex_minimal.aux` | lualatex | `\luatexversion`, `\luatexrevision`, `\luatexkv@true` |

Round-trip expectation: `Aux_state.of_string` parses each, recovering
1 label (`sec:intro` -> `{1}{1}…{section.1}`), 1 bibcite (`Knuth1984`
-> `1`), `\bibstyle{plain}`, `\bibdata{refs}`, and **zero warnings**
in `parse_warnings`.

These are hand-synthesised representative fixtures (not real engine
output); v26.4+ may swap in genuine engine-generated `.aux` files
once a CI runner with the engines is provisioned.
