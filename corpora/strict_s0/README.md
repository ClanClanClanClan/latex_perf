# Evidence of the strict kernel L_S0 (ADR-012, milestone M2 phases 1 and 2)

Generated data. The kernel is `proofs/Strict/` (Coq), extracted to
`latex-parse/strict/strict_kernel_extracted.ml`; these files are the evidence
that its semantics `Runs` describes the pinned pdflatex (the premise
`Faithful` of `Bridge.strict_ready_iff_pdflatex`, which cannot be proved and
is attested instead). Both were produced by `scripts/tools/strict_differential.py`,
which runs the EXTRACTED decider and renderer (through
`latex-parse/strict/strict_decide.ml`) and grades the rendered bytes with the
one oracle (`scripts/tools/_oracle.py`, the pinned image).

| file | what |
|---|---|
| `rule_probes.json` | directed probes, a few per `Runs` constructor (family = constructor name, cited in each constructor's comment in `proofs/Strict/Semantics.v`); the BRANCH MATRIX (family `MATRIX`: every innermost frame x every token class, and for `$`, `^`, `_`, whose rules read the next token, x every follower class; each probe records the `head\|token\|follower\|tail` cells it passed, C-85); the BOUND family (the structure at the capacity bounds of `Decide.v`, C-86); and, under `outside_tier`, the documents built to be outside the tier (`MATRIX-OUT`: a script without its argument; `BOUND-OUT`: one past a bound), recorded and never graded |
| `bytes_probes.json` | M2 phase 2, the decision on the BYTES of a file (`proofs/Strict/Lexer.v`, `Front.v`, `DecideBytes.v`, run as the extracted `decide_bytes` through `strict_decide.exe --bytes`): directed files per constructor of the reader and the front matter (family = constructor name, cited as `probe L0/<constructor>` in the Coq sources), the family `L0-bounds` (a 10,000-byte line, a 1,000,000-byte file, 20,000 kernel tokens, 200 nested groups), the phase-1 rule probes' rendered bytes re-laid out four ways (`P1-RENDER` as rendered, `P1-TIGHT` lines joined, `P1-COMMENT` joined through comments holding any byte, `P1-MIXED` CR/CR LF/LF line ends, padding and comments mixed, front matter and `\end{document}` varied, bytes after `\end{document}`), and under `outside` the files outside the fragment by design (the reader's outside rules and the near-misses `L0-NEAR`), decided and never graded. Each graded record carries the reader's rule and branch labels (`lex_rules`, `lex_branches`) and the kernel's (`rules`, `branches`). `summary.tree_bytes_consistency`: the tree decider and the bytes decider on every phase-1 rendering (verdict, reason, line) |
| `bytes_differential.json` | M2 phase 2's generated differential: files half re-laid-out phase-1 trees and half generated directly as byte strings (`_strict_bytes.Direct`), plus the near-misses; per verdict class and per `Runs` constructor. A generated file the decider places outside is replaced and counted (`generated_outside_replaced`); its bound is over THIS generator's distribution |
| `differential_v3.json` | the generated differential v3 (generator version 3, ADR-012 step 2 slice A): seeded random documents of the fragment, weighted toward boundaries — a `$` in display math followed by a name, runs of names repeated up to 300 times, brace nesting up to the bound (v2), and since v3 the one-argument commands (`Gen.arg`), their arguments in the mode they run in, with the step-2 hazards inside failing documents (an undefined name, a paragraph break or blank line, a `$` or script in the wrong mode, `$$` and `\[ \]` in an hbox, nested commands, a stray brace, a command where it stops); per verdict class and per constructor (Runs, Scans, Stops), every disagreement in full. Its `upper_bound_95` is a bound over THIS generator's distribution, not over the fragment (C-85). v1 (1,200 documents) and v2 (4,000, phase 1) are in git history |

The agreement rule (`scripts/tools/_strict_s0.py`, `agrees`): READY iff rc 0
and a PDF; E0 iff rc 0 and no PDF; any other reason iff rc is not 0, the first
`!` message is one pdfTeX gives for that reason at that token in that mode,
and the line of the fatal token equals the oracle's `l.N`. A wrong reason or
a wrong line is a disagreement (ADR-012 decision 6). Since step 2 (slice A)
the message is checked against the fatal EVENT and the line against the
fatal's LOCATION: for an error inside the argument of a command they differ
(the event is the offending token, e.g. an undefined name or a paragraph
break in an argument that is not long, "Paragraph ended before ... was
complete"; the location is the closing brace of the outermost argument, where
pdfTeX's reader stands); strict_decide.ml `fatal_event` computes the event,
`deferred` and `loc_stop` record it.

Slice A's families in `rule_probes.json`: `R_arg_*`, `R_close_arg`,
`R_par_short`, `R_dollar_restricted_open`, `R_mopen_display_restricted`,
`Stop_now`, `Stop_defer`, `SC_*` (one per constructor of `Runs`, `Stops` and
`Scans`; a constructor whose premise no admitted argument signature satisfies
is DORMANT and has no family, derived from the files by
`check_strict_kernel.py`), the matrix's argument heads (`arg.text`,
`arg.textr`, `arg.math`) and argument tokens, and `SCAN` (the argument
scanner's cells: every token class, directly in the argument and one group
deeper, per longness). They come after the phase-1 families, so the
byte-level re-layouts of the phase-1 probes are drawn as before. The
one-argument commands' signatures are in
`corpora/contracts/strict/article-s1-arg-signatures.json`
(`scripts/tools/gen_strict_arg_signatures.py`).

Grades are reused only for byte-identical files graded by the same oracle
(every provenance field equal): `strict_differential.py --reuse FILE...`
records the files and the count in each output (`reuse`).

`scripts/tools/check_strict_kernel.py` (pure) checks that every constructor
has an agreeing, exercised family here, that every branch-matrix cell the
grammar allows is covered, that the BOUND family agrees, that both files ran
the committed extraction, signature file, kernel and contract, and that
neither reports a disagreement.

The byte-level files use the same rule on the extracted `decide_bytes`'
verdict (`strict_differential.agrees_bytes`); the LINE compared is the
declarative reported line of `DecideBytes.ReportedLine` (the line of the last
token the outcome depends on; none when the file ends without
`\end{document}`). Line agreement is over the classes that have an `l.N`:
E0 (rc 0, no PDF) has none, so an E0 record carries no line and agrees only
when the oracle reports none.

`scripts/tools/check_strict_bytes.py` (pure) checks the byte-level files: every
constructor of the reader and front matter probe-tagged and attested (or, for
the rules that put a file outside, used by a file decided outside), every cell
of the reader's branch matrix and the kernel's matrix exercised at the byte
level, the committed extraction and lexical contract, 0 disagreements, every
near-miss outside, the pin of `BridgeBytes.v`'s whole code, and that each
record's `agree` and every count of the summary are what the per-file records
(stored oracle tuple, model verdict) give.

Regenerate (needs docker and the pinned image; local or nightly only):

    python3 scripts/tools/gen_strict_signatures.py --reuse <previous file>
    python3 scripts/tools/gen_strict_arg_signatures.py
    python3 scripts/tools/strict_differential.py --rules --reuse <previous files>
    python3 scripts/tools/strict_differential.py --random 3000 --seed 3
    python3 scripts/tools/gen_strict_lexical.py
    python3 scripts/tools/strict_differential.py --bytes-rules --seed 2 --reuse <previous files>
    python3 scripts/tools/strict_differential.py --bytes 3500 --seed 6
