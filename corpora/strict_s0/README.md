# Evidence of the strict kernel L_S0 (ADR-012, milestone M2 phase 1)

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
| `differential_v2.json` | the generated differential v2 (generator version 2, seed 2): seeded random documents of the fragment, weighted toward boundaries, and since v2 also a `$` in display math followed by a name, runs of names repeated up to 300 times and brace nesting up to the bound; per verdict class and per constructor, every disagreement in full. Its `upper_bound_95` is a bound over THIS generator's distribution, not over L_S0 (C-85). v1 (1,200 documents) is in git history; it drew none of those shapes |

The agreement rule (`scripts/tools/_strict_s0.py`, `agrees`): READY iff rc 0
and a PDF; E0 iff rc 0 and no PDF; any other reason iff rc is not 0, the first
`!` message is one pdfTeX gives for that reason at that token in that mode,
and the line of the fatal token equals the oracle's `l.N`. A wrong reason or
a wrong line is a disagreement (ADR-012 decision 6).

`scripts/tools/check_strict_kernel.py` (pure) checks that every constructor
has an agreeing, exercised family here, that every branch-matrix cell the
grammar allows is covered, that the BOUND family agrees, that both files ran
the committed extraction, signature file, kernel and contract, and that
neither reports a disagreement.

Regenerate (needs docker and the pinned image; local or nightly only):

    python3 scripts/tools/strict_differential.py --rules
    python3 scripts/tools/strict_differential.py --random 3000 --seed 2
