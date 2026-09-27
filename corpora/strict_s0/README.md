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
| `rule_probes.json` | directed probes, a few per `Runs` constructor (family = constructor name, cited in each constructor's comment in `proofs/Strict/Semantics.v`), each graded and compared; `by_family` says how many probes each family has, how many agree, and how many actually used the constructor |
| `differential_v1.json` | the generated differential v1: seeded random documents of the fragment, weighted toward boundaries; per verdict class and per constructor, every disagreement in full |

The agreement rule (`scripts/tools/_strict_s0.py`, `agrees`): READY iff rc 0
and a PDF; E0 iff rc 0 and no PDF; any other reason iff rc is not 0, the first
`!` message is one pdfTeX gives for that reason at that token in that mode,
and the line of the fatal token equals the oracle's `l.N`. A wrong reason or
a wrong line is a disagreement (ADR-012 decision 6).

`scripts/tools/check_strict_kernel.py` (pure) checks that every constructor
has an agreeing, exercised family here, that both files ran the committed
extraction, signature file, kernel and contract, and that neither reports a
disagreement.

Regenerate (needs docker and the pinned image; local or nightly only):

    python3 scripts/tools/strict_differential.py --rules
    python3 scripts/tools/strict_differential.py --random 1200 --seed 1
