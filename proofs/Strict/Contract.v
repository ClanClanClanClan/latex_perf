(** * Strict.Contract — the configuration contract, as the kernel sees it.

    ADR-012 / STRICT_TIER_DESIGN.md §B.  A contract is generated data, never
    hand-listed (§B.2 "the generator is the only writer"); the kernel takes
    it as a PARAMETER.  Every theorem of the kernel is quantified over every
    contract [C], so no fact about any particular name is assumed in Coq.

    The runtime value comes from committed, generated files:
    - [c_defined] is membership in the closed world of the configuration:
      the kernel names of the pinned format
      (corpora/contracts/kernel/<arch>-<fmt>.json) updated by the
      configuration's [defined_names] (corpora/contracts/article.json; a
      name of kind [Undefined] there was removed by the configuration).
      The contract generator attests that this set is exact at body start
      (gen_contract.py, TeX's own hash-table count; design §I.2).
    - [c_sig] is the probe-attested behaviour of a defined name, read from
      corpora/contracts/strict/article-s0-signatures.json, which
      scripts/tools/gen_strict_signatures.py writes from solo probes run
      under the pinned oracle.  A defined name with no signature is OUTSIDE
      the strict tier (design §A.1.3): the kernel never guesses it.
    The OCaml loader that builds this record from those files is the
    trusted component T5 of the design's trusted base (§G.2). *)

From LaTeXPerfectionist.Strict Require Import Syntax.

(** The decided fatal reasons of phase 1 (design §C.2).  Codes that phase 1
    cannot produce (E2, E7-E14) are added with the constructs that produce
    them (M3 and later). *)
Inductive reason :=
| E0   (* rc 0 but no PDF: nothing was typeset *)
| E1   (* undefined control sequence *)
| E3   (* mode violation: ^/_ or a math-only command in text, a text-only
          command in math *)
| E4   (* double superscript / double subscript *)
| E5   (* stack discipline: stray }, a math delimiter that does not match
          the open math, unclosed math at \end{document}, no \end{document} *)
| E6.  (* \par (or a blank line) in math *)

(** How a defined control word behaves when it is executed in TEXT (vertical
    or horizontal) mode, as attested by probes. *)
Inductive text_beh :=
| TxMaterial            (* typesets: the document gets a page *)
| TxNoop                (* no material, no change of any modelled state *)
| TxFatal (r : reason). (* stops pdflatex, with reason [r] *)

(** ... and in MATH mode. *)
Inductive math_beh :=
| MxNoad                (* appends a new noad: the next ^/_ attaches to it *)
| MxNoop                (* appends no noad: a following ^/_ still sees the
                           previous noad's scripts *)
| MxFatal (r : reason).

Record signature := mkSig { sig_text : text_beh; sig_math : math_beh }.

Record contract := mkContract {
  c_defined : name -> bool;
  c_sig : name -> option signature
}.

(** Well-formedness the loader checks (a signature only for a defined name).
    No theorem of the kernel needs it: an undefined name is decided E1
    whatever its (then meaningless) signature says. *)
Definition contract_wf (C : contract) : Prop :=
  forall n s, c_sig C n = Some s -> c_defined C n = true.
