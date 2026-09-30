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
| E6.  (* \par (or a blank line) in math, or in the argument of a command
          whose argument is not long (slice A) *)

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

(** ** Commands with one mandatory argument (ADR-012 step 2, slice A)

    A control word whose meaning reads ONE undelimited macro argument, given
    as a brace group right after the name.  pdfTeX first READS the whole
    argument from the file (so the file reader then stands on its closing
    brace), and only then runs the command's expansion.  MEASURED under the
    pinned oracle (the rule probes of family S0/Stop_defer): an error raised
    while the argument's tokens run is reported on the line of that closing
    brace, not on the line of the token that raised it.  How a signature
    describes such a command, attested per name by solo probes
    (scripts/tools/gen_strict_signatures.py, stage A):

    - [as_long], what a paragraph break inside the argument does.  [LLong]:
      nothing special.  [LShortInner]: the command's expansion re-reads its
      argument with a macro that is not long (the text font commands'
      [text@command]); pdfTeX stops with "Paragraph ended before ... was
      complete" before any of the argument runs, where the file reader
      stands.  [LShortOuter]: already the macro that reads the argument FROM
      THE FILE is not long; pdfTeX stops at the paragraph break itself.
    - [as_text] / [as_math], what the command does in text / in math: stop
      before reading the argument ([TFatalNow]/[MFatalNow]: the file reader
      stands on the name); read it and stop ([TFatalAfter]/[MFatalAfter]);
      or read it and run it in a group whose mode is a [pay]
      ([TRun]/[MRun]; in text, [material] says whether the command typesets
      something even for an empty argument).  In math a run argument always
      leaves a fresh tail: the result is a noad, or a node that is not one (a
      box, a choice), and then TeX gives a following script a new empty
      noad.
    - [g] of [TRun]/[MRun] (correction C-94): the number of TeX GROUPS the
      command holds open while its argument runs (an hbox is one, the
      [\hmode@bgroup] of a text font command is one, [\underline] in text
      opens a formula, a math group and an hbox: three).  It is the
      argument frame's share of TeX's grouping level (Decide.v [groups]),
      MEASURED per name and per mode by the capacity probes of
      gen_strict_arg_signatures.py (the deepest nesting of the argument
      that compiles, against the measured capacity of the body), never read
      from a definition. *)

Inductive longness := LLong | LShortInner | LShortOuter.

(** The mode an argument runs in: text, in restricted horizontal mode (an
    hbox: there a double dollar is an empty formula and the display opener of
    LaTeX opens nothing) or not; or math, as a math group. *)
Inductive pay := PText (restricted : bool) | PMath.

Inductive arg_text :=
| TFatalNow (r : reason)
| TFatalAfter (r : reason)
| TRun (material : bool) (p : pay) (g : nat).

Inductive arg_math :=
| MFatalNow (r : reason)
| MFatalAfter (r : reason)
| MRun (p : pay) (g : nat).

(** [as_copy] (correction C-98): the main memory, in words, that each token
    of the command's argument costs while the command runs.  pdfTeX keeps a
    copy of an argument it has read, and a command nested in an argument
    reads its own argument out of that copy: a new copy.  MEASURED per
    command by the argument generator (the slope of memory over the tokens
    held, stage G), rounded up. *)
Record asig := mkASig { as_long : longness; as_text : arg_text; as_math : arg_math;
                        as_copy : nat }.

(** [c_cost] (correction C-98): the main memory, in words, a token costs
    wherever it runs (the nodes it makes, and for a one-argument command the
    memory its running holds besides its argument's copy), MEASURED per
    admitted name by its generator (the name repeated in text, in math, in a
    display) and per structural token by the phase-1 generator, rounded up;
    never read from a definition.  It is an upper bound on every graded
    document (the account is not proved to be one: correction C-104). *)
(** [c_dim] (correction C-104): the DIMENSIONS, in whole points, a token can
    contribute to any dimension pdfTeX computes when it runs in math
    ([c_dim C true t]) or in text ([c_dim C false t]): the absolute widths,
    heights, depths, shifts, stretch and shrink of every node it makes, in
    the worst of the contexts of that mode (in math, each of the four
    styles), plus one inter-atom spacing per math atom it makes, or one kern
    at its left in text.  MEASURED per admitted name and command
    (TeX's own box dump of the name alone, the font's character dimensions)
    and per structural token by the phase-1 generator; never read from a
    definition. *)
Record contract := mkContract {
  c_defined : name -> bool;
  c_sig : name -> option signature;
  c_arg : name -> option asig;   (* slice A: the one-argument commands *)
  c_cost : tok -> nat;
  c_dim : bool -> tok -> nat
}.

(** Well-formedness the loader checks (a signature only for a defined name,
    and never both kinds for one name).  No theorem of the kernel needs it:
    an undefined name is decided E1 whatever its (then meaningless)
    signatures say, and the argument rules require [c_sig C n = None]. *)
Definition contract_wf (C : contract) : Prop :=
  (forall n s, c_sig C n = Some s -> c_defined C n = true) /\
  (forall n a, c_arg C n = Some a -> c_defined C n = true /\ c_sig C n = None).
