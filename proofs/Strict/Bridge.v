(** * Strict.Bridge — from the proved decider to pdflatex, under [Faithful].

    ADR-012 / STRICT_TIER_DESIGN.md §0 and §C.3, trust layer (3).  That the
    semantics [Runs] describes real pdflatex CANNOT be proved in Coq: it is a
    claim about a program Coq does not model.  It is therefore a named
    [Definition], [Faithful], taken as an explicit PREMISE of the bridge
    corollary — never an [Axiom] and never a [Section] [Hypothesis] (which
    would disappear into a binder at [End]).  So [Print Assumptions
    strict_ready_iff_pdflatex] stays Closed under the global context
    (scripts/tools/check_print_assumptions.py enforces it), and the
    corollary's statement shows [Faithful] as its only premise about the
    world; the others are structural ([in_strict_doc]).

    [oracle_ok bytes] is: the pinned pdflatex, under the oracle protocol of
    design §B.4 (nonstopmode, halt-on-error, run to the first rc 0 then one
    confirming pass), exits 0 AND writes a PDF on these bytes, within the
    oracle timeout (scripts/tools/_oracle.py, [OracleRun.compiles]; the
    timeout is 300 s PER PASS, design §B.4: [run_to_fixpoint] runs up to
    MAX_PASSES = 3 passes plus one confirming pass, each bounded by 300 s,
    so the wall-clock bound on [oracle_ok] is (3+1) x 300 s = 1200 s, and a
    run with a pass that times out is not ok).
    The bridge covers READY iff compiles ONLY: the reason and line of a
    NOT-READY are exact against [Runs], and agree with pdfTeX by the probes
    and the differential, not by this file.  The BODY of [Faithful] is
    pinned by check_print_assumptions.py (coqc [Print]) and by
    check_strict_kernel.py check 10; it must mention [Runs] and never the
    decider (OPEN-121 final review, MEDIUM-1).  [Faithful] is attested
    — not proved — by the probes of every [Runs] constructor and by the
    generated differential (scripts/tools/strict_differential.py), which runs
    the EXTRACTED [render] and [decide] (Extract.v) against that oracle.

    This file holds no double-quote character, not even in a comment: in
    Coq a string opens inside a comment too, so a comment delimiter inside
    one moves where the comment ends (OPEN-121 re-review 2, HIGH-1); the
    whole code of this file is pinned by check_strict_kernel.py check 10,
    and its three constants by check_print_assumptions.py against fully
    qualified names (kernel conversion) and by [Print Module].

    Phase-1 deviation from the design's statement: there is no [parse] yet,
    so the corollary starts from the tree [d], not from bytes; [parse_exact]
    and the bytes-level corollary are phase 2. *)

From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics Decide.

Definition Faithful (oracle_ok : list Ascii.ascii -> Prop) (C : contract) : Prop :=
  forall d, in_strict_doc C d ->
    (oracle_ok (render d) <-> Runs C init (flatten_doc d) Compiles).

Corollary strict_ready_iff_pdflatex : forall oracle_ok C d,
  Faithful oracle_ok C ->
  in_strict_doc C d ->
  (decide C d = ProvenReady <-> oracle_ok (render d)).
Proof.
  intros oracle_ok C d HF Hs.
  destruct (strict_decider_exact C d Hs) as [Hready _].
  rewrite Hready. symmetry. apply HF. exact Hs.
Qed.

(** The NOT-READY side under the same premise: a strict document the decider
    rejects is one pdflatex does not compile. *)
Corollary strict_not_ready_pdflatex : forall oracle_ok C d r l,
  Faithful oracle_ok C ->
  in_strict_doc C d ->
  decide C d = ProvenNotReady r l -> ~ oracle_ok (render d).
Proof.
  intros oracle_ok C d r l HF Hs Hd Hok.
  apply (proj2 (strict_ready_iff_pdflatex oracle_ok C d HF Hs)) in Hok.
  rewrite Hd in Hok. discriminate.
Qed.
