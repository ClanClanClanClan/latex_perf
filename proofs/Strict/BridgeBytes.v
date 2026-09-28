(** * Strict.BridgeBytes — from the proved decision on BYTES to pdflatex.

    ADR-012 / STRICT_TIER_DESIGN.md §0 and §C.3, trust layer (3), for a file
    given as bytes (M2 phase 2).  That the declarative reading [LexFile], the
    front matter and body [Parse], and the semantics [Runs] together describe
    what the pinned pdflatex does with a file CANNOT be proved in Coq.  It is
    the named [Definition] [FaithfulBytes], an explicit PREMISE of the bridge
    corollary, never an [Axiom] and never a [Section] [Hypothesis]; so
    [Print Assumptions strict_ready_iff_pdflatex_bytes] stays "Closed under
    the global context" (scripts/tools/check_print_assumptions.py).

    [FaithfulBytes] is stated against the DECLARATIVE side only: for every
    file in the fragment and its declarative parse [ks], the oracle compiles
    the file iff [Runs] derives [Compiles] on the kernel stream of [ks].  It
    never mentions the decider or the executable lexer and parser.  Its body
    is pinned three ways, as [Bridge.Faithful]'s is (OPEN-121 final review
    MEDIUM-1 and re-review, C-87): coqc's [Print], a kernel [eq_refl]
    convertibility check against fully qualified names
    (check_print_assumptions.py), and a textual scan of every Coq sentence of
    this file (scripts/tools/check_strict_bytes.py, kill-tested).

    [oracle_ok bytes] is Bridge.v's: the pinned pdflatex, under the oracle
    protocol of design §B.4, exits 0 AND writes a PDF on these bytes, each
    pass within the 300 s oracle timeout (scripts/tools/_oracle.py).  The
    bridge covers READY iff compiles ONLY: the reason and the line of a
    NOT-READY are exact against [Runs] and the declarative [ReportedLine]
    ([DecideBytes.decide_bytes_exact]), and agree with pdfTeX's first error
    and its [l.N] by the probes and the byte-level differential, not by this
    file.  [FaithfulBytes] is attested, not proved, by the probe families of
    every constructor of Lexer.v, Front.v and Semantics.v and by the
    differential (scripts/tools/strict_differential.py --bytes), which run
    the EXTRACTED [decide_bytes] (ExtractBytes.v) on the very bytes the
    oracle grades. *)

From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics Decide Lexer Front DecideBytes.

Definition FaithfulBytes (oracle_ok : list Ascii.ascii -> Prop) (C : bcontract) : Prop :=
  forall b ks, in_strict_bytes C b -> Parse (bc_lex C) b ks ->
    (oracle_ok b <-> Runs (bc_kernel C) init (toks_of ks) Compiles).

Corollary strict_ready_iff_pdflatex_bytes : forall oracle_ok C b,
  FaithfulBytes oracle_ok C ->
  in_strict_bytes C b ->
  (decide_bytes C b = ProvenReady <-> oracle_ok b).
Proof.
  intros oracle_ok C b HF Hs.
  destruct Hs as [Hlen [ks [Hp Hk]]].
  assert (Hin : in_strict_bytes C b) by (split; [exact Hlen|exists ks; split; assumption]).
  destruct (decide_bytes_exact C b ks Hin Hp) as [Hready _].
  rewrite Hready. symmetry. apply HF; assumption.
Qed.

(** The NOT-READY side under the same premise: a file in the fragment the
    decider rejects is one pdflatex does not compile. *)
Corollary strict_not_ready_pdflatex_bytes : forall oracle_ok C b r ln,
  FaithfulBytes oracle_ok C ->
  in_strict_bytes C b ->
  decide_bytes C b = ProvenNotReady r ln -> ~ oracle_ok b.
Proof.
  intros oracle_ok C b r ln HF Hs Hd Hok.
  apply (proj2 (strict_ready_iff_pdflatex_bytes oracle_ok C b HF Hs)) in Hok.
  rewrite Hd in Hok. discriminate.
Qed.
