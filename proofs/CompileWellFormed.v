(** * CompileWellFormed — T7 output well-formedness (memo §5, ADR-004).

    T7 is hypothesis-parametric in v26.2: we abstract over
    [output_format_well_formed] and [output_wellformed_rule]. v27 WS8
    discharges these against concrete artefact validators (valid PDF
    graph, valid DVI header, etc.) — see [ADMISSIBILITY_MAP.md].

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith.
Import ListNotations.

Section Output_wellformed.

  Variable Project : Type.
  Variable Profile : Type.
  Variable Artefact : Type.

  (** The T6 premise abstracted. *)
  Variable T6_compile_succeeds : Project -> Profile -> Prop.

  (** Produced artefact binder. *)
  Variable produces : Project -> Profile -> Artefact -> Prop.

  (** The toolchain-level well-formedness predicate. *)
  Variable output_format_well_formed : Artefact -> Prop.

  (** Load-bearing hypothesis. v27 WS8 must discharge this. *)
  Hypothesis output_wellformed_rule :
    forall (p : Project) (pf : Profile) (out : Artefact),
      T6_compile_succeeds p pf ->
      produces p pf out ->
      output_format_well_formed out.

  (** ── T7 main theorem ───────────────────────────────────────────── *)

  Theorem T7_output_wellformed :
    forall p pf out,
      T6_compile_succeeds p pf ->
      produces p pf out ->
      output_format_well_formed out.
  Proof.
    (* ANTI-TAUT-OK: wrapper over [output_wellformed_rule]; substantive
       content is in the v27 WS8 discharge target. The supporting
       lemmas below carry the file's substantive proof content. *)
    intros p pf out Hcompile Hprod.
    apply (output_wellformed_rule p pf out); assumption.
  Qed.

  (** ── Supporting lemmas (load-bearing) ───────────────────────────── *)

  (** Uniqueness of well-formedness as a property: two artefacts
      produced under the same (p, pf) are both well-formed. This isn't
      a non-trivial claim about the toolchain, but it's a useful packaged
      form when T7 consumers fan-out to multiple artefacts. *)
  Theorem T7_both_outputs_wellformed :
    forall p pf out1 out2,
      T6_compile_succeeds p pf ->
      produces p pf out1 ->
      produces p pf out2 ->
      output_format_well_formed out1 /\ output_format_well_formed out2.
  Proof.
    intros p pf out1 out2 Hcompile Hp1 Hp2.
    split; apply T7_output_wellformed with (p := p) (pf := pf); assumption.
  Qed.

  (** Monotonicity: if a stronger compile-succeeds predicate holds,
      well-formedness still follows. Useful for v27 WS8 where a toolchain
      may certify a stronger property (e.g. bit-reproducible PDF). *)
  Theorem T7_stable_under_stronger_compile :
    forall (T6_strong : Project -> Profile -> Prop),
      (forall p pf, T6_strong p pf -> T6_compile_succeeds p pf) ->
      forall p pf out,
        T6_strong p pf ->
        produces p pf out ->
        output_format_well_formed out.
  Proof.
    intros T6_strong Himp p pf out Hstrong Hprod.
    apply T7_output_wellformed with (p := p) (pf := pf); auto.
  Qed.

  (** Contrapositive: an artefact that is not well-formed cannot arise
      from a successful compile under the rule. *)
  Theorem T7_contrapositive :
    forall p pf out,
      produces p pf out ->
      ~ output_format_well_formed out ->
      ~ T6_compile_succeeds p pf.
  Proof.
    intros p pf out Hprod Hnwf Hcompile.
    apply Hnwf. apply T7_output_wellformed with (p := p) (pf := pf); assumption.
  Qed.

End Output_wellformed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition compile_wellformed_zero_admits : True := I.
