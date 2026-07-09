(** * FaithfulWS8Bridge — Stage 6 (FAITHFUL-SEMANTICS Tier 3).

    ADDITIVE connection between the faithful operational pass model
    ([LexerFaithfulStep.L0Pass], Stages 4-5) and the shipped WS8
    capstone model ([PdflatexModel]).

    This file is PURELY ADDITIVE: it [Require]s both [LexerFaithfulStep]
    and [PdflatexModel] and proves new theorems downstream of both.  It
    does NOT modify [PdflatexModel.v]; the shipped
    [pdflatex_compile_safe] capstone (Qed, Print Assumptions Closed) is
    untouched and unaffected — a new downstream file cannot change an
    upstream proof term or its assumption footprint.

    Content: the faithful ≤2-pass convergence result
    ([L0Pass.pdflatex_pass_converges_bounded]) SITS INSIDE the WS8
    industry pass budget [PdflatexModel.pdflatex_pass_max] (= 5).  In
    other words, the real aux-stabilisation convergence proved in
    Stage 5 is consistent with — and strictly sharper than — the
    abstract counter-bound the WS8 capstone assumes.

    Zero admits, zero axioms. *)

From Coq Require Import List Arith Lia.
Require Import LexerFaithfulStep.
Require Import PdflatexModel.
Import ListNotations.

(** The faithful convergence witness (k ≤ 2, real [converged] flag)
    also fits the WS8 pass budget [pdflatex_pass_max = 5].  This ties
    the faithful Stage-5 result to the WS8 constant WITHOUT touching the
    capstone: our operational pass provably converges well within the
    5-pass window WS8's [pdflatex_bounded_terminates] posits. *)
Theorem faithful_pass_within_ws8_bound :
  forall (input : list L0Aux.pdflatex_token) (s0 : L0Pass.pass_state),
    L0Pass.bounded_labels input ->
    exists k,
      k <= pdflatex_pass_max /\
      (L0Pass.iterate_pass_step s0 k input).(L0Pass.converged) = true.
Proof.
  intros input s0 Hb.
  destruct (L0Pass.pdflatex_pass_converges_bounded input s0 Hb)
    as [k [Hk Hconv]].
  exists k. split; [| exact Hconv].
  unfold pdflatex_pass_max. lia.
Qed.

(** Consistency of the two models over the same 5-pass budget: for any
    project/profile and any finite-label document, BOTH the WS8 abstract
    bounded-termination [pdflatex_bounded_terminates] (already universal)
    AND the faithful operational convergence hold within
    [pdflatex_pass_max].  The faithful model refines the WS8 one: it
    reaches its (meaningful, set-stabilisation) [converged] flag in ≤ 2
    of the 5 permitted passes. *)
Corollary faithful_refines_ws8_bounded_terminates :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (input : list L0Aux.pdflatex_token) (s0 : L0Pass.pass_state),
    L0Pass.bounded_labels input ->
    pdflatex_bounded_terminates p pf /\
    (exists k,
        k <= pdflatex_pass_max /\
        (L0Pass.iterate_pass_step s0 k input).(L0Pass.converged) = true).
Proof.
  intros p pf input s0 Hb. split.
  - apply pdflatex_bounded_terminates_universal.
  - apply faithful_pass_within_ws8_bound; exact Hb.
Qed.

(** Additionally: the faithful converged run is fatal-free within the
    WS8 budget, connecting Stage-3/Stage-4 log safety to the WS8
    [log_no_fatal] discipline (here the faithful [L0Log.log_no_fatal],
    byte-for-byte the same fatal-marker check as [PdflatexModel]'s). *)
Corollary faithful_within_ws8_bound_and_safe :
  forall (input : list L0Aux.pdflatex_token),
    L0Log.no_fatal_tokens input ->
    exists k,
      k <= pdflatex_pass_max /\
      (L0Pass.iterate_pass_step L0Pass.initial_pass_state k input)
        .(L0Pass.converged) = true /\
      L0Log.log_no_fatal
        (L0Pass.log
           (L0Pass.iterate_pass_step L0Pass.initial_pass_state k input)).
Proof.
  intros input Hnf.
  destruct (L0Pass.converged_run_is_safe input Hnf) as [k [Hk [Hconv Hsafe]]].
  exists k. split; [| split].
  - unfold pdflatex_pass_max. lia.
  - exact Hconv.
  - exact Hsafe.
Qed.
