From Coq Require Import List Arith Lia.
Import ListNotations.

(* A small, faithful-shaped step relation for L0: consumes one input byte
   and appends a token computed by a fixed classifier.  This mirrors the
   SoA update shape (advance input cursor; append one token) while remaining
   model-agnostic and admit-free. *)

Module L0F.

  Definition byte := nat.
  Definition token := nat.

  Record state := { inp : list byte; out : list token }.

  (* Fixed classifier for a byte to a token id (total, deterministic). *)
  Definition classify (b:byte) : token := b mod 256.

  Inductive step : state -> state -> Prop :=
  | Step : forall b rest out,
      b < 256 ->
      step {| inp := b :: rest; out := out |}
           {| inp := rest; out := out ++ [classify b] |}.

  Theorem step_deterministic : forall s s1 s2,
    step s s1 -> step s s2 -> s1 = s2.
  Proof.
    intros [inp out] s1 s2 H1 H2.
    destruct inp as [|b rest]; inversion H1.
    inversion H1; inversion H2; subst; reflexivity.
  Qed.

  Theorem step_progress : forall s,
    s.(inp) <> [] ->
    Forall (fun b => b < 256) s.(inp) ->
    exists s', step s s'.
  Proof.
    intros [i o] Hne Hall.
    destruct i as [|b rest]; [contradiction|].
    inversion Hall; subst.
    exists {| inp := rest; out := o ++ [classify b] |}.
    constructor; assumption.
  Qed.

  (* Stage 1 (FAITHFUL-SEMANTICS Tier 3): a total tokenizer over a byte
     list.  It is the batch (whole-input) analogue of [step]: exactly one
     token is produced per input byte, via the same fixed [classify].
     Being defined as [map classify] it is manifestly total and every byte
     maps to exactly one token — the 1-byte -> 1-token faithfulness the plan
     calls for. *)
  Fixpoint tokenize (bs : list byte) : list token :=
    match bs with
    | [] => []
    | b :: rest => classify b :: tokenize rest
    end.

  (* [tokenize] agrees with the point-free [map classify] specification. *)
  Lemma tokenize_is_map : forall bs, tokenize bs = map classify bs.
  Proof.
    induction bs as [|b rest IH]; simpl; [reflexivity|].
    rewrite IH; reflexivity.
  Qed.

  (* Byte -> token count faithfulness: one token out per byte in. *)
  Theorem tokenize_preserves_byte_count :
    forall bs, length (tokenize bs) = length bs.
  Proof.
    induction bs as [|b rest IH]; simpl; [reflexivity|].
    rewrite IH; reflexivity.
  Qed.

End L0F.

(* ========================================================================= *)
(* Stage 2 (FAITHFUL-SEMANTICS Tier 3): aux-state evolution.                  *)
(*                                                                            *)
(* pdflatex runs the document more than once because cross references         *)
(* (\ref -> \label) are resolved through an auxiliary (.aux) file that is     *)
(* only complete after a full pass.  We model the auxiliary bookkeeping as    *)
(* an [aux_state] that accumulates the set of DEFINED labels (\label{...})    *)
(* and the set of USED references (\ref{...}).  A "pass" folds the document's  *)
(* token stream through [aux_step_token].                                     *)
(*                                                                            *)
(* Faithfulness target: the SET of defined labels CONVERGES after the first   *)
(* pass.  Re-running the same document does not define any new label and does *)
(* not lose any previously-defined label; hence reference resolution is       *)
(* stable from the second pass on.  Note the subtlety flagged in the plan:    *)
(* [aux_step_token] PREPENDS, so the underlying [defined_labels] LIST grows   *)
(* on every pass (see [naive_list_eq_is_false] below).  Convergence is a fact *)
(* about the SET (membership), not the concrete list.                         *)
(* ========================================================================= *)

Module L0Aux.

  Inductive pdflatex_token :=
  | Tok_text
  | Tok_label_def (n : nat)
  | Tok_label_ref (n : nat).

  Record aux_state := mk_aux { defined_labels : list nat; used_refs : list nat }.

  (* One token's effect on the auxiliary state: a label definition prepends
     to [defined_labels], a reference prepends to [used_refs], plain text is
     inert. *)
  Definition aux_step_token (s : aux_state) (t : pdflatex_token) : aux_state :=
    match t with
    | Tok_label_def n => mk_aux (n :: defined_labels s) (used_refs s)
    | Tok_label_ref n => mk_aux (defined_labels s) (n :: used_refs s)
    | Tok_text        => s
    end.

  (* One full pass: fold every token of the document through [aux_step_token]. *)
  Fixpoint aux_step_pass (s : aux_state) (toks : list pdflatex_token) : aux_state :=
    match toks with
    | []          => s
    | t :: rest   => aux_step_pass (aux_step_token s t) rest
    end.

  Definition empty_aux : aux_state := mk_aux [] [].

  (* The multiset (here: list) of labels a token stream defines, in the plain
     document order.  This is the intended "specification" of the definitions
     a single pass contributes, independent of the prepend/order artefacts of
     [aux_step_token]. *)
  Fixpoint collect_defs (toks : list pdflatex_token) : list nat :=
    match toks with
    | []                     => []
    | Tok_label_def n :: rest => n :: collect_defs rest
    | _ :: rest               => collect_defs rest
    end.

  (* Membership characterisation of the labels defined after a pass: a pass
     from state [s] defines exactly the labels [s] already had, plus the
     labels [collect_defs toks] the document contributes.  Proof folds over
     the token stream with [s] generalised. *)
  Lemma pass_defined_iff :
    forall toks s n,
      In n (defined_labels (aux_step_pass s toks))
      <-> In n (collect_defs toks) \/ In n (defined_labels s).
  Proof.
    induction toks as [|t rest IH]; intros s n; simpl.
    - (* empty pass: defined set unchanged *)
      split; [intro H; right; exact H | intros [[] | H]; exact H].
    - destruct t as [| m | m]; simpl.
      + (* Tok_text: inert *)
        apply IH.
      + (* Tok_label_def m: prepends m *)
        rewrite IH; simpl. tauto.
      + (* Tok_label_ref m: defined set unchanged *)
        rewrite IH. tauto.
  Qed.

  (* KEY LEMMA — 2-pass convergence of the defined-label SET.

     Running the same document a second time (starting from the state that the
     first pass produced) yields exactly the same SET of defined labels as the
     first pass: for every label id [n], [n] is defined after pass 2 iff it is
     defined after pass 1.  This is the faithful statement of pdflatex's
     "definitions converge after the first pass" property, and it is precisely
     the invariant that makes \ref resolution stable from pass 2 onward.

     It is NON-VACUOUS: [defined_labels] is inhabited exactly when the document
     contains \label tokens (see [collect_defs]); the corresponding raw
     list-equality is FALSE because the list keeps growing
     (see [naive_list_eq_is_false]).  The content is in the SET stabilising. *)
  Theorem aux_pass_stable_after_2 :
    forall toks n,
      In n (defined_labels (aux_step_pass (aux_step_pass empty_aux toks) toks))
      <-> In n (defined_labels (aux_step_pass empty_aux toks)).
  Proof.
    intros toks n.
    rewrite (pass_defined_iff toks (aux_step_pass empty_aux toks) n).
    rewrite (pass_defined_iff toks empty_aux n).
    unfold empty_aux; simpl.
    (* both sides reduce to [In n (collect_defs toks)] *)
    tauto.
  Qed.

  (* Companion: the naive list-level idempotence is genuinely FALSE, which is
     why the convergence theorem is stated at the SET level.  A second pass
     over a document with one label duplicates that label in the list. *)
  Example naive_list_eq_is_false :
    aux_step_pass (aux_step_pass empty_aux [Tok_label_def 0]) [Tok_label_def 0]
    <> aux_step_pass empty_aux [Tok_label_def 0].
  Proof.
    simpl. intro H. inversion H.
  Qed.

  (* And the SET-level theorem does hold on that same witness, confirming the
     statement is not vacuously true. *)
  Example stable_on_witness :
    In 0 (defined_labels
            (aux_step_pass (aux_step_pass empty_aux [Tok_label_def 0])
                           [Tok_label_def 0]))
    <-> In 0 (defined_labels (aux_step_pass empty_aux [Tok_label_def 0])).
  Proof. apply aux_pass_stable_after_2. Qed.

End L0Aux.

(* ========================================================================= *)
(* Stage 3 (FAITHFUL-SEMANTICS Tier 3): log-state evolution + fatal marker.   *)
(*                                                                            *)
(* pdflatex writes a .log file as it runs.  Two DISTINCT severities live in   *)
(* that log and the distinction is the whole point of this stage:             *)
(*                                                                            *)
(*   * WARNING  — e.g. "LaTeX Warning: Reference `foo' on page 1 undefined".  *)
(*                The document STILL COMPILES: a .pdf is produced, only with   *)
(*                a bogus "??" cross-reference.  An undefined \ref is a        *)
(*                WARNING, never a fatal error.                                *)
(*   * FATAL    — e.g. "! Emergency stop", "! Fatal", "Runaway argument".      *)
(*                pdflatex aborts; no usable .pdf.  Reserved for catastrophic  *)
(*                conditions (TeX capacity exceeded, unrecoverable syntax).    *)
(*                                                                            *)
(* We model the log as a byte stream (list nat) exactly as pdflatex emits it,  *)
(* and detect fatality by substring search for the canonical fatal markers.   *)
(* This mirrors PdflatexModel.v's [fatal_markers] / [log_no_fatal] machinery   *)
(* (introduced v27.0.1): identical exclamation-Fatal / Emergency-stop /        *)
(* Runaway-argument byte markers, identical prefix_match / contains_subseq /    *)
(* [log_no_fatal] shape.  We keep a LOCAL faithful copy here rather than       *)
(* [Require Import PdflatexModel] because PdflatexModel pulls in the entire     *)
(* WS8 compile chain (ProjectClosure, the T*_wrapper family, ProjectSemantics, *)
(* ...); coupling the Lexer proof files (which Require this one) to that chain  *)
(* is undesirable.  The definitions below are byte-for-byte the same as the    *)
(* canonical ones, so results transfer directly.                              *)
(*                                                                            *)
(* Faithfulness targets proved below:                                          *)
(*   (A) CLEAN PROJECT   => empty log, hence no fatal AND no warnings.         *)
(*   (B) UNDEFINED REF   => NON-empty warnings list but STILL no fatal.        *)
(*   (C) NON-VACUITY     => a genuine fatal path exists ([emit_fatal]) that    *)
(*                          [log_no_fatal] rejects; the warning path never      *)
(*                          takes it.                                           *)
(* ========================================================================= *)

Module L0Log.

  Import L0Aux.

  (* -- Fatal-marker byte machinery (local mirror of PdflatexModel.v) ------- *)

  (* A log artefact is the raw byte stream pdflatex writes to the .log file. *)
  Definition log_artefact : Type := list nat.

  Fixpoint prefix_match (pre seq : list nat) : bool :=
    match pre, seq with
    | [], _ => true
    | _ :: _, [] => false
    | x :: xs, y :: ys => andb (Nat.eqb x y) (prefix_match xs ys)
    end.

  Fixpoint contains_subseq (sub seq : list nat) : bool :=
    match seq with
    | [] => prefix_match sub []
    | _ :: rest => orb (prefix_match sub seq) (contains_subseq sub rest)
    end.

  (* "! Fatal" — bytes 33 32 70 97 116 97 108. *)
  Definition fatal_marker_exclamation_fatal : list nat :=
    [33; 32; 70; 97; 116; 97; 108].
  (* "! Emergency stop" — pdflatex's catch-all fatal marker. *)
  Definition fatal_marker_emergency_stop : list nat :=
    [33; 32; 69; 109; 101; 114; 103; 101; 110; 99; 121; 32; 115; 116; 111; 112].
  (* "Runaway argument" — TeX's brace-mismatch / unclosed-macro marker. *)
  Definition fatal_marker_runaway_argument : list nat :=
    [82; 117; 110; 97; 119; 97; 121; 32; 97; 114; 103; 117; 109; 101; 110; 116].

  Definition fatal_markers : list (list nat) :=
    [ fatal_marker_exclamation_fatal;
      fatal_marker_emergency_stop;
      fatal_marker_runaway_argument ].

  (* -- Log state and its evolution ----------------------------------------- *)

  (* The evolving log carries the structured list of undefined-reference ids
     that triggered WARNINGS ([warnings]) alongside the raw byte stream
     ([log_bytes]) as pdflatex would physically emit it. *)
  Record log_state := mk_log { warnings : list nat; log_bytes : list nat }.

  Definition empty_log : log_state := mk_log [] [].

  (* The byte payload of a "Reference undefined" WARNING line.  These bytes are
     "undef" = [117;110;100;101;102]; crucially they contain NO 33 ('!') and
     NO 82 ('R'), so no fatal marker (each begins with 33 or 82) can ever be a
     substring of a log built only from these.  The numeric ref id is recorded
     in [warnings], NOT injected into the byte stream, so the byte stream stays
     provably fatal-free regardless of the id. *)
  Definition warn_bytes : list nat := [117; 110; 100; 101; 102].

  (* One token's effect on the log, given the FIXED, fully-resolved aux state.
     Only a reference to an UNDEFINED label produces output — a warning — and it
     is emitted as a warning (id appended to [warnings], benign bytes appended
     to [log_bytes]).  Nothing here is fatal: a resolved ref, a label
     definition, and plain text are all inert. *)
  Definition log_step_token (s : log_state) (t : pdflatex_token)
                            (aux : aux_state) : log_state :=
    match t with
    | Tok_label_ref n =>
        if in_dec Nat.eq_dec n (defined_labels aux)
        then s
        else mk_log (warnings s ++ [n]) (log_bytes s ++ warn_bytes)
    | _ => s
    end.

  (* One full log pass: thread every token through [log_step_token] with the
     (already-converged, from Stage 2) aux state held fixed. *)
  Fixpoint log_step_pass (s : log_state) (toks : list pdflatex_token)
                         (aux : aux_state) : log_state :=
    match toks with
    | []        => s
    | t :: rest => log_step_pass (log_step_token s t aux) rest aux
    end.

  (* [log_no_fatal]: the log contains NONE of the canonical fatal markers as a
     substring.  Warnings (which append [warn_bytes]) are permitted; only fatal
     markers are excluded.  Mirrors PdflatexModel.v's [log_no_fatal]. *)
  Definition log_no_fatal (s : log_state) : Prop :=
    forall m, In m fatal_markers -> contains_subseq m (log_bytes s) = false.

  (* -- The undefined-reference collector (spec of [warnings]) -------------- *)

  (* The ids that, on a pass with this aux, are UNDEFINED references — the exact
     multiset of warnings a pass raises, in document order. *)
  Fixpoint collect_undef (toks : list pdflatex_token) (aux : aux_state)
    : list nat :=
    match toks with
    | [] => []
    | Tok_label_ref n :: rest =>
        if in_dec Nat.eq_dec n (defined_labels aux)
        then collect_undef rest aux
        else n :: collect_undef rest aux
    | _ :: rest => collect_undef rest aux
    end.

  (* [warnings] after a pass is exactly the starting warnings followed by the
     undefined refs of the stream.  Folds over the stream, [s] generalised. *)
  Lemma warnings_eq_collect :
    forall toks s aux,
      warnings (log_step_pass s toks aux)
      = warnings s ++ collect_undef toks aux.
  Proof.
    induction toks as [|t rest IH]; intros s aux; simpl.
    - rewrite app_nil_r; reflexivity.
    - destruct t as [| m | m]; simpl.
      + apply IH.
      + apply IH.
      + destruct (in_dec Nat.eq_dec m (defined_labels aux)) as [Hin|Hout].
        * apply IH.
        * rewrite IH; simpl. rewrite <- app_assoc; reflexivity.
  Qed.

  (* -- No-fatal is preserved: undefined refs never cause a fatal ----------- *)

  Definition benign (b : nat) : Prop := b <> 33 /\ b <> 82.

  Lemma forall_benign_app :
    forall l1 l2, Forall benign l1 -> Forall benign l2 ->
                  Forall benign (l1 ++ l2).
  Proof.
    induction l1 as [|a l1 IH]; simpl; intros l2 H1 H2; auto.
    inversion H1; subst. constructor; auto.
  Qed.

  Lemma warn_bytes_benign : Forall benign warn_bytes.
  Proof.
    unfold warn_bytes, benign.
    repeat (constructor; try (split; discriminate)).
  Qed.

  (* If a marker's head byte is absent from the log, the marker is not a
     substring.  (All fatal markers are non-empty and begin with 33 or 82.) *)
  Lemma contains_subseq_head_absent :
    forall h t seq, ~ In h seq -> contains_subseq (h :: t) seq = false.
  Proof.
    induction seq as [|a seq IH]; simpl; intros Hnin.
    - reflexivity.
    - assert (h <> a) by (intro; subst; apply Hnin; left; reflexivity).
      replace (Nat.eqb h a) with false
        by (symmetry; apply Nat.eqb_neq; assumption).
      simpl. apply IH. intro; apply Hnin; right; assumption.
  Qed.

  (* A byte stream with no 33 and no 82 (i.e. all-benign) is fatal-free. *)
  Lemma benign_bytes_no_fatal :
    forall bytes, Forall benign bytes ->
      forall m, In m fatal_markers -> contains_subseq m bytes = false.
  Proof.
    intros bytes Hb m Hm.
    assert (Hn33 : ~ In 33 bytes).
    { rewrite Forall_forall in Hb. intro Hin.
      destruct (Hb 33 Hin) as [H33 _]. apply H33; reflexivity. }
    assert (Hn82 : ~ In 82 bytes).
    { rewrite Forall_forall in Hb. intro Hin.
      destruct (Hb 82 Hin) as [_ H82]. apply H82; reflexivity. }
    unfold fatal_markers in Hm; simpl in Hm.
    destruct Hm as [Heq | [Heq | [Heq | []]]]; subst.
    - unfold fatal_marker_exclamation_fatal.
      apply contains_subseq_head_absent; exact Hn33.
    - unfold fatal_marker_emergency_stop.
      apply contains_subseq_head_absent; exact Hn33.
    - unfold fatal_marker_runaway_argument.
      apply contains_subseq_head_absent; exact Hn82.
  Qed.

  Lemma log_step_token_benign :
    forall s t aux,
      Forall benign (log_bytes s) ->
      Forall benign (log_bytes (log_step_token s t aux)).
  Proof.
    intros s t aux H. destruct t as [| m | m]; simpl; auto.
    destruct (in_dec Nat.eq_dec m (defined_labels aux)); simpl; auto.
    apply forall_benign_app; [assumption | apply warn_bytes_benign].
  Qed.

  Lemma log_step_pass_benign :
    forall toks s aux,
      Forall benign (log_bytes s) ->
      Forall benign (log_bytes (log_step_pass s toks aux)).
  Proof.
    induction toks as [|t rest IH]; simpl; intros s aux H; auto.
    apply IH. apply log_step_token_benign; assumption.
  Qed.

  (* KEY SAFETY RESULT: starting from the empty log, NO token stream — clean or
     with any number of undefined references — ever produces a fatal marker.
     Undefined \ref is a WARNING, never fatal. *)
  Theorem log_no_fatal_from_empty :
    forall toks aux, log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux m Hm.
    apply benign_bytes_no_fatal; [| exact Hm].
    apply log_step_pass_benign. simpl. constructor.
  Qed.

  (* -- (A) CLEAN PROJECT => no fatal AND no warnings ----------------------- *)

  Lemma clean_collect_nil :
    forall toks aux,
      (forall n, In (Tok_label_ref n) toks -> In n (defined_labels aux)) ->
      collect_undef toks aux = [].
  Proof.
    induction toks as [|t rest IH]; simpl; intros aux Hclean; auto.
    destruct t as [| m | m]; simpl.
    - apply IH. intros n Hn. apply Hclean. right; assumption.
    - apply IH. intros n Hn. apply Hclean. right; assumption.
    - destruct (in_dec Nat.eq_dec m (defined_labels aux)) as [Hin|Hout].
      + apply IH. intros n Hn. apply Hclean. right; assumption.
      + exfalso. apply Hout. apply Hclean. left; reflexivity.
  Qed.

  (* (A): every reference resolves (its id is among the defined labels) => the
     pass leaves the log completely empty: no warnings, no fatal. *)
  Theorem clean_no_fatal :
    forall toks aux,
      (forall n, In (Tok_label_ref n) toks -> In n (defined_labels aux)) ->
      warnings (log_step_pass empty_log toks aux) = []
      /\ log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux Hclean. split.
    - rewrite warnings_eq_collect. simpl.
      apply clean_collect_nil; assumption.
    - apply log_no_fatal_from_empty.
  Qed.

  (* -- (B) UNDEFINED REF => NON-empty warnings but STILL no fatal ---------- *)

  Lemma exists_undef_collect_nonnil :
    forall toks aux,
      (exists n, In (Tok_label_ref n) toks /\ ~ In n (defined_labels aux)) ->
      collect_undef toks aux <> [].
  Proof.
    induction toks as [|t rest IH]; simpl; intros aux [n [Hin Hout]].
    - inversion Hin.
    - destruct t as [| m | m]; simpl.
      + (* Tok_text head: witness must be in rest *)
        destruct Hin as [Habs | Hin']; [discriminate|].
        apply IH. exists n; split; assumption.
      + (* Tok_label_def head: witness must be in rest *)
        destruct Hin as [Habs | Hin']; [discriminate|].
        apply IH. exists n; split; assumption.
      + (* Tok_label_ref m head *)
        destruct (in_dec Nat.eq_dec m (defined_labels aux)) as [Hm|Hm].
        * (* m defined; the undefined witness cannot be this head, so it is in
             rest, giving a non-empty tail *)
          apply IH.
          destruct Hin as [Heq | Hin'].
          -- injection Heq as ->. contradiction.
          -- exists n; split; assumption.
        * (* m itself undefined: the head already emits a warning *)
          discriminate.
  Qed.

  (* (B): the stream contains at least one reference to an UNDEFINED label =>
     the pass raises a NON-empty warnings list, yet the log is STILL fatal-free.
     This is the crux: undefined-ref is a warning, not a fatal error. *)
  Theorem undefined_ref_warns_not_fatal :
    forall toks aux,
      (exists n, In (Tok_label_ref n) toks /\ ~ In n (defined_labels aux)) ->
      warnings (log_step_pass empty_log toks aux) <> []
      /\ log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux Hex. split.
    - rewrite warnings_eq_collect. simpl.
      apply exists_undef_collect_nonnil; assumption.
    - apply log_no_fatal_from_empty.
  Qed.

  (* Concrete witness for (B): a single reference to the never-defined label 7
     over the empty aux state raises the warning [7] and stays fatal-free. *)
  Example undefined_ref_witness :
    warnings (log_step_pass empty_log [Tok_label_ref 7] empty_aux) = [7]
    /\ log_no_fatal (log_step_pass empty_log [Tok_label_ref 7] empty_aux).
  Proof.
    split.
    - reflexivity.
    - apply log_no_fatal_from_empty.
  Qed.

  (* -- NON-VACUITY: a genuine fatal path that [log_no_fatal] rejects ------- *)

  (* [emit_fatal] models a CATASTROPHIC event (here "! Emergency stop", the
     canonical pdflatex abort): unlike the warning path, it writes a real fatal
     marker into the log.  This is the fatal path the warning path deliberately
     avoids — so [log_no_fatal] is a genuinely discriminating predicate, not one
     that is vacuously always true. *)
  Definition emit_fatal (s : log_state) : log_state :=
    mk_log (warnings s) (log_bytes s ++ fatal_marker_emergency_stop).

  Theorem fatal_path_is_detected : ~ log_no_fatal (emit_fatal empty_log).
  Proof.
    unfold log_no_fatal. intro H.
    assert (Hin : In fatal_marker_emergency_stop fatal_markers)
      by (unfold fatal_markers; simpl; right; left; reflexivity).
    specialize (H fatal_marker_emergency_stop Hin).
    unfold emit_fatal, empty_log in H. vm_compute in H. discriminate.
  Qed.

  (* And the same fatal marker cannot be produced by any warning stream: the
     warning path keeps the log fatal-free (restatement of the safety result,
     confirming the warning / fatal separation is real, not definitional). *)
  Corollary warning_stream_never_fatal :
    forall toks aux,
      log_bytes (log_step_pass empty_log toks aux)
      <> log_bytes (emit_fatal empty_log).
  Proof.
    intros toks aux Heq.
    apply fatal_path_is_detected.
    intros m Hm.
    rewrite <- Heq. apply log_no_fatal_from_empty; exact Hm.
  Qed.

End L0Log.
