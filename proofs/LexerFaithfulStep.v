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
  | Tok_label_ref (n : nat)
  (* Stage 6 (DEEPENING): a genuinely UNRECOVERABLE construct — e.g. an
     unresolved \input to a file absent from the project, "! Emergency
     stop" / TeX-capacity-exceeded.  Unlike an undefined \ref (a mere
     warning), this token makes the pass EMIT A FATAL MARKER into the
     log (see [L0Log.log_step_token]).  Its presence is exactly what
     project well-typedness (T2 closure) rules out, so [log_no_fatal]
     is now FALSIFIABLE BY THE PASS on a reachable input, not just by an
     artificial [emit_fatal]. *)
  | Tok_fatal.

  Record aux_state := mk_aux { defined_labels : list nat; used_refs : list nat }.

  (* One token's effect on the auxiliary state: a label definition prepends
     to [defined_labels], a reference prepends to [used_refs], plain text is
     inert. *)
  Definition aux_step_token (s : aux_state) (t : pdflatex_token) : aux_state :=
    match t with
    | Tok_label_def n => mk_aux (n :: defined_labels s) (used_refs s)
    | Tok_label_ref n => mk_aux (defined_labels s) (n :: used_refs s)
    | Tok_text        => s
    | Tok_fatal       => s   (* inert on the aux bookkeeping *)
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
    - destruct t as [| m | m |]; simpl.
      + (* Tok_text: inert *)
        apply IH.
      + (* Tok_label_def m: prepends m *)
        rewrite IH; simpl. tauto.
      + (* Tok_label_ref m: defined set unchanged *)
        rewrite IH. tauto.
      + (* Tok_fatal: inert on aux *)
        apply IH.
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
    (* Stage 6 (DEEPENING): the fatal transition.  A [Tok_fatal] writes
       a REAL fatal marker ("! Emergency stop") into the byte stream, so
       a document containing one drives [log_no_fatal] to FALSE through
       the ordinary pass (see [fatal_token_is_fatal]).  This is the
       genuinely-reachable fatal path the warning path avoids. *)
    | Tok_fatal =>
        mk_log (warnings s) (log_bytes s ++ fatal_marker_emergency_stop)
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

  (* -- The genuine safety hypothesis (Stage 6 DEEPENING) -------------------- *)

  (* A token is non-fatal unless it is [Tok_fatal]. *)
  Definition tok_not_fatal (t : pdflatex_token) : Prop := t <> Tok_fatal.

  (* [no_fatal_tokens toks]: the document contains NO unrecoverable
     construct.  This is the REAL, FALSIFIABLE hypothesis under which the
     pass is fatal-free — it is NOT universal (the singleton [Tok_fatal]
     stream fails it, see [fatal_token_is_fatal]), unlike the decorative
     [bounded_labels].  Project well-typedness (T2 closure) is what
     establishes it for a real project (see [PdflatexModel.project_tokens]
     / [project_closed_no_fatal_tokens]). *)
  Definition no_fatal_tokens (toks : list pdflatex_token) : Prop :=
    Forall tok_not_fatal toks.

  Lemma no_fatal_tokens_nil : no_fatal_tokens [].
  Proof. constructor. Qed.

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
    - destruct t as [| m | m |]; simpl.
      + apply IH.
      + apply IH.
      + destruct (in_dec Nat.eq_dec m (defined_labels aux)) as [Hin|Hout].
        * apply IH.
        * rewrite IH; simpl. rewrite <- app_assoc; reflexivity.
      + (* Tok_fatal: writes bytes but leaves [warnings] unchanged *)
        rewrite IH; reflexivity.
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
      tok_not_fatal t ->
      Forall benign (log_bytes s) ->
      Forall benign (log_bytes (log_step_token s t aux)).
  Proof.
    intros s t aux Hnf H. destruct t as [| m | m |]; simpl.
    - exact H.
    - exact H.
    - destruct (in_dec Nat.eq_dec m (defined_labels aux)); simpl.
      + exact H.
      + apply forall_benign_app; [exact H | apply warn_bytes_benign].
    - (* Tok_fatal excluded by [tok_not_fatal] *)
      exfalso. apply Hnf. reflexivity.
  Qed.

  Lemma log_step_pass_benign :
    forall toks s aux,
      no_fatal_tokens toks ->
      Forall benign (log_bytes s) ->
      Forall benign (log_bytes (log_step_pass s toks aux)).
  Proof.
    induction toks as [|t rest IH]; simpl; intros s aux Hnf H; auto.
    inversion Hnf as [| t' rest' Ht Hrest]; subst.
    apply IH; [exact Hrest |].
    apply log_step_token_benign; [exact Ht | exact H].
  Qed.

  (* KEY SAFETY RESULT: starting from the empty log, NO token stream — clean or
     with any number of undefined references — ever produces a fatal marker.
     Undefined \ref is a WARNING, never fatal. *)
  Theorem log_no_fatal_from_empty :
    forall toks aux,
      no_fatal_tokens toks ->
      log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux Hnf m Hm.
    apply benign_bytes_no_fatal; [| exact Hm].
    apply log_step_pass_benign; [exact Hnf |]. simpl. constructor.
  Qed.

  (* -- (A) CLEAN PROJECT => no fatal AND no warnings ----------------------- *)

  Lemma clean_collect_nil :
    forall toks aux,
      (forall n, In (Tok_label_ref n) toks -> In n (defined_labels aux)) ->
      collect_undef toks aux = [].
  Proof.
    induction toks as [|t rest IH]; simpl; intros aux Hclean; auto.
    destruct t as [| m | m |]; simpl.
    - apply IH. intros n Hn. apply Hclean. right; assumption.
    - apply IH. intros n Hn. apply Hclean. right; assumption.
    - destruct (in_dec Nat.eq_dec m (defined_labels aux)) as [Hin|Hout].
      + apply IH. intros n Hn. apply Hclean. right; assumption.
      + exfalso. apply Hout. apply Hclean. left; reflexivity.
    - apply IH. intros n Hn. apply Hclean. right; assumption.
  Qed.

  (* (A): every reference resolves (its id is among the defined labels) => the
     pass leaves the log completely empty: no warnings, no fatal. *)
  Theorem clean_no_fatal :
    forall toks aux,
      no_fatal_tokens toks ->
      (forall n, In (Tok_label_ref n) toks -> In n (defined_labels aux)) ->
      warnings (log_step_pass empty_log toks aux) = []
      /\ log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux Hnf Hclean. split.
    - rewrite warnings_eq_collect. simpl.
      apply clean_collect_nil; assumption.
    - apply log_no_fatal_from_empty; exact Hnf.
  Qed.

  (* -- (B) UNDEFINED REF => NON-empty warnings but STILL no fatal ---------- *)

  Lemma exists_undef_collect_nonnil :
    forall toks aux,
      (exists n, In (Tok_label_ref n) toks /\ ~ In n (defined_labels aux)) ->
      collect_undef toks aux <> [].
  Proof.
    induction toks as [|t rest IH]; simpl; intros aux [n [Hin Hout]].
    - inversion Hin.
    - destruct t as [| m | m |]; simpl.
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
      + (* Tok_fatal head: witness must be in rest *)
        destruct Hin as [Habs | Hin']; [discriminate|].
        apply IH. exists n; split; assumption.
  Qed.

  (* Converse of [exists_undef_collect_nonnil] at the element level: every id
     collected as a warning is a genuine reference to a label undefined in the
     (fixed) aux state.  Used to prove warning-faithfulness (Stage 6). *)
  Lemma collect_undef_in :
    forall toks aux m,
      In m (collect_undef toks aux) ->
      In (Tok_label_ref m) toks /\ ~ In m (defined_labels aux).
  Proof.
    induction toks as [|t rest IH]; simpl; intros aux m Hin.
    - inversion Hin.
    - destruct t as [| a | a |]; simpl in Hin.
      + destruct (IH aux m Hin) as [H1 H2]. split; [right; assumption | assumption].
      + destruct (IH aux m Hin) as [H1 H2]. split; [right; assumption | assumption].
      + destruct (in_dec Nat.eq_dec a (defined_labels aux)) as [Hd|Hd].
        * destruct (IH aux m Hin) as [H1 H2]. split; [right; assumption | assumption].
        * destruct Hin as [Heq | Hin'].
          -- subst. split; [left; reflexivity | assumption].
          -- destruct (IH aux m Hin') as [H1 H2].
             split; [right; assumption | assumption].
      + destruct (IH aux m Hin) as [H1 H2]. split; [right; assumption | assumption].
  Qed.

  (* (B): the stream contains at least one reference to an UNDEFINED label =>
     the pass raises a NON-empty warnings list, yet the log is STILL fatal-free.
     This is the crux: undefined-ref is a warning, not a fatal error. *)
  Theorem undefined_ref_warns_not_fatal :
    forall toks aux,
      no_fatal_tokens toks ->
      (exists n, In (Tok_label_ref n) toks /\ ~ In n (defined_labels aux)) ->
      warnings (log_step_pass empty_log toks aux) <> []
      /\ log_no_fatal (log_step_pass empty_log toks aux).
  Proof.
    intros toks aux Hnf Hex. split.
    - rewrite warnings_eq_collect. simpl.
      apply exists_undef_collect_nonnil; assumption.
    - apply log_no_fatal_from_empty; exact Hnf.
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
      repeat constructor; discriminate.
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

  (* STAGE 6 DEEPENING — the fatal path is REACHABLE BY THE ORDINARY PASS.
     Unlike [emit_fatal] (an artificial constructor), this shows that a
     *document* — the singleton token stream [Tok_fatal] — drives the real
     [log_step_pass] to a state that [log_no_fatal] REJECTS.  Hence
     [no_fatal_tokens] is a genuine, falsifiable hypothesis and
     [log_no_fatal] is non-vacuous: the pass itself can produce a fatal
     log. *)
  Theorem fatal_token_is_fatal :
    ~ log_no_fatal (log_step_pass empty_log [Tok_fatal] empty_aux).
  Proof.
    unfold log_no_fatal. intro H.
    assert (Hin : In fatal_marker_emergency_stop fatal_markers)
      by (unfold fatal_markers; simpl; right; left; reflexivity).
    specialize (H fatal_marker_emergency_stop Hin).
    vm_compute in H. discriminate.
  Qed.

  (* The singleton [Tok_fatal] stream also FAILS [no_fatal_tokens] — the
     hypothesis genuinely excludes some inputs (contrast: [bounded_labels]
     holds for every input). *)
  Theorem fatal_token_not_no_fatal :
    ~ no_fatal_tokens [Tok_fatal].
  Proof.
    intro H. inversion H as [| t' rest' Ht _]. apply Ht. reflexivity.
  Qed.

  (* And the same fatal marker cannot be produced by any warning stream: the
     warning path keeps the log fatal-free (restatement of the safety result,
     confirming the warning / fatal separation is real, not definitional). *)
  Corollary warning_stream_never_fatal :
    forall toks aux,
      no_fatal_tokens toks ->
      log_bytes (log_step_pass empty_log toks aux)
      <> log_bytes (emit_fatal empty_log).
  Proof.
    intros toks aux Hnf Heq.
    apply fatal_path_is_detected.
    intros m Hm.
    rewrite <- Heq. apply log_no_fatal_from_empty; [exact Hnf | exact Hm].
  Qed.

End L0Log.

From Coq Require Import Bool.

(* ========================================================================= *)
(* Stage 4 (FAITHFUL-SEMANTICS Tier 3): the operational pdflatex pass.        *)
(*                                                                            *)
(* A single pdflatex invocation (a "pass") re-reads the whole document, folds *)
(* the token stream through the aux bookkeeping (Stage 2) and the log         *)
(* bookkeeping (Stage 3, threaded against the aux state produced THIS pass),  *)
(* and records whether the aux state CHANGED — the signal pdflatex itself     *)
(* uses ("Rerun to get cross-references right").  Convergence is exactly      *)
(* "the aux state did not change this pass".                                  *)
(*                                                                            *)
(* The document is carried as the already-tokenised stream                    *)
(* [input : list pdflatex_token]; tokenisation is the upstream Stage-1        *)
(* concern (L0F / the L2 tokenizer) and is not re-done here.  Each pass       *)
(* re-folds the SAME [input], mirroring pdflatex re-reading the .tex file.    *)
(*                                                                            *)
(* CONVERGENCE is compared at the SET (membership) level via [aux_eq], not    *)
(* the raw list: as Stage 2 established ([naive_list_eq_is_false]), the        *)
(* underlying [defined_labels] LIST grows on every pass (prepend), so a        *)
(* list-equality [converged] flag would NEVER fire.  [aux_eq] compares the    *)
(* defined-label SETs, which is what actually drives \ref resolution.         *)
(* ========================================================================= *)

Module L0Pass.

  Import L0Aux.
  Import L0Log.

  (* -- Set-level equality of aux states (decidable, on defined_labels) ----- *)

  Definition mem_bool (x : nat) (l : list nat) : bool :=
    if in_dec Nat.eq_dec x l then true else false.

  Lemma mem_bool_true : forall x l, mem_bool x l = true <-> In x l.
  Proof.
    intros x l. unfold mem_bool.
    destruct (in_dec Nat.eq_dec x l) as [Hin|Hout].
    - split; intro H; [exact Hin | reflexivity].
    - split; intro H; [discriminate | contradiction].
  Qed.

  Definition subset_bool (l1 l2 : list nat) : bool :=
    forallb (fun x => mem_bool x l2) l1.

  Lemma subset_bool_spec :
    forall l1 l2, subset_bool l1 l2 = true <-> (forall x, In x l1 -> In x l2).
  Proof.
    intros l1 l2. unfold subset_bool. rewrite forallb_forall.
    split; intros H x Hx; apply mem_bool_true; apply H; exact Hx.
  Qed.

  (* [aux_eq a b] is true iff [a] and [b] define exactly the same SET of
     labels.  This is the faithful convergence test: it ignores list order and
     multiplicity (the prepend artefacts) and looks only at membership. *)
  Definition aux_eq (a b : aux_state) : bool :=
    andb (subset_bool (defined_labels a) (defined_labels b))
         (subset_bool (defined_labels b) (defined_labels a)).

  Lemma aux_eq_true :
    forall a b,
      aux_eq a b = true
      <-> (forall n, In n (defined_labels a) <-> In n (defined_labels b)).
  Proof.
    intros a b. unfold aux_eq. rewrite andb_true_iff.
    rewrite !subset_bool_spec. split.
    - intros [H1 H2] n. split; [apply H1 | apply H2].
    - intros H. split; intros x Hx; apply H; exact Hx.
  Qed.

  (* -- Pass state + one operational pass ----------------------------------- *)

  Record pass_state := mk_pass {
    pass_count : nat;
    aux : aux_state;
    log : log_state;
    converged : bool
  }.

  Definition initial_pass_state : pass_state :=
    mk_pass 0 empty_aux empty_log false.

  (* One pdflatex pass: fold the token stream through the aux bookkeeping,
     then through the log bookkeeping (against the freshly-produced aux), bump
     the pass counter, and set [converged] iff the aux SET is unchanged. *)
  Definition pdflatex_pass_step (s : pass_state) (input : list pdflatex_token)
      : pass_state :=
    let new_aux := aux_step_pass (aux s) input in
    let new_log := log_step_pass (log s) input new_aux in
    mk_pass (S (pass_count s)) new_aux new_log (aux_eq (aux s) new_aux).

  (* [k] consecutive passes over the same document. *)
  Fixpoint iterate_pass_step (s : pass_state) (k : nat)
                             (input : list pdflatex_token) : pass_state :=
    match k with
    | 0    => s
    | S k' => iterate_pass_step (pdflatex_pass_step s input) k' input
    end.

  (* -- Stage-4 safety: the pass never manufactures a fatal marker ---------- *)

  Lemma pass_preserves_benign :
    forall s input,
      no_fatal_tokens input ->
      Forall benign (log_bytes (log s)) ->
      Forall benign (log_bytes (log (pdflatex_pass_step s input))).
  Proof.
    intros s input Hnf H. unfold pdflatex_pass_step; simpl.
    apply log_step_pass_benign; [exact Hnf | exact H].
  Qed.

  Lemma iterate_preserves_benign :
    forall k s input,
      no_fatal_tokens input ->
      Forall benign (log_bytes (log s)) ->
      Forall benign (log_bytes (log (iterate_pass_step s k input))).
  Proof.
    induction k as [|k IH]; intros s input Hnf H; simpl.
    - exact H.
    - apply IH; [exact Hnf |]. apply pass_preserves_benign; [exact Hnf | exact H].
  Qed.

  (* From the initial (empty-log) state, no number of passes over a
     FATAL-FREE document ([no_fatal_tokens]) ever produces a fatal marker:
     the Stage-3 warning/fatal separation is preserved by the Stage-4 pass
     iteration.  This is now CONDITIONAL on [no_fatal_tokens] — a document
     containing [Tok_fatal] genuinely reaches a fatal log (see
     [L0Log.fatal_token_is_fatal]). *)
  Theorem pass_iteration_no_fatal :
    forall k input,
      no_fatal_tokens input ->
      log_no_fatal (log (iterate_pass_step initial_pass_state k input)).
  Proof.
    intros k input Hnf. unfold log_no_fatal. intros m Hm.
    apply benign_bytes_no_fatal; [| exact Hm].
    apply iterate_preserves_benign; [exact Hnf |].
    unfold initial_pass_state; simpl. constructor.
  Qed.

  (* ======================================================================= *)
  (* Stage 5 (FAITHFUL-SEMANTICS Tier 3): convergence in at most two passes.  *)
  (*                                                                          *)
  (* The heart of the pdflatex "run twice" folklore, proved faithfully: the   *)
  (* defined-label SET reaches a fixpoint after the FIRST pass, so the SECOND  *)
  (* pass detects no change and [converged] fires.  The bound 2 is REAL — it  *)
  (* is not [k] left unconstrained, and it is TIGHT: [bound_two_is_tight]      *)
  (* exhibits a document that is NOT converged after one pass but IS after     *)
  (* two.  The [converged=true] conclusion is the ACTUAL [aux_eq] flag         *)
  (* computed by the pass, reflecting genuine aux stabilisation (Stage 2).    *)
  (* ======================================================================= *)

  (* General set-stability: for ANY starting aux state, a second identical
     pass adds no new defined labels and drops none — the defined-label SET is
     already stable after the first pass.  Pure consequence of Stage 2's
     [pass_defined_iff]; needs no fresh-start hypothesis. *)
  Lemma pass_defined_set_stable :
    forall input s n,
      In n (defined_labels (aux_step_pass (aux_step_pass s input) input))
      <-> In n (defined_labels (aux_step_pass s input)).
  Proof.
    intros input s n.
    rewrite (pass_defined_iff input (aux_step_pass s input) n).
    rewrite (pass_defined_iff input s n).
    tauto.
  Qed.

  (* RESIDUAL-3 CLOSURE (v27.1.38): the old [bounded_labels] /
     [bounded_labels_holds] pair was a UNIVERSALLY-TRUE decoration — it was
     the hypothesis of the convergence theorem yet [intros ... _]'d away and
     discharged for EVERY input by [bounded_labels_holds].  It has been
     REMOVED.  The ≤2-pass convergence genuinely needs no finite-label bound
     (it holds for every finite token list), so the theorem below is now
     UNCONDITIONAL.  The single genuinely-falsifiable hypothesis on the pass
     is [no_fatal_tokens] (the [Tok_fatal] singleton fails it — see
     [L0Log.fatal_token_not_no_fatal]), which is what [converged_run_is_safe]
     and the WS8 capstone actually load-bear on.  No decorative predicate
     survives on the convergence path. *)

  (* Two passes from any state converge: the [aux_eq] flag is exactly the
     defined-label SET being stable after the first pass. *)
  Lemma converged_at_two :
    forall (input : list pdflatex_token) (s0 : pass_state),
      (iterate_pass_step s0 2 input).(converged) = true.
  Proof.
    intros input s0.
    simpl. unfold pdflatex_pass_step; simpl.
    apply (proj2 (aux_eq_true _ _)).
    intro n. symmetry. apply pass_defined_set_stable.
  Qed.

  (* THE CONVERGENCE THEOREM (unconditional).  For any document and any
     starting pass state, at most 2 passes reach [converged = true].  The
     witness is exactly k = 2, and the [converged] flag is the real [aux_eq]
     test — true because the defined-label set stabilised after the first
     pass (Stage 2 / [pass_defined_set_stable]). *)
  Theorem pdflatex_pass_converges_bounded :
    forall (input : list pdflatex_token) (s0 : pass_state),
      exists k, k <= 2 /\ (iterate_pass_step s0 k input).(converged) = true.
  Proof.
    intros input s0.
    exists 2. split; [apply le_n | apply converged_at_two].
  Qed.

  (* The ≤2 bound is TIGHT and MEANINGFUL: a one-label document is NOT
     converged after a single pass (the empty starting set differs from the
     one-element set) but IS converged after the second.  So [converged]
     genuinely tracks aux change and k = 1 does not suffice in general. *)
  Example bound_two_is_tight :
    (iterate_pass_step initial_pass_state 1 [Tok_label_def 0]).(converged)
      = false
    /\ (iterate_pass_step initial_pass_state 2 [Tok_label_def 0]).(converged)
      = true.
  Proof. split; vm_compute; reflexivity. Qed.

  (* And convergence composes with the Stage-4 safety guarantee: a
     FATAL-FREE ([no_fatal_tokens]) document's converged run is also
     fatal-free.  Convergence itself needs NO hypothesis (the ≤2 bound is
     unconditional); the GENUINE, falsifiable hypothesis is
     [no_fatal_tokens].  This is the honest resolution of the old
     decorative [bounded_labels]. *)
  Corollary converged_run_is_safe :
    forall input,
      no_fatal_tokens input ->
      exists k,
        k <= 2 /\
        (iterate_pass_step initial_pass_state k input).(converged) = true /\
        log_no_fatal (log (iterate_pass_step initial_pass_state k input)).
  Proof.
    intros input Hnf.
    destruct (pdflatex_pass_converges_bounded input initial_pass_state)
      as [k [Hk Hconv]].
    exists k. repeat split; [exact Hk | exact Hconv |].
    apply pass_iteration_no_fatal; exact Hnf.
  Qed.

  (* ======================================================================= *)
  (* Stage 6 (DEEPENING): the converged run's WARNINGS faithfully reflect the *)
  (* document's UNRESOLVED cross-references — the log warns IFF the document   *)
  (* references a label it never defines.  This makes the Stage-3 warning path *)
  (* (undefined \ref => non-empty warnings, still fatal-free) LOAD-BEARING in  *)
  (* the WS8 capstone: the capstone now states cross-references resolve/warn   *)
  (* faithfully over the project's REAL token stream.                         *)
  (* ======================================================================= *)

  (* One pass appends exactly the undefined refs (against the pass's own aux)
     to the running warnings. *)
  Lemma warnings_step :
    forall s input,
      warnings (log (pdflatex_pass_step s input))
      = warnings (log s) ++ collect_undef input (aux_step_pass (aux s) input).
  Proof.
    intros s input. unfold pdflatex_pass_step; cbn [log aux].
    apply warnings_eq_collect.
  Qed.

  Lemma aux_after_step :
    forall s input, aux (pdflatex_pass_step s input) = aux_step_pass (aux s) input.
  Proof. intros s input. reflexivity. Qed.

  Lemma iterate_two_unfold :
    forall s input,
      iterate_pass_step s 2 input
      = pdflatex_pass_step (pdflatex_pass_step s input) input.
  Proof. reflexivity. Qed.

  (* Membership bridges: what the aux defines after one / two passes from the
     empty state is exactly the document's [collect_defs] SET. *)
  Lemma defined_after_pass1 :
    forall input n,
      In n (defined_labels (aux_step_pass empty_aux input))
      <-> In n (collect_defs input).
  Proof.
    intros input n. rewrite (pass_defined_iff input empty_aux n).
    unfold empty_aux; simpl. tauto.
  Qed.

  Lemma defined_after_pass2 :
    forall input n,
      In n (defined_labels (aux_step_pass (aux_step_pass empty_aux input) input))
      <-> In n (collect_defs input).
  Proof.
    intros input n.
    rewrite (pass_defined_set_stable input empty_aux n).
    apply defined_after_pass1.
  Qed.

  (* Warnings after the (converged) two-pass run, in closed form: the
     undefined refs of pass 1 followed by those of pass 2. *)
  Lemma warnings_iterate_two :
    forall input,
      warnings (log (iterate_pass_step initial_pass_state 2 input))
      = collect_undef input (aux_step_pass empty_aux input)
        ++ collect_undef input
             (aux_step_pass (aux_step_pass empty_aux input) input).
  Proof.
    intros input.
    rewrite iterate_two_unfold.
    rewrite warnings_step.
    rewrite warnings_step.
    rewrite aux_after_step.
    (* aux initial_pass_state = empty_aux, warnings (log initial) = [] *)
    cbn [warnings log initial_pass_state aux empty_log].
    reflexivity.
  Qed.

  (* THE WARNING-FAITHFULNESS THEOREM: the two-pass run raises a warning IFF
     the document contains a reference to a never-defined label.  Both
     directions are genuine — the [<-] exercises the warning path, the [->]
     shows warnings arise ONLY from real unresolved refs. *)
  Theorem warns_iff_unresolved_two :
    forall input,
      warnings (log (iterate_pass_step initial_pass_state 2 input)) <> []
      <-> (exists n, In (Tok_label_ref n) input
                     /\ ~ In n (collect_defs input)).
  Proof.
    intros input. rewrite warnings_iterate_two. split.
    - intros Hne.
      destruct (collect_undef input (aux_step_pass empty_aux input))
        as [|a A'] eqn:EA.
      + (* pass-1 undef set empty; the non-emptiness is in pass 2 *)
        simpl in Hne.
        destruct (collect_undef input
                    (aux_step_pass (aux_step_pass empty_aux input) input))
          as [|b B'] eqn:EB; [contradiction Hne; reflexivity|].
        assert (Hin : In b (collect_undef input
                       (aux_step_pass (aux_step_pass empty_aux input) input)))
          by (rewrite EB; left; reflexivity).
        apply collect_undef_in in Hin. destruct Hin as [Href Hnd].
        exists b. split; [exact Href |].
        intro Hc. apply Hnd. apply defined_after_pass2. exact Hc.
      + (* pass-1 already has an undef ref *)
        assert (Hin : In a (collect_undef input (aux_step_pass empty_aux input)))
          by (rewrite EA; left; reflexivity).
        apply collect_undef_in in Hin. destruct Hin as [Href Hnd].
        exists a. split; [exact Href |].
        intro Hc. apply Hnd. apply defined_after_pass1. exact Hc.
    - intros [n [Href Hnd]].
      assert (Hnd1 : ~ In n (defined_labels (aux_step_pass empty_aux input))).
      { intro Hc. apply Hnd. apply defined_after_pass1. exact Hc. }
      assert (HA : collect_undef input (aux_step_pass empty_aux input) <> [])
        by (apply exists_undef_collect_nonnil; exists n; split; assumption).
      intro Happ. apply HA.
      destruct (collect_undef input (aux_step_pass empty_aux input)); auto.
      discriminate Happ.
  Qed.

End L0Pass.
