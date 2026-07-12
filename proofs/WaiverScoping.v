(** WaiverScoping — v27 "waiver scoping correctness" proof family
    (specs/v27/V27_REPO_EXACT_MASTER_SPEC.md §7 "Required new proof families").

    WS9 shipped runtime-only in [latex-parse/src/editorial_policy.ml].  This
    file formalises the CORE invariants of that runtime's waiver application in
    a small, faithful, admit-free operational model — mirroring the style of
    [proofs/LexerFaithfulStep.v] (a compact model plus Qed soundness theorems,
    0 admits, 0 axioms).

    Runtime shape mirrored ([editorial_policy.ml]):
    - a FINDING is rule-aggregated: it carries a rule id and the file it was
      raised in ([Validators.result].id + the [~file] argument to [apply]);
    - a WAIVER carries a rule id, an OPTIONAL file glob, and a REQUIRED reason
      ([type waiver]); [waiver_matches_file] treats [None] as "any file";
    - [apply] keeps a finding unless the FIRST waiver whose rule id matches AND
      whose file glob (if any) matches suppresses it, and emits exactly one
      audit record per suppressed finding (so suppression is never silent).

    We prove, all by [Qed] (checked [Closed under the global context]):
    (a) SOUNDNESS         — every suppressed finding is matched by some waiver;
    (b) COMPLETENESS      — every finding a waiver matches is suppressed;
    (c) NON-SILENCE       — audit records correspond exactly, one per suppressed
                            finding (so suppression count = audit count), and
                            every audit record carries a real waiver's reason;
    (d) NO-MATCH NO-OP    — a waiver matching no finding suppresses nothing.
    Plus a concrete non-vacuity witness where one finding IS and one is NOT
    suppressed. *)

From Coq Require Import List String Arith Lia.
Import ListNotations.
(* NB: we do NOT [Open Scope string_scope] — that would shadow [List.length]
   with [String.length].  The only string literal below is annotated [%string]. *)

Module WaiverModel.

  (* Rule ids and file ids modelled as nats (opaque identifiers). *)
  Definition rule_id := nat.
  Definition file_id := nat.

  (* A finding is rule-aggregated: a rule id together with the file it fired in.
     Mirrors [Validators.result.id] plus the [~file] passed to [apply]. *)
  Record finding := { f_rule : rule_id; f_file : file_id }.

  (* A waiver: a rule id, an OPTIONAL file glob (modelled faithfully as an
     OPTIONAL decidable file matcher — [None] = "any file", exactly the
     [w_file_glob = None] case), and a REQUIRED reason string. *)
  Record waiver := {
    w_rule   : rule_id;
    w_file   : option (file_id -> bool);
    w_reason : string
  }.

  (* An audit record: which finding was suppressed and under what reason.
     Mirrors [audit_record] (a_rule/a_count/a_scope elided; the load-bearing
     accountability content is the suppressed finding + the waiver's reason). *)
  Record audit := { a_finding : finding; a_reason : string }.

  (* [waiver_matches w f]: rule ids agree AND the file glob (if any) matches the
     finding's file.  Mirrors the [apply] predicate
     [w.w_rule = r.id && waiver_matches_file w file]. *)
  Definition waiver_matches (w : waiver) (f : finding) : bool :=
    Nat.eqb (w_rule w) (f_rule f)
    && (match w_file w with
        | None   => true
        | Some g => g (f_file f)
        end).

  (* The FIRST matching waiver, if any — mirrors [List.find_opt ... p.waivers]. *)
  Definition find_waiver (ws : list waiver) (f : finding) : option waiver :=
    find (fun w => waiver_matches w f) ws.

  (* Whether a finding is suppressed at all. *)
  Definition matched_b (ws : list waiver) (f : finding) : bool :=
    match find_waiver ws f with
    | Some _ => true
    | None   => false
    end.

  (* [apply_waivers ws fs] = (kept findings, audit records).  Faithful to
     [Editorial_policy.apply]: keep a finding unless some waiver matches it, in
     which case drop it and emit one audit record carrying that waiver's
     reason. *)
  Fixpoint apply_waivers (ws : list waiver) (fs : list finding)
    : list finding * list audit :=
    match fs with
    | [] => ([], [])
    | f :: rest =>
        let '(kept, aud) := apply_waivers ws rest in
        match find_waiver ws f with
        | Some w => (kept, {| a_finding := f; a_reason := w_reason w |} :: aud)
        | None   => (f :: kept, aud)
        end
    end.

  Definition kept_of  (ws : list waiver) (fs : list finding) : list finding :=
    fst (apply_waivers ws fs).
  Definition audit_of (ws : list waiver) (fs : list finding) : list audit :=
    snd (apply_waivers ws fs).

  (* The findings the model actually reports as suppressed (the audit trail). *)
  Definition suppressed_of (ws : list waiver) (fs : list finding) : list finding :=
    map a_finding (audit_of ws fs).

  (* ── Structural characterisations of [apply_waivers] ─────────────────── *)

  (* Combined structural spec: both output components are the corresponding
     [filter]s of the input.  Proved together so the induction hypothesis
     carries both facts. *)
  Lemma apply_waivers_spec : forall ws fs,
    fst (apply_waivers ws fs) = filter (fun f => negb (matched_b ws f)) fs /\
    map a_finding (snd (apply_waivers ws fs)) = filter (fun f => matched_b ws f) fs.
  Proof.
    intros ws fs. induction fs as [|a fs IH]; [split; reflexivity|].
    simpl. destruct (apply_waivers ws fs) as [kept aud] eqn:Hrec.
    simpl in IH. destruct IH as [IH1 IH2].
    unfold matched_b, find_waiver.
    destruct (find (fun w => waiver_matches w a) ws) eqn:E; simpl.
    - split; [exact IH1 | rewrite IH2; reflexivity].
    - split; [rewrite IH1; reflexivity | exact IH2].
  Qed.

  Lemma kept_is_filter : forall ws fs,
    kept_of ws fs = filter (fun f => negb (matched_b ws f)) fs.
  Proof. intros ws fs. apply (proj1 (apply_waivers_spec ws fs)). Qed.

  Lemma audit_is_filter : forall ws fs,
    map a_finding (audit_of ws fs) = filter (fun f => matched_b ws f) fs.
  Proof. intros ws fs. apply (proj2 (apply_waivers_spec ws fs)). Qed.

  (* ── (a) SOUNDNESS ───────────────────────────────────────────────────
     Every suppressed finding is matched by some waiver that is actually in the
     policy — no finding is suppressed without a matching waiver. *)
  Theorem waiver_soundness : forall ws fs f,
    In f (suppressed_of ws fs) ->
    exists w, In w ws /\ waiver_matches w f = true.
  Proof.
    intros ws fs f Hin.
    unfold suppressed_of in Hin. rewrite audit_is_filter in Hin.
    apply filter_In in Hin. destruct Hin as [_ Hmatch].
    unfold matched_b, find_waiver in Hmatch.
    destruct (find (fun w => waiver_matches w f) ws) eqn:E; [|discriminate].
    apply find_some in E. destruct E as [Hin_w Hpred].
    exists w. split; assumption.
  Qed.

  (* ── (b) COMPLETENESS ────────────────────────────────────────────────
     Every finding that some in-policy waiver matches IS suppressed (dropped
     from [kept] and present in the audit trail). *)
  Theorem waiver_completeness : forall ws fs f w,
    In w ws -> waiver_matches w f = true -> In f fs ->
    In f (suppressed_of ws fs).
  Proof.
    intros ws fs f w Hin_w Hmatch Hin_f.
    unfold suppressed_of. rewrite audit_is_filter.
    apply filter_In. split; [exact Hin_f|].
    unfold matched_b, find_waiver.
    destruct (find (fun w0 => waiver_matches w0 f) ws) eqn:E; [reflexivity|].
    assert (Hfw : waiver_matches w f = false)
      by (exact (@find_none _ (fun w0 => waiver_matches w0 f) ws E w Hin_w)).
    rewrite Hmatch in Hfw. discriminate.
  Qed.

  (* A matched finding never survives into the kept output. *)
  Corollary matched_not_kept : forall ws fs f w,
    In w ws -> waiver_matches w f = true ->
    ~ In f (kept_of ws fs).
  Proof.
    intros ws fs f w Hin_w Hmatch Hkept.
    rewrite kept_is_filter in Hkept.
    apply filter_In in Hkept. destruct Hkept as [_ Hneg].
    unfold matched_b, find_waiver in Hneg.
    destruct (find (fun w0 => waiver_matches w0 f) ws) eqn:E.
    - simpl in Hneg. discriminate.
    - assert (Hfw : waiver_matches w f = false)
        by (exact (@find_none _ (fun w0 => waiver_matches w0 f) ws E w Hin_w)).
      rewrite Hmatch in Hfw. discriminate.
  Qed.

  (* ── (c) NON-SILENCE / audit-completeness ────────────────────────────
     The audit trail lists EXACTLY the suppressed findings — one record per
     suppressed finding, so nothing is suppressed silently. *)
  Theorem waiver_non_silence : forall ws fs,
    map a_finding (audit_of ws fs) = filter (fun f => matched_b ws f) fs.
  Proof. exact audit_is_filter. Qed.

  (* Corollary: suppression count = audit count (no silent drop, no phantom
     record). *)
  Theorem waiver_audit_count : forall ws fs,
    List.length (audit_of ws fs)
    = List.length (filter (fun f => matched_b ws f) fs).
  Proof.
    intros ws fs.
    rewrite <- (List.map_length a_finding (audit_of ws fs)).
    rewrite audit_is_filter. reflexivity.
  Qed.

  (* Every audit record's reason is the reason of some in-policy waiver — the
     audit trail is accountable (each suppression cites a real waiver). *)
  Lemma audit_reason_from_waiver : forall ws fs a,
    In a (audit_of ws fs) ->
    exists w, In w ws /\ a_reason a = w_reason w.
  Proof.
    intros ws fs a. unfold audit_of.
    induction fs as [|f rest IH]; [intros []|].
    simpl. destruct (apply_waivers ws rest) as [kept aud] eqn:Hrec.
    unfold find_waiver.
    destruct (find (fun w => waiver_matches w f) ws) eqn:E; simpl.
    - intros [Heq | Hin].
      + apply find_some in E. destruct E as [Hin_w _].
        exists w. split; [exact Hin_w|]. subst a. reflexivity.
      + apply IH. exact Hin.
    - intro Hin. apply IH. exact Hin.
  Qed.

  (* Hence if every waiver carries a non-empty reason, so does every audit
     record: no suppression is ever recorded with an empty justification. *)
  Theorem waiver_audit_reasons_nonempty : forall ws fs,
    (forall w, In w ws -> w_reason w <> EmptyString) ->
    forall a, In a (audit_of ws fs) -> a_reason a <> EmptyString.
  Proof.
    intros ws fs Hnonempty a Hin.
    destruct (audit_reason_from_waiver ws fs a Hin) as [w [Hin_w Heq]].
    rewrite Heq. apply Hnonempty. exact Hin_w.
  Qed.

  (* ── (d) NO-MATCH NO-OP ──────────────────────────────────────────────
     A waiver that matches no finding suppresses nothing: [kept] is unchanged
     and the audit trail is empty. *)
  Theorem waiver_no_match_noop : forall w fs,
    (forall f, In f fs -> waiver_matches w f = false) ->
    apply_waivers (w :: nil) fs = (fs, nil).
  Proof.
    intros w fs. induction fs as [|f rest IH]; intro Hnone; [reflexivity|].
    simpl.
    rewrite (IH (fun g Hg => Hnone g (or_intror Hg))).
    unfold find_waiver. simpl.
    rewrite (Hnone f (or_introl eq_refl)).
    reflexivity.
  Qed.

  (* ── Non-vacuity witness ─────────────────────────────────────────────
     Two findings on file 10: rule 1 and rule 2.  A single waiver for rule 1
     (any file).  Finding f1 IS suppressed; f2 is NOT. *)
  Definition ex_f1 : finding := {| f_rule := 1; f_file := 10 |}.
  Definition ex_f2 : finding := {| f_rule := 2; f_file := 10 |}.
  Definition ex_w  : waiver  :=
    {| w_rule := 1; w_file := None; w_reason := "legacy: reviewed 2026-07"%string |}.

  Example witness_apply :
    apply_waivers (ex_w :: nil) (ex_f1 :: ex_f2 :: nil)
    = (ex_f2 :: nil,
       {| a_finding := ex_f1; a_reason := "legacy: reviewed 2026-07"%string |} :: nil).
  Proof. vm_compute. reflexivity. Qed.

  Example witness_f1_suppressed : matched_b (ex_w :: nil) ex_f1 = true.
  Proof. reflexivity. Qed.

  Example witness_f2_not_suppressed : matched_b (ex_w :: nil) ex_f2 = false.
  Proof. reflexivity. Qed.

  (* The witness is genuinely non-vacuous: something IS and something is NOT
     suppressed, and the audit trail is non-empty. *)
  Example witness_nonvacuous :
    In ex_f1 (suppressed_of (ex_w :: nil) (ex_f1 :: ex_f2 :: nil)) /\
    ~ In ex_f2 (suppressed_of (ex_w :: nil) (ex_f1 :: ex_f2 :: nil)) /\
    audit_of (ex_w :: nil) (ex_f1 :: ex_f2 :: nil) <> nil.
  Proof.
    split; [| split].
    - vm_compute. left. reflexivity.
    - vm_compute. intros [H|[]]. discriminate.
    - vm_compute. discriminate.
  Qed.

End WaiverModel.
