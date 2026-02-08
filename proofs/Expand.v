From Coq Require Import List Arith Lia.
Import ListNotations.

(* ================================================================== *)
(*  L1 Expansion model with fuel-bounded recursion.                    *)
(*                                                                     *)
(*  Key definitions:                                                   *)
(*    - macro_catalog : finite map from name to expansion body         *)
(*    - expand_fuel  : fuel-bounded single-step expansion              *)
(*    - expand_star  : fuel-bounded fixpoint expansion                 *)
(*                                                                     *)
(*  Key theorems (roadmap §7.4, Week 14-17 exit criteria):            *)
(*    - expand_no_teof             : expansion never produces EOF      *)
(*    - expand_deterministic       : same input → same output          *)
(*    - expand_one_unchanged       : unchanged flag means identity     *)
(*    - expand_star_fixpoint       : fixpoint fuel is a no-op          *)
(*    - expand_one_decreases_ctrls : acyclic step decreases ctrls     *)
(*    - expand_terminates_acyclic  : acyclic catalog → termination    *)
(*    - expand_fuel_insensitive    : sufficient fuel → confluence      *)
(* ================================================================== *)

Module L1.

  (* ── Token representation ─────────────────────────────────────── *)

  Inductive token_kind := TText | TControl | TBeginG | TEndG | TEof.

  Record token := { kind : token_kind; payload : nat }.

  Definition token_stream := list token.

  Definition is_eof (t : token) : bool :=
    match t.(kind) with TEof => true | _ => false end.

  Fixpoint has_eof (ts : token_stream) : bool :=
    match ts with
    | [] => false
    | t :: rest => if is_eof t then true else has_eof rest
    end.

  Definition mk_text (n : nat) : token := {| kind := TText; payload := n |}.
  Definition mk_ctrl (n : nat) : token := {| kind := TControl; payload := n |}.

  (* ── Macro catalog ────────────────────────────────────────────── *)

  Record catalog_entry := {
    entry_name : nat;
    entry_body : token_stream;
  }.

  Definition catalog := list catalog_entry.

  Fixpoint catalog_lookup (cat : catalog) (ctrl_id : nat) : option token_stream :=
    match cat with
    | [] => None
    | e :: rest =>
        if Nat.eqb e.(entry_name) ctrl_id then Some e.(entry_body)
        else catalog_lookup rest ctrl_id
    end.

  Definition wf_entry (e : catalog_entry) : Prop :=
    has_eof e.(entry_body) = false.

  Definition wf_catalog (cat : catalog) : Prop :=
    Forall wf_entry cat.

  (* ── Single-step expansion ────────────────────────────────────── *)

  Fixpoint expand_one (cat : catalog) (ts : token_stream) : bool * token_stream :=
    match ts with
    | [] => (false, [])
    | t :: rest =>
        match t.(kind) with
        | TControl =>
            match catalog_lookup cat t.(payload) with
            | Some body => (true, body ++ rest)
            | None =>
                let '(ch, rest') := expand_one cat rest in
                (ch, t :: rest')
            end
        | _ =>
            let '(ch, rest') := expand_one cat rest in
            (ch, t :: rest')
        end
    end.

  (* ── Fuel-bounded fixpoint expansion ──────────────────────────── *)

  Fixpoint expand_star (cat : catalog) (fuel : nat) (ts : token_stream) : token_stream :=
    match fuel with
    | 0 => ts
    | S fuel' =>
        let '(changed, ts') := expand_one cat ts in
        if changed then expand_star cat fuel' ts'
        else ts'
    end.

  (* ── Acyclicity definitions (used by deferred proofs) ─────────── *)

  Definition is_catalog_ctrl (cat : catalog) (t : token) : bool :=
    match t.(kind) with
    | TControl =>
        match catalog_lookup cat t.(payload) with
        | Some _ => true
        | None => false
        end
    | _ => false
    end.

  Definition count_catalog_ctrls (cat : catalog) (ts : token_stream) : nat :=
    length (filter (is_catalog_ctrl cat) ts).

  Definition acyclic_catalog (cat : catalog) : Prop :=
    forall e, In e cat ->
      count_catalog_ctrls cat e.(entry_body) = 0.

  (* ================================================================ *)
  (*  PROVEN THEOREMS (all QED, zero admits)                           *)
  (* ================================================================ *)

  (* ── Helper lemmas ───────────────────────────────────────────── *)

  Lemma has_eof_cons : forall t ts,
    has_eof (t :: ts) = false ->
    is_eof t = false /\ has_eof ts = false.
  Proof.
    intros t ts H. simpl in H.
    destruct (is_eof t) eqn:Ht.
    - discriminate.
    - auto.
  Qed.

  Lemma has_eof_app : forall xs ys,
    has_eof xs = false ->
    has_eof ys = false ->
    has_eof (xs ++ ys) = false.
  Proof.
    intros xs. induction xs as [|x xs' IH]; intros ys Hxs Hys.
    - simpl. exact Hys.
    - apply has_eof_cons in Hxs as [Hx Hxs'].
      simpl. rewrite Hx. apply IH; assumption.
  Qed.

  Lemma catalog_lookup_wf : forall cat ctrl_id body,
    wf_catalog cat ->
    catalog_lookup cat ctrl_id = Some body ->
    has_eof body = false.
  Proof.
    intros cat ctrl_id body Hwf Hlook.
    induction cat as [|e cat' IHcat]; [discriminate|].
    simpl in Hlook.
    destruct (Nat.eqb (entry_name e) ctrl_id) eqn:Eid.
    - injection Hlook as <-.
      inversion Hwf; subst. exact H1.
    - apply IHcat; [|exact Hlook].
      inversion Hwf; assumption.
  Qed.

  (* ── T1: expand_no_teof ──────────────────────────────────────── *)

  Lemma expand_one_no_eof : forall cat ts changed ts',
    wf_catalog cat ->
    has_eof ts = false ->
    expand_one cat ts = (changed, ts') ->
    has_eof ts' = false.
  Proof.
    intros cat ts.
    revert cat.
    induction ts as [|t rest IH]; intros cat changed ts' Hwf Hno Heq.
    - simpl in Heq. inversion Heq; subst. assumption.
    - apply has_eof_cons in Hno as [Ht Hrest].
      simpl in Heq.
      destruct (kind t) eqn:Hk.
      + (* TText *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        inversion Heq; subst.
        simpl. rewrite Ht. eapply IH; eassumption.
      + (* TControl *)
        destruct (catalog_lookup cat (payload t)) eqn:Hlook.
        * inversion Heq; subst.
          apply has_eof_app.
          -- eapply catalog_lookup_wf; eassumption.
          -- exact Hrest.
        * destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
          inversion Heq; subst.
          simpl. rewrite Ht. eapply IH; eassumption.
      + (* TBeginG *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        inversion Heq; subst.
        simpl. rewrite Ht. eapply IH; eassumption.
      + (* TEndG *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        inversion Heq; subst.
        simpl. rewrite Ht. eapply IH; eassumption.
      + (* TEof *)
        unfold is_eof in Ht. rewrite Hk in Ht. discriminate.
  Qed.

  Theorem expand_no_teof : forall cat fuel ts,
    wf_catalog cat ->
    has_eof ts = false ->
    has_eof (expand_star cat fuel ts) = false.
  Proof.
    intros cat fuel.
    induction fuel as [|fuel' IH]; intros ts Hwf Hno.
    - simpl. assumption.
    - simpl.
      destruct (expand_one cat ts) as [changed ts'] eqn:Heq.
      destruct changed.
      + apply IH; [assumption|].
        eapply expand_one_no_eof; eassumption.
      + eapply expand_one_no_eof; eassumption.
  Qed.

  (* ── T2: expand_deterministic ────────────────────────────────── *)

  Theorem expand_deterministic : forall cat fuel ts,
    expand_star cat fuel ts = expand_star cat fuel ts.
  Proof. reflexivity. Qed.

  (* ── T3: unchanged implies identity ──────────────────────────── *)

  Lemma expand_one_unchanged : forall cat ts ts',
    expand_one cat ts = (false, ts') -> ts' = ts.
  Proof.
    intros cat ts. revert cat.
    induction ts as [|t rest IH]; intros cat ts' Heq.
    - simpl in Heq. inversion Heq. reflexivity.
    - simpl in Heq.
      destruct (kind t) eqn:Hk.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst. f_equal. eapply IH. exact Hrec.
      + destruct (catalog_lookup cat (payload t)) eqn:Hlook.
        * inversion Heq.
        * destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
          destruct ch'; [inversion Heq|].
          inversion Heq; subst. f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst. f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst. f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst. f_equal. eapply IH. exact Hrec.
  Qed.

  (* ── T4: fixpoint fuel is a no-op ───────────────────────────── *)

  Lemma expand_star_fixpoint : forall cat fuel ts ts',
    expand_one cat ts = (false, ts') ->
    expand_star cat fuel ts = ts.
  Proof.
    intros cat fuel ts ts' Heq.
    destruct fuel as [|fuel'].
    - simpl. reflexivity.
    - simpl. rewrite Heq.
      apply expand_one_unchanged in Heq. subst. reflexivity.
  Qed.

  (* ================================================================ *)
  (*  COUNTING HELPERS (for decrease / termination / fuel proofs)      *)
  (* ================================================================ *)

  Lemma filter_app : forall {A : Type} (f : A -> bool) (xs ys : list A),
    filter f (xs ++ ys) = filter f xs ++ filter f ys.
  Proof.
    intros A f xs. induction xs as [|x xs' IH]; intros ys.
    - reflexivity.
    - simpl. destruct (f x); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma count_ctrls_app : forall cat xs ys,
    count_catalog_ctrls cat (xs ++ ys) =
    count_catalog_ctrls cat xs + count_catalog_ctrls cat ys.
  Proof.
    intros. unfold count_catalog_ctrls.
    rewrite filter_app. apply app_length.
  Qed.

  Lemma count_ctrls_nil : forall cat,
    count_catalog_ctrls cat [] = 0.
  Proof. reflexivity. Qed.

  Lemma count_ctrls_zero_filter : forall cat ts,
    count_catalog_ctrls cat ts = 0 ->
    filter (is_catalog_ctrl cat) ts = [].
  Proof.
    intros cat ts H. unfold count_catalog_ctrls in H.
    destruct (filter (is_catalog_ctrl cat) ts) eqn:Hf.
    - reflexivity.
    - simpl in H. lia.
  Qed.

  Lemma count_ctrls_cons : forall cat t ts,
    count_catalog_ctrls cat (t :: ts) =
    (if is_catalog_ctrl cat t then 1 else 0) + count_catalog_ctrls cat ts.
  Proof.
    intros. unfold count_catalog_ctrls. simpl.
    destruct (is_catalog_ctrl cat t); simpl; reflexivity.
  Qed.

  (* Key fact: a resolvable control token contributes exactly 1 *)
  Lemma is_catalog_ctrl_lookup : forall cat t body,
    kind t = TControl ->
    catalog_lookup cat (payload t) = Some body ->
    is_catalog_ctrl cat t = true.
  Proof.
    intros cat t body Hk Hlook.
    unfold is_catalog_ctrl. rewrite Hk. rewrite Hlook. reflexivity.
  Qed.

  (* Non-control tokens contribute 0 *)
  Lemma is_catalog_ctrl_non_ctrl : forall cat t,
    kind t <> TControl ->
    is_catalog_ctrl cat t = false.
  Proof.
    intros cat t Hk. unfold is_catalog_ctrl.
    destruct (kind t); try reflexivity; contradiction.
  Qed.

  (* Control with no lookup contributes 0 *)
  Lemma is_catalog_ctrl_none : forall cat t,
    kind t = TControl ->
    catalog_lookup cat (payload t) = None ->
    is_catalog_ctrl cat t = false.
  Proof.
    intros cat t Hk Hlook.
    unfold is_catalog_ctrl. rewrite Hk. rewrite Hlook. reflexivity.
  Qed.

  (* ================================================================ *)
  (*  T5: expand_one preserves count (unchanged case)                  *)
  (* ================================================================ *)

  Lemma expand_one_ctrls_unchanged : forall cat ts ts',
    expand_one cat ts = (false, ts') ->
    count_catalog_ctrls cat ts' = count_catalog_ctrls cat ts.
  Proof.
    intros cat ts.
    revert cat.
    induction ts as [|t rest IH]; intros cat ts' Heq.
    - simpl in Heq. inversion Heq. reflexivity.
    - simpl in Heq.
      destruct (kind t) eqn:Hk.
      + (* TText *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        f_equal. eapply IH. exact Hrec.
      + (* TControl *)
        destruct (catalog_lookup cat (payload t)) eqn:Hlook.
        * (* found → changed=true, contradicts false *)
          inversion Heq.
        * (* not found → recurse *)
          destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
          destruct ch'; [inversion Heq|].
          inversion Heq; subst.
          rewrite !count_ctrls_cons.
          f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        f_equal. eapply IH. exact Hrec.
      + destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [inversion Heq|].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        f_equal. eapply IH. exact Hrec.
  Qed.

  (* Lookup implies membership: body came from some entry *)
  Lemma catalog_lookup_in : forall cat name body,
    catalog_lookup cat name = Some body ->
    exists e, In e cat /\ entry_name e = name /\ entry_body e = body.
  Proof.
    intros cat name body.
    induction cat as [|e cat' IH]; intros Hlook.
    - simpl in Hlook. discriminate.
    - simpl in Hlook.
      destruct (Nat.eqb (entry_name e) name) eqn:Eid.
      + injection Hlook as <-.
        apply Nat.eqb_eq in Eid.
        exists e. split; [left; reflexivity | split; [exact Eid | reflexivity]].
      + destruct (IH Hlook) as [e' [Hin [Hname Hbody]]].
        exists e'. split; [right; exact Hin | split; assumption].
  Qed.

  (* Acyclicity + lookup → body has 0 resolvable ctrls *)
  Lemma acyclic_lookup_zero : forall cat name body,
    acyclic_catalog cat ->
    catalog_lookup cat name = Some body ->
    count_catalog_ctrls cat body = 0.
  Proof.
    intros cat name body Hacyc Hlook.
    destruct (catalog_lookup_in cat name body Hlook) as [e [Hin [_ Hbody]]].
    subst. apply Hacyc. exact Hin.
  Qed.

  (* ================================================================ *)
  (*  T6: expand_one_decreases_ctrls                                   *)
  (*  When expand_one succeeds (changed=true) AND the catalog is       *)
  (*  acyclic, the count of resolvable controls strictly decreases.    *)
  (* ================================================================ *)

  Theorem expand_one_decreases_ctrls : forall cat ts ts',
    acyclic_catalog cat ->
    expand_one cat ts = (true, ts') ->
    count_catalog_ctrls cat ts' < count_catalog_ctrls cat ts.
  Proof.
    intros cat ts.
    revert cat.
    induction ts as [|t rest IH]; intros cat ts' Hacyc Heq.
    - simpl in Heq. inversion Heq.
    - simpl in Heq.
      destruct (kind t) eqn:Hk.
      + (* TText *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [|inversion Heq].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        assert (Hne : kind t <> TControl) by (rewrite Hk; discriminate).
        rewrite (is_catalog_ctrl_non_ctrl cat t Hne).
        specialize (IH cat rest' Hacyc Hrec). lia.
      + (* TControl *)
        destruct (catalog_lookup cat (payload t)) eqn:Hlook.
        * (* found body *)
          inversion Heq; subst.
          rewrite count_ctrls_app.
          rewrite count_ctrls_cons.
          rewrite (is_catalog_ctrl_lookup cat t t0 Hk Hlook).
          rewrite (acyclic_lookup_zero cat (payload t) t0 Hacyc Hlook).
          lia.
        * (* not found → recurse *)
          destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
          destruct ch'; [|inversion Heq].
          inversion Heq; subst.
          rewrite !count_ctrls_cons.
          rewrite (is_catalog_ctrl_none cat t Hk Hlook).
          specialize (IH cat rest' Hacyc Hrec). lia.
      + (* TBeginG *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [|inversion Heq].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        assert (Hne : kind t <> TControl) by (rewrite Hk; discriminate).
        rewrite (is_catalog_ctrl_non_ctrl cat t Hne).
        specialize (IH cat rest' Hacyc Hrec). lia.
      + (* TEndG *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [|inversion Heq].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        assert (Hne : kind t <> TControl) by (rewrite Hk; discriminate).
        rewrite (is_catalog_ctrl_non_ctrl cat t Hne).
        specialize (IH cat rest' Hacyc Hrec). lia.
      + (* TEof *)
        destruct (expand_one cat rest) as [ch' rest'] eqn:Hrec.
        destruct ch'; [|inversion Heq].
        inversion Heq; subst.
        rewrite !count_ctrls_cons.
        assert (Hne : kind t <> TControl) by (rewrite Hk; discriminate).
        rewrite (is_catalog_ctrl_non_ctrl cat t Hne).
        specialize (IH cat rest' Hacyc Hrec). lia.
  Qed.

  (* ================================================================ *)
  (*  T7: expand_terminates_acyclic                                    *)
  (*  With an acyclic, well-formed catalog, expansion reaches a        *)
  (*  fixpoint within count_catalog_ctrls steps.                       *)
  (* ================================================================ *)

  Lemma expand_star_reaches_fixpoint : forall cat n ts,
    acyclic_catalog cat ->
    wf_catalog cat ->
    has_eof ts = false ->
    count_catalog_ctrls cat ts <= n ->
    let ts' := expand_star cat n ts in
    fst (expand_one cat ts') = false.
  Proof.
    intros cat n.
    induction n as [|n' IH]; intros ts Hacyc Hwf Hno Hle.
    - (* n=0, so count = 0. Must show expand_one on ts returns false. *)
      simpl.
      destruct (expand_one cat ts) as [changed ts'] eqn:Heq.
      simpl. destruct changed eqn:Hch.
      + (* changed = true contradicts count = 0 *)
        exfalso.
        assert (Hdec := expand_one_decreases_ctrls cat ts ts' Hacyc Heq).
        lia.
      + reflexivity.
    - simpl.
      destruct (expand_one cat ts) as [changed ts'] eqn:Heq.
      destruct changed.
      + (* changed = true → count decreased; recurse *)
        apply IH.
        * exact Hacyc.
        * exact Hwf.
        * eapply expand_one_no_eof; eassumption.
        * assert (Hdec := expand_one_decreases_ctrls cat ts ts' Hacyc Heq).
          lia.
      + (* changed = false → already at fixpoint *)
        simpl.
        assert (Hid := expand_one_unchanged cat ts ts' Heq). subst ts'.
        rewrite Heq. reflexivity.
  Qed.

  Theorem expand_terminates_acyclic : forall cat ts,
    acyclic_catalog cat ->
    wf_catalog cat ->
    has_eof ts = false ->
    let fuel := count_catalog_ctrls cat ts in
    fst (expand_one cat (expand_star cat fuel ts)) = false.
  Proof.
    intros cat ts Hacyc Hwf Hno.
    apply expand_star_reaches_fixpoint; auto.
  Qed.

  (* ================================================================ *)
  (*  T8: expand_fuel_insensitive                                      *)
  (*  Once a fixpoint is reached, additional fuel does not change       *)
  (*  the result.                                                      *)
  (* ================================================================ *)

  Lemma expand_star_succ_at_fixpoint : forall cat fuel ts,
    fst (expand_one cat (expand_star cat fuel ts)) = false ->
    expand_star cat (S fuel) ts = expand_star cat fuel ts.
  Proof.
    intros cat fuel.
    induction fuel as [|fuel' IH]; intros ts Hfix.
    - (* fuel = 0 → expand_star cat 0 ts = ts *)
      simpl. simpl in Hfix.
      destruct (expand_one cat ts) as [changed ts'] eqn:Heq.
      simpl in Hfix. subst changed.
      apply expand_one_unchanged in Heq. subst. reflexivity.
    - (* fuel = S fuel' *)
      simpl.
      destruct (expand_one cat ts) as [changed ts'] eqn:Heq.
      destruct changed.
      + (* changed = true → recurse *)
        simpl in Hfix. rewrite Heq in Hfix.
        apply IH. exact Hfix.
      + (* changed = false → fixpoint reached *)
        apply expand_one_unchanged in Heq as Hid. subst ts'.
        reflexivity.
  Qed.

  Lemma expand_star_fuel_excess : forall cat fuel extra ts,
    fst (expand_one cat (expand_star cat fuel ts)) = false ->
    expand_star cat (fuel + extra) ts = expand_star cat fuel ts.
  Proof.
    intros cat fuel extra.
    induction extra as [|extra' IH]; intros ts Hfix.
    - rewrite Nat.add_0_r. reflexivity.
    - replace (fuel + S extra') with (S (fuel + extra')) by lia.
      rewrite <- IH; [|exact Hfix].
      apply expand_star_succ_at_fixpoint.
      rewrite IH; [|exact Hfix].
      exact Hfix.
  Qed.

  Theorem expand_fuel_insensitive : forall cat fuel1 fuel2 ts,
    acyclic_catalog cat ->
    wf_catalog cat ->
    has_eof ts = false ->
    count_catalog_ctrls cat ts <= fuel1 ->
    count_catalog_ctrls cat ts <= fuel2 ->
    expand_star cat fuel1 ts = expand_star cat fuel2 ts.
  Proof.
    intros cat fuel1 fuel2 ts Hacyc Hwf Hno Hle1 Hle2.
    assert (Hf1 : fst (expand_one cat (expand_star cat fuel1 ts)) = false).
    { apply expand_star_reaches_fixpoint; assumption. }
    assert (Hf2 : fst (expand_one cat (expand_star cat fuel2 ts)) = false).
    { apply expand_star_reaches_fixpoint; assumption. }
    (* Both fuel1 and fuel2 reach the same fixpoint *)
    set (base := count_catalog_ctrls cat ts) in *.
    assert (H1 : expand_star cat fuel1 ts = expand_star cat base ts).
    { replace fuel1 with (base + (fuel1 - base)) by lia.
      apply expand_star_fuel_excess.
      apply expand_star_reaches_fixpoint; auto. }
    assert (H2 : expand_star cat fuel2 ts = expand_star cat base ts).
    { replace fuel2 with (base + (fuel2 - base)) by lia.
      apply expand_star_fuel_excess.
      apply expand_star_reaches_fixpoint; auto. }
    congruence.
  Qed.

End L1.
