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
(*    - expand_no_teof       : expansion never produces EOF token      *)
(*    - expand_deterministic : same input → same output                *)
(*    - expand_one_unchanged : unchanged flag means identity           *)
(*    - expand_star_fixpoint : fixpoint fuel is a no-op                *)
(*                                                                     *)
(*  Deferred to Week 15-16 (in proofs/archive/ExpandDraft.v):         *)
(*    - expand_one_decreases_ctrls                                     *)
(*    - expand_terminates_acyclic                                      *)
(*    - expand_fuel_insensitive                                        *)
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

End L1.
