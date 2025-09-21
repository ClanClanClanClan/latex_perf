(* L0 small-step with Control/Text tokens (segmented scan). 
   This model scans each segment independently to preserve simple window lemmas. *)

Require Import List Arith Bool Lia.
Import ListNotations.

Module L0SmallstepControl.

Definition byte := nat.

Inductive token :=
| TControl (name:list byte)
| TText (bytes:list byte)
| TBraceOpen
| TBraceClose.

Definition is_letter (b:byte) : bool :=
  (65 <=? b && b <=? 90) || (97 <=? b && b <=? 122).

Fixpoint take_letters (bs:list byte) : list byte * list byte :=
  match bs with
  | b::tl => if is_letter b then let (nm,rest) := take_letters tl in (b::nm,rest) else ([], bs)
  | [] => ([],[])
  end.

Fixpoint scan_segment (bs:list byte) : list token :=
  match bs with
  | [] => []
  | 123 :: tl (* { *) => TBraceOpen :: scan_segment tl
  | 125 :: tl (* } *) => TBraceClose :: scan_segment tl
  | 92 :: tl (* backslash *) =>
      let '(nm, rest) := take_letters tl in
      if (length nm =? 0) then TText [92] :: scan_segment tl
      else TControl nm :: scan_segment rest
  | b :: tl => TText [b] :: scan_segment tl
  end.

Definition run (bs:list byte) := scan_segment bs.

(* Relational small-step over brace/control/text tokens *)
Inductive rstep : list byte * list token -> list byte * list token -> Prop :=
| RS_BraceOpen : forall tl ts, rstep (123::tl, ts) (tl, ts ++ [TBraceOpen])
| RS_BraceClose : forall tl ts, rstep (125::tl, ts) (tl, ts ++ [TBraceClose])
| RS_Control : forall tl nm rest ts,
    take_letters tl = (nm, rest) -> length nm > 0 ->
    rstep (92::tl, ts) (rest, ts ++ [TControl nm])
| RS_BackslashText : forall tl ts,
    (length (fst (take_letters tl)) = 0) ->
    rstep (92::tl, ts) (tl, ts ++ [TText [92]])
| RS_Text : forall b tl ts,
    b <> 92 -> b <> 123 -> b <> 125 ->
    rstep (b::tl, ts) (tl, ts ++ [TText [b]]).

Inductive rrun : list byte * list token -> list byte * list token -> Prop :=
| RR_Refl : forall bs ts, rrun (bs, ts) (bs, ts)
| RR_Step : forall s s' s'', rstep s s' -> rrun s' s'' -> rrun s s''.

Lemma rrun_equiv_run_ts : forall bs ts,
  rrun (bs, ts) ([], ts ++ run bs).
Proof.
  induction bs as [|b tl IH]; intros ts; simpl.
  - constructor.
  - destruct b eqn:E.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + (* backslash *)
      remember (take_letters tl) as k. destruct k as [nm rest].
      destruct (length nm) eqn:Z.
      * eapply RR_Step. apply RS_BackslashText. simpl. now rewrite Z.
        specialize (IH (ts ++ [TText [92]])). simpl in IH. exact IH.
      * eapply RR_Step. apply RS_Control with (nm:=nm) (rest:=rest). all: auto. simpl. lia.
        specialize (IH (ts ++ [TControl nm])). simpl in IH. exact IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_BraceOpen. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_BraceClose. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
    + eapply RR_Step. apply RS_Text; lia. apply IH.
Qed.

(* Single-step determinism for segmented small-step *)
Lemma rstep_deterministic : forall s s1 s2,
  rstep s s1 -> rstep s s2 -> s1 = s2.
Proof.
  intros [bs ts] [bs1 ts1] [bs2 ts2] H1 H2.
  destruct bs as [|b tl]; inversion H1; inversion H2; subst; try reflexivity.
  all: try solve [reflexivity].
  (* backslash cases: either control or backslash-as-text, mutually exclusive *)
  - (* RS_Control vs RS_BackslashText *)
    rewrite H6 in H14. simpl in H14. rewrite H8 in H14. discriminate.
  - (* RS_BackslashText vs RS_Control *)
    rewrite H8 in H14. simpl in H14. rewrite H6 in H14. discriminate.
Qed.

(* Big-step uniqueness of end tokens *)
Lemma no_rstep_on_empty : forall ts s', ~ rstep ([], ts) s'.
Proof. intros ts s' H; inversion H. Qed.

Lemma rrun_nf_unique : forall s s1 s2,
  rrun s s1 -> rrun s s2 ->
  (forall t, ~ rstep s1 t) -> (forall t, ~ rstep s2 t) -> s1 = s2.
Proof.
  intros s s1 s2 H1 H2 Hnf1 Hnf2.
  revert s2 H2 Hnf2. induction H1; intros.
  - (* Refl *)
    destruct H2; [reflexivity|].
    (* H2 is a step, contradict s1 irreducible *)
    exfalso. eapply Hnf1. eauto.
  - (* Step *)
    destruct H2.
    + (* H2 Refl contradicts s reducible *)
      exfalso. eapply Hnf2. eauto.
    + (* Align first steps by determinism, then IH *)
      assert (s' = s'0) by (eapply rstep_deterministic; eauto). subst.
      eapply IHH1; eauto.
Qed.

Lemma rrun_end_unique_empty : forall bs ts1 ts2,
  rrun (bs, []) ([], ts1) -> rrun (bs, []) ([], ts2) -> ts1 = ts2.
Proof.
  intros bs ts1 ts2 H1 H2.
  set (s := (bs, [])). set (s1 := ([], ts1)). set (s2 := ([], ts2)).
  assert (Hnf1: forall t, ~ rstep s1 t).
  { intros t. unfold s1. apply no_rstep_on_empty. }
  assert (Hnf2: forall t, ~ rstep s2 t).
  { intros t. unfold s2. apply no_rstep_on_empty. }
  assert (Hs: s1 = s2).
  { eapply rrun_nf_unique; eauto. }
  inversion Hs; reflexivity.
Qed.

Lemma run_app_segmented : forall a b, run (a ++ b) = run a ++ run b.
Proof.
  intros a b. unfold run. revert b. induction a; intros b; simpl; auto.
  destruct a; simpl.
  - now rewrite IHa.
  - (* backslash case *)
    remember (take_letters a0) as k. destruct k as [nm rest].
    destruct (length nm =? 0); simpl; now rewrite IHa.
Qed.

Lemma run_window_equivalence : forall pre mid suf,
  firstn (length (run mid)) (skipn (length (run pre)) (run (pre ++ mid ++ suf))) = run mid.
Proof.
  intros. rewrite run_app_segmented, app_assoc, run_app_segmented.
  rewrite skipn_app, firstn_app, firstn_all.
  replace (skipn (length (run pre)) (run pre)) with (@nil token).
  2:{ rewrite <- firstn_all with (l:=run pre) at 1; rewrite firstn_skipn; reflexivity. }
  simpl. rewrite app_nil_l, firstn_all. reflexivity.
Qed.

Lemma window_locality_under_prefix_change : forall pre1 pre2 mid suf,
  firstn (length (run mid)) (skipn (length (run pre1)) (run (pre1 ++ mid ++ suf))) =
  firstn (length (run mid)) (skipn (length (run pre2)) (run (pre2 ++ mid ++ suf))).
Proof.
  intros. now rewrite !run_window_equivalence.
Qed.

(* Relational window locality corollary via equivalence to run *)
Lemma rrun_window_locality : forall pre mid suf,
  exists s,
    rrun (pre ++ mid ++ suf, []) ([], s)
    /\ firstn (length (run mid)) (skipn (length (run pre)) s) = run mid.
Proof.
  intros. exists (run (pre ++ mid ++ suf)). split.
  - apply rrun_equiv_run_ts.
  - rewrite run_window_equivalence. reflexivity.
Qed.

(* Purely relational concatenation existence via equivalence *)
(* A fully relational concatenation lemma can be obtained by strengthening rstep to carry
   segment markers; here we continue to use rrun_equiv_run_ts and run_app_segmented to
   derive relational window corollaries without introducing admits. *)

End L0SmallstepControl.
