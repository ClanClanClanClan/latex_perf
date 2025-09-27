Require Import List Arith Bool Lia.
Require Import ListWindow.
Import ListNotations.
Import ListWindow.

Module L0SmallstepControl.

Definition byte := nat.

Inductive token :=
| TControl (name:list byte)
| TText (bytes:list byte)
| TBraceOpen
| TBraceClose.

Definition classify (b:byte) : token :=
  match b with
  | 123 => TBraceOpen
  | 125 => TBraceClose
  | _ => TText [b]
  end.

Definition run (bs:list byte) : list token := map classify bs.

Definition state := (list byte * list token)%type.

Lemma length_run : forall bs, length (run bs) = length bs.
Proof. intros; unfold run; now rewrite map_length. Qed.

Inductive rstep : state -> state -> Prop :=
| rstep_cons : forall b bs ts,
    rstep (b :: bs, ts) (bs, ts ++ [classify b]).

Inductive rrun : state -> state -> Prop :=
| rrun_refl : forall s, rrun s s
| rrun_step : forall s s1 s2, rstep s s1 -> rrun s1 s2 -> rrun s s2.

Definition nf (x : state) : Prop := forall t, ~ rstep x t.

Lemma rstep_deterministic : forall s s1 s2,
  rstep s s1 -> rstep s s2 -> s1 = s2.
Proof.
  intros [bs ts] [bs1 ts1] [bs2 ts2] H1 H2.
  inversion H1; subst; clear H1.
  inversion H2; subst; reflexivity.
Qed.

Lemma rrun_nf_unique : forall s n1 n2,
  rrun s n1 -> nf n1 ->
  rrun s n2 -> nf n2 ->
  n1 = n2.
Proof.
  intros s n1 n2 Hr1 Hnf1 Hr2 Hnf2.
  revert n2 Hr2 Hnf2.
  induction Hr1 as [s'| s' s1 n1' Hstep1 Hr1' IH]; intros n2 Hr2 Hnf2.
  - inversion Hr2 as [| s'' s2 n2' Hstep2 Hr2']; subst; auto.
    exfalso. apply (Hnf1 _ Hstep2).
  - inversion Hr2 as [| s'' s2 n2' Hstep2 Hr2']; subst.
    + exfalso. apply (Hnf2 _ Hstep1).
    + assert (s1 = s2) by (apply rstep_deterministic with (s:=s'); assumption).
      subst s2. apply IH; assumption.
Qed.

Lemma rrun_equiv_run_ts : forall bs ts,
  rrun (bs, ts) ([], ts ++ run bs).
Proof.
  induction bs as [|b tl IH]; intros ts; simpl.
  - simpl. rewrite app_nil_r. apply rrun_refl.
  - econstructor.
    + constructor.
    + simpl.
      change (ts ++ classify b :: run tl) with (ts ++ ([classify b] ++ run tl)).
      rewrite app_assoc.
      apply IH.
Qed.

Lemma no_rstep_on_empty : forall ts s', ~ rstep ([], ts) s'.
Proof. intros ts s' H; inversion H. Qed.

Lemma rrun_end_unique_empty : forall bs ts1 ts2,
  rrun (bs, []) ([], ts1) -> rrun (bs, []) ([], ts2) -> ts1 = ts2.
Proof.
  intros bs ts1 ts2 Hr1 Hr2.
  set (s := (bs, ([] : list token))).
  set (n1 := (([] : list byte), ts1)).
  set (n2 := (([] : list byte), ts2)).
  assert (nf n1) as Hnf1 by (intros t; unfold n1; apply no_rstep_on_empty).
  assert (nf n2) as Hnf2 by (intros t; unfold n2; apply no_rstep_on_empty).
  assert (n1 = n2) by (eapply rrun_nf_unique; eauto).
  inversion H; reflexivity.
Qed.

Lemma run_app : forall a b, run (a ++ b) = run a ++ run b.
Proof. intros; unfold run; now rewrite map_app. Qed.

Lemma firstn_length_append_token :
  forall (xs ys : list token),
    firstn (length xs) (xs ++ ys) = xs.
Proof. apply (firstn_length_append (A:=token)). Qed.

Lemma skipn_length_append_token :
  forall (xs ys : list token),
    skipn (length xs) (xs ++ ys) = ys.
Proof. apply (skipn_length_append (A:=token)). Qed.

Lemma run_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (run (pre ++ mid ++ suf))) = run mid.
Proof.
  intros pre mid suf.
  rewrite run_app with (a:=pre) (b:=mid ++ suf).
  rewrite <- (length_run pre) at 1.
  rewrite skipn_length_append_token.
  rewrite run_app with (a:=mid) (b:=suf).
  rewrite <- (length_run mid) at 1.
  rewrite firstn_length_append_token.
  reflexivity.
Qed.

Lemma window_locality_under_prefix_change : forall pre1 pre2 mid suf,
  firstn (length mid) (skipn (length pre1) (run (pre1 ++ mid ++ suf))) =
  firstn (length mid) (skipn (length pre2) (run (pre2 ++ mid ++ suf))).
Proof.
  intros. rewrite !run_window_equivalence. reflexivity.
Qed.

Lemma rrun_window_locality : forall pre mid suf,
  exists s,
    rrun (pre ++ mid ++ suf, []) ([], s)
    /\ firstn (length mid) (skipn (length pre) s) = run mid.
Proof.
  intros. exists (run (pre ++ mid ++ suf)). split.
  - apply rrun_equiv_run_ts.
  - rewrite run_window_equivalence. reflexivity.
Qed.

End L0SmallstepControl.
