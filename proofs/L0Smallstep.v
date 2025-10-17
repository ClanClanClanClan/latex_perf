(* L0 small-step lexer skeleton with a catcode-sensitive classifier.
   This is a faithful shape for a small-step semantics over bytes → tokens,
   using a simple classifier (b mod 16) as an abstraction of catcodes. *)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Require Import ListWindow.
Import ListWindow.

Module L0Smallstep.

Definition byte := nat.
Inductive token :=
| TokEscape | TokBeginGrp | TokEndGrp | TokMath | TokAlignTab | TokNewline
| TokParam | TokSuperscr | TokSubscr | TokIgnored | TokSpace | TokLetter
| TokOther | TokActive | TokComment | TokInvalid.

(* ASCII helpers and catcode-like classifier (mirrors runtime shape) *)
Definition is_letter (b:byte) : bool :=
  orb (andb (Nat.leb 65 b) (Nat.leb b 90))
      (andb (Nat.leb 97 b) (Nat.leb b 122)).

Definition classify (b:byte) : token :=
  if Nat.eqb b 92 then TokEscape (* \\ *) else
  if Nat.eqb b 123 then TokBeginGrp (* { *) else
  if Nat.eqb b 125 then TokEndGrp (* } *) else
  if Nat.eqb b 36 then TokMath (* $ *) else
  if Nat.eqb b 38 then TokAlignTab (* & *) else
  if (Nat.eqb b 10) || (Nat.eqb b 13) then TokNewline (* NL/CR *) else
  if Nat.eqb b 35 then TokParam (* # *) else
  if Nat.eqb b 94 then TokSuperscr (* ^ *) else
  if Nat.eqb b 95 then TokSubscr (* _ *) else
  if Nat.eqb b 0 then TokIgnored  (* NUL *) else
  if (Nat.eqb b 32) || (Nat.eqb b 9) then TokSpace (* space/tab *) else
  if is_letter b then TokLetter else
  if Nat.eqb b 126 then TokActive (* ~ *) else
  if Nat.eqb b 37 then TokComment  (* % *) else
  if Nat.eqb b 127 then TokInvalid else TokOther.

Definition run (bs:list byte) : list token := map classify bs.

Lemma length_run : forall bs, length (run bs) = length bs.
Proof. intros; unfold run; now rewrite List.length_map. Qed.

Lemma firstn_length_append_token :
  forall (xs ys : list token),
    firstn (length xs) (xs ++ ys) = xs.
Proof. apply (firstn_length_append (A:=token)). Qed.

Lemma skipn_length_append_token :
  forall (xs ys : list token),
    skipn (length xs) (xs ++ ys) = ys.
Proof. apply (skipn_length_append (A:=token)). Qed.

Lemma run_app : forall a b, run (a ++ b) = run a ++ run b.
Proof. intros; unfold run; now rewrite map_app. Qed.

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

Definition state := (list byte * list token)%type.

(* Relational small-step: consume one byte, emit one token. *)
Inductive step : list byte * list token -> list byte * list token -> Prop :=
| Step_Cons : forall b bs ts,
    step (b::bs, ts) (bs, ts ++ [classify b]).

Definition nf (x : state) : Prop :=
  forall t, ~ step x t.

(* Determinism: exactly one next state for non-empty input. *)
Lemma step_deterministic : forall s s1 s2,
  step s s1 -> step s s2 -> s1 = s2.
Proof.
  intros [bs ts] [bs1 ts1] [bs2 ts2] H1 H2.
  inversion H1; subst; clear H1.
  inversion H2; subst; auto.
Qed.

(* Reflexive–transitive closure of [step] *)
Inductive steps : list byte * list token -> list byte * list token -> Prop :=
| Steps_Refl : forall s, steps s s
| Steps_Step : forall s s' s'', step s s' -> steps s' s'' -> steps s s''.

Lemma steps_nf_unique : forall s n1 n2,
  steps s n1 -> nf n1 ->
  steps s n2 -> nf n2 ->
  n1 = n2.
Proof.
  intros s n1 n2 Hr1 Hnf1 Hr2 Hnf2.
  revert n2 Hr2 Hnf2.
  induction Hr1 as [s'| s' s1 n1' Hstep1 Hr1' IH]; intros n2 Hr2 Hnf2.
  - inversion Hr2 as [| s'' s2 n2' Hstep2 Hr2']; subst; auto.
    exfalso. apply (Hnf1 _ Hstep2).
  - inversion Hr2 as [| s'' s2 n2' Hstep2 Hr2']; subst.
    + exfalso. apply (Hnf2 _ Hstep1).
    + assert (s1 = s2) by (apply step_deterministic with (s:=s'); assumption).
      subst s2. apply IH; assumption.
Qed.

(* Big-step equivalence to the functional [run] *)
Lemma steps_equiv_run_ts : forall bs ts,
  steps (bs, ts) ([], ts ++ run bs).
Proof.
  induction bs as [|b tl IH]; intros ts; simpl.
  - rewrite (app_nil_r (A:=token) ts). constructor.
  - econstructor.
    + constructor.
    + simpl.
      change (ts ++ classify b :: run tl) with (ts ++ ([classify b] ++ run tl)).
      rewrite app_assoc.
      apply IH.
Qed.

Lemma steps_end_run : forall bs,
  steps (bs, []) ([], run bs).
Proof.
  intro bs.
  pose proof (steps_equiv_run_ts bs []) as H.
  simpl in H.
  exact H.
Qed.

Lemma no_step_on_empty : forall ts s', ~ step ([], ts) s'.
Proof. intros ts s' H; inversion H. Qed.

Lemma steps_end_unique_empty : forall bs ts1 ts2,
  steps (bs, []) ([], ts1) -> steps (bs, []) ([], ts2) -> ts1 = ts2.
Proof.
  intros bs ts1 ts2 H1 H2.
  set (s := (bs, ([] : list token))).
  set (n1 := (([] : list byte), ts1)).
  set (n2 := (([] : list byte), ts2)).
  assert (nf n1) as Hnf1 by (intros t; unfold n1; apply no_step_on_empty).
  assert (nf n2) as Hnf2 by (intros t; unfold n2; apply no_step_on_empty).
  assert (n1 = n2) as Heq by (eapply steps_nf_unique; eauto).
  inversion Heq; reflexivity.
Qed.

Lemma steps_window_equivalence : forall pre mid suf ts,
  steps (pre ++ mid ++ suf, []) ([], ts) ->
  firstn (length mid) (skipn (length pre) ts) = run mid.
Proof.
  intros pre mid suf ts H.
  pose proof (steps_end_run (pre ++ mid ++ suf)) as Hrun.
  assert (ts = run (pre ++ mid ++ suf)) as -> by (eapply steps_end_unique_empty; eauto).
  apply run_window_equivalence.
Qed.

(* --- Index-based edits over bytes and their window consequences --- *)

Definition split_at (k:nat) (xs:list byte) : list byte * list byte := (firstn k xs, skipn k xs).

Inductive edit_at_index : list byte -> nat -> list byte -> Prop :=
| EA_Insert : forall mid k b,
    k <= length mid ->
    edit_at_index mid k (firstn k mid ++ b :: skipn k mid)
| EA_Delete : forall mid k x,
    k < length mid -> nth k mid 0 = x ->
    edit_at_index mid k (firstn k mid ++ skipn (S k) mid).

Lemma run_insert_at_index : forall mid k b,
  k <= length mid ->
  run (firstn k mid ++ b :: skipn k mid) = run (firstn k mid) ++ classify b :: run (skipn k mid).
Proof.
  intros. unfold run. now rewrite map_app.
Qed.

Lemma run_delete_at_index : forall mid k x,
  k < length mid -> nth k mid 0 = x ->
  run (firstn k mid ++ skipn (S k) mid) = run (firstn k mid) ++ run (skipn (S k) mid).
Proof.
  intros. unfold run. now rewrite map_app.
Qed.

Lemma steps_window_after_edit_at_index : forall pre mid suf k mid' ts,
  edit_at_index mid k mid' ->
  steps (pre ++ mid' ++ suf, []) ([], ts) ->
  firstn (length mid') (skipn (length pre) ts) = run mid'.
Proof.
  intros. eapply steps_window_equivalence; eauto.
Qed.

(* Functional run (map classify). *)
(* Offsets as 0..n-1 for run. *)
Fixpoint seq (s n:nat) : list nat := match n with 0=>[] | S k => s :: seq (S s) k end.
Definition offsets (bs:list byte) := seq 0 (length (run bs)).
Definition normalize (k:nat) (xs:list nat) := map (fun o => o - k) xs.

Lemma Nat_sub_succ_succ : forall n k, S n - S k = n - k.
Proof.
  intros n k. revert n.
  induction k; intros n; simpl.
  - reflexivity.
  - destruct n; simpl; auto.
Qed.

Lemma Nat_add_succ_comm : forall s k, s + S k = S s + k.
Proof.
  intros s k; induction s; simpl.
  - reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma skipn_seq : forall s n k, skipn k (seq s n) = seq (s+k) (n-k).
Proof.
  intros s n k; revert s n; induction k; intros s n; simpl.
  - rewrite Nat.add_0_r. destruct n; reflexivity.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + specialize (IHk (S s) n').
      replace (s + S k) with (S s + k) by (symmetry; apply Nat_add_succ_comm).
      exact IHk.
Qed.

Lemma firstn_seq : forall s n m, firstn m (seq s n) = seq s (Nat.min m n).
Proof.
  intros s n m; revert s n; induction m; intros s n; simpl; auto.
  destruct n; simpl; auto. now rewrite IHm.
Qed.

Lemma seq_succ : forall s n,
  seq (S s) n = map S (seq s n).
Proof.
  intros s n; revert s.
  induction n; intros s; simpl; auto.
  rewrite IHn with (s := S s). reflexivity.
Qed.

Lemma seq_shift : forall k m,
  seq k m = map (fun i => k + i) (seq 0 m).
Proof.
  intros k m; revert k.
  induction m; intros k; simpl; auto.
  rewrite IHm with (k := S k).
  rewrite seq_succ.
  rewrite map_map.
  rewrite Nat.add_0_r.
  f_equal.
  apply map_ext_in; intros i _.
  now rewrite Nat.add_succ_comm.
Qed.

Lemma add_sub_cancel : forall k i, k + i - k = i.
Proof.
  intros k i; lia.
Qed.

Lemma map_sub_seq : forall k m,
  map (fun o => o - k) (seq k m) = seq 0 m.
Proof.
  intros k m.
  rewrite seq_shift.
  rewrite map_map.
  assert (map (fun i => (k + i) - k) (seq 0 m) = map (fun i => i) (seq 0 m)) as ->.
  { apply map_ext_in; intros i _. now rewrite add_sub_cancel. }
  now rewrite map_id.
Qed.

Lemma normalize_seq : forall k m,
  normalize k (seq k m) = seq 0 m.
Proof.
  intros k m; unfold normalize; apply map_sub_seq.
Qed.

Lemma offsets_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (offsets (pre ++ mid ++ suf))) =
  seq (length pre) (length mid).
Proof.
  intros pre mid suf. unfold offsets.
  rewrite length_run.
  rewrite List.length_app.
  rewrite List.length_app.
  rewrite skipn_seq, firstn_seq. now rewrite Nat.min_l by lia.
Qed.

Lemma normalized_offsets_window : forall pre mid suf,
  normalize (length pre)
    (firstn (length mid) (skipn (length pre) (offsets (pre ++ mid ++ suf)))) =
  offsets mid.
Proof.
  intros pre mid suf.
  rewrite offsets_window_equivalence.
  rewrite (normalize_seq (length pre) (length mid)).
  unfold offsets. now rewrite length_run.
Qed.

End L0Smallstep.
