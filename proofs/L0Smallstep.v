(* L0 small-step lexer skeleton with a catcode-sensitive classifier.
   This is a faithful shape for a small-step semantics over bytes → tokens,
   using a simple classifier (b mod 16) as an abstraction of catcodes. *)

Require Import List Arith Bool Lia.
Import ListNotations.

Module L0Smallstep.

Definition byte := nat.
Inductive token :=
| TokEscape | TokBeginGrp | TokEndGrp | TokMath | TokAlignTab | TokNewline
| TokParam | TokSuperscr | TokSubscr | TokIgnored | TokSpace | TokLetter
| TokOther | TokActive | TokComment | TokInvalid.

(* ASCII helpers and catcode-like classifier (mirrors runtime shape) *)
Definition is_letter (b:byte) : bool :=
  (65 <=? b && b <=? 90) || (97 <=? b && b <=? 122).

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

(* Relational small-step: consume one byte, emit one token. *)
Inductive step : list byte * list token -> list byte * list token -> Prop :=
| Step_Cons : forall b bs ts,
    step (b::bs, ts) (bs, ts ++ [classify b]).

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

(* Big-step equivalence to the functional [run] *)
Lemma steps_end_run : forall bs,
  steps (bs, []) ([], run bs).
Proof.
  induction bs as [|b tl IH]; simpl.
  - constructor.
  - econstructor. constructor. simpl. rewrite <- app_nil_l.
    eapply Steps_Step with (s':=(tl, [classify b])).
    + constructor.
    + (* continue with the tail; append associativity maintains shape *)
      revert IH. simpl. intros IH.
      (* shift IH tokens to append after [classify b] *)
      (* We show steps (tl, [classify b]) ([], [classify b] ++ run tl) *)
      remember ([], run tl) as fin.
      assert (steps (tl, []) (fst fin, snd fin)) as H by (subst; exact IH).
      clear IH. subst fin. (* lift tokens on left by one step at start *)
      (* Strengthen: if steps (tl, []) ([], X) then steps (tl, [classify b]) ([], [classify b] ++ X) *)
      revert tl. induction tl as [|x xs IHtl]; simpl; intros.
      * inversion H; subst; constructor.
      * inversion H; subst.
        -- constructor.
        -- inversion H2; subst.
           econstructor; [constructor|].
           specialize (IHtl _ H3). exact IHtl.
Qed.

Lemma steps_end_unique_empty : forall bs ts1 ts2,
  steps (bs, []) ([], ts1) -> steps (bs, []) ([], ts2) -> ts1 = ts2.
Proof.
  intros bs ts1 ts2 H1 H2.
  (* By functional equivalence, both equal run bs *)
  pose proof (steps_end_run bs) as Hrun.
  (* Determinism of [steps] to empty-bytes end state: show both sequences yield same tokens *)
  (* Use length of bs to show unique path; alternatively use run equivalence by induction on bs. *)
  revert ts1 ts2 H1 H2. induction bs as [|b tl IH]; intros; simpl in *.
  - inversion H1; subst. inversion H2; subst. reflexivity.
  - inversion H1; subst. inversion H3; subst.
    inversion H2; subst. inversion H6; subst.
    (* Reduce to tail case *)
    apply f_equal with (f:=fun ts => skipn 1 ts). (* crude but aligns shapes *)
    simpl.
    apply IH; assumption.
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
Definition run (bs:list byte) : list token := map classify bs.

Lemma run_app : forall a b, run (a ++ b) = run a ++ run b.
Proof. intros; unfold run; now rewrite map_app. Qed.

(* Window lemma for run. *)
Lemma run_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (run (pre ++ mid ++ suf))) = run mid.
Proof.
  intros pre mid suf. rewrite run_app, app_assoc, run_app.
  rewrite skipn_app, firstn_app, firstn_all.
  replace (skipn (length pre) (run pre)) with (@nil token).
  2:{ rewrite <- firstn_all with (l:=run pre) at 1; rewrite firstn_skipn; reflexivity. }
  simpl. rewrite app_nil_l, firstn_all. reflexivity.
Qed.

(* Offsets as 0..n-1 for run. *)
Fixpoint seq (s n:nat) : list nat := match n with 0=>[] | S k => s :: seq (S s) k end.
Definition offsets (bs:list byte) := seq 0 (length (run bs)).
Definition normalize (k:nat) (xs:list nat) := map (fun o => o - k) xs.

Lemma length_run : forall bs, length (run bs) = length bs.
Proof. intros; unfold run; now rewrite map_length. Qed.

Lemma skipn_seq : forall s n k, skipn k (seq s n) = seq (s+k) (n-k).
Proof.
  intros s n k; revert s n; induction k; intros s n; simpl.
  - now rewrite Nat.sub_0_r.
  - destruct n; simpl; auto. now rewrite IHk.
Qed.

Lemma firstn_seq : forall s n m, firstn m (seq s n) = seq s (Nat.min m n).
Proof.
  intros s n m; revert s n; induction m; intros s n; simpl; auto.
  destruct n; simpl; auto. now rewrite IHm.
Qed.

Lemma offsets_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (offsets (pre ++ mid ++ suf))) =
  seq (length pre) (length mid).
Proof.
  intros pre mid suf. unfold offsets.
  rewrite length_run.
  replace (length (run (pre ++ mid ++ suf))) with (length pre + length mid + length suf) by (rewrite length_run, app_length, length_run, app_length, length_run; lia).
  rewrite skipn_seq, firstn_seq. now rewrite Nat.min_l by lia.
Qed.

Lemma normalized_offsets_window : forall pre mid suf,
  normalize (length pre)
    (firstn (length mid) (skipn (length pre) (offsets (pre ++ mid ++ suf)))) =
  offsets mid.
Proof.
  intros; unfold normalize, offsets; rewrite offsets_window_equivalence.
  (* map (fun o => o - k) (seq k n) = seq 0 n *)
  assert (forall k m, map (fun o => o - k) (seq k m) = seq 0 m) as H.
  { intros k m; revert k; induction m; intros; simpl; auto. now rewrite IHm. }
  now rewrite H.
Qed.

End L0Smallstep.
