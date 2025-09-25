(* LaTeX Perfectionist v25_R1 — Incremental Lexer Foundations (skeleton)
   Zero-admit lemmas to stage windowed determinism/progress proofs. *)

Require Import List Arith Bool Lia.
Import ListNotations.
Require Import ListWindow.
Import ListWindow.

Module Incremental.

(* Executable model over bytes and a trivial tokenization that mirrors bytes. *)
Definition byte := nat.
Definition token := nat.

(* Tokenize function: identity on bytes (1:1 mapping), expressed over lists. *)
Fixpoint tokenize (bs:list byte) : list token :=
  match bs with
  | [] => []
  | b::tl => b :: tokenize tl
  end.

(* Concatenation homomorphism. *)
Lemma tokenize_app : forall a b,
  tokenize (a ++ b) = tokenize a ++ tokenize b.
Proof.
  induction a; simpl; intros; auto.
  now rewrite IHa.
Qed.

(* Determinism is immediate for this functional model. *)
Lemma tokenize_deterministic : forall bs, exists! ts, ts = tokenize bs.
Proof.
  intros. eexists. split; [reflexivity|]. intros x Hx. now subst.
Qed.

Lemma length_tokenize : forall bs, length (tokenize bs) = length bs.
Proof.
  induction bs; simpl; congruence.
Qed.

Lemma firstn_length_append_token :
  forall (xs ys : list token),
    firstn (length xs) (xs ++ ys) = xs.
Proof. apply firstn_length_append. Qed.

Lemma skipn_length_append_token :
  forall (xs ys : list token),
    skipn (length xs) (xs ++ ys) = ys.
Proof. apply skipn_length_append. Qed.

(* Window extraction on the token stream equals tokenization of the window bytes. *)
Lemma tokenize_window_equivalence
      (pre mid suf : list byte) :
  firstn (length mid)
         (skipn (length pre) (tokenize (pre ++ mid ++ suf)))
  = tokenize mid.
Proof.
  rewrite tokenize_app with (a:=pre) (b:=mid ++ suf).
  rewrite <- (length_tokenize pre) at 1.
  rewrite skipn_length_append_token.
  rewrite tokenize_app with (a:=mid) (b:=suf).
  rewrite <- (length_tokenize mid) at 1.
  rewrite firstn_length_append_token.
  reflexivity.
Qed.

(* Locality under disjoint edit: changing the prefix/suffix leaves the mid-window tokens unchanged. *)
Lemma window_locality_under_prefix_change : forall pre1 pre2 mid suf,
  firstn (length mid) (skipn (length pre1) (tokenize (pre1 ++ mid ++ suf))) =
  firstn (length mid) (skipn (length pre2) (tokenize (pre2 ++ mid ++ suf))).
Proof.
  intros. rewrite !tokenize_window_equivalence. reflexivity.
Qed.

(* --- Offsets model and normalized window invariants --- *)

(* Offsets are the 0..n-1 sequence for the tokenization above. *)
Fixpoint seq (start len:nat) : list nat :=
  match len with 0 => [] | S k => start :: seq (S start) k end.

Definition offsets_of (bs:list byte) : list nat := seq 0 (length (tokenize bs)).

(* Normalization of offsets by subtracting a prefix length. *)
Definition normalize (k:nat) (xs:list nat) : list nat := List.map (fun o => o - k) xs.

(* Helpers over seq/firstn/skipn to avoid admits. *)
Lemma length_seq : forall s n, length (seq s n) = n.
Proof.
  intros s n. revert s.
  induction n; intros s; simpl.
  - reflexivity.
  - rewrite (IHn (S s)). reflexivity.
Qed.

Lemma Nat_sub_succ_succ : forall n k, S n - S k = n - k.
Proof.
  intros n k. revert n.
  induction k; intros n; simpl.
  - reflexivity.
  - destruct n; simpl; auto.
Qed.

Lemma Nat_add_succ_comm : forall s k, s + S k = S s + k.
Proof.
  intros s k. induction s; simpl.
  - reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma skipn_seq : forall s n k,
  skipn k (seq s n) = seq (s+k) (n - k).
Proof.
  intros s n k. revert s n.
  induction k; intros s n; simpl.
  - rewrite Nat.add_0_r. destruct n; reflexivity.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + specialize (IHk (S s) n').
      replace (s + S k) with (S s + k) by (symmetry; apply Nat_add_succ_comm).
      exact IHk.
Qed.

Lemma firstn_seq : forall s n m,
  firstn m (seq s n) = seq s (Nat.min m n).
Proof.
  intros s n m. revert s n.
  induction m; intros s n; simpl; auto.
  destruct n; simpl; auto. now rewrite IHm.
Qed.

Lemma seq_succ : forall s n,
  seq (S s) n = map S (seq s n).
Proof.
  intros s n. revert s.
  induction n; intros s; simpl; auto.
  rewrite IHn with (s := S s). reflexivity.
Qed.

Lemma seq_shift : forall k m,
  seq k m = map (fun i => k + i) (seq 0 m).
Proof.
  intros k m. revert k.
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
  intros k i. lia.
Qed.

Lemma map_sub_seq : forall k m,
  map (fun o => o - k) (seq k m) = seq 0 m.
Proof.
  intros k m.
  rewrite seq_shift.
  rewrite map_map.
  assert (map (fun i => (k + i) - k) (seq 0 m) = map (fun i => i) (seq 0 m)) as ->.
  { apply map_ext_in. intros i _. now rewrite add_sub_cancel. }
  now rewrite map_id.
Qed.

Lemma normalize_seq : forall k m,
  normalize k (seq k m) = seq 0 m.
Proof.
  intros k m. unfold normalize. apply map_sub_seq.
Qed.

Lemma offsets_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf))) =
  seq (length pre) (length mid).
Proof.
  intros pre mid suf. unfold offsets_of.
  rewrite length_tokenize.
  replace (length (tokenize (pre ++ mid ++ suf))) with (length (pre ++ mid ++ suf)) by now rewrite length_tokenize.
  rewrite app_length, app_length.
  set (npre := length pre). set (nmid := length mid). set (nsuf := length suf).
  rewrite skipn_seq.
  rewrite firstn_seq.
  rewrite Nat.min_l; [reflexivity|]. lia.
Qed.

Lemma normalized_offsets_window : forall pre mid suf,
  normalize (length pre)
    (firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf)))) =
  offsets_of mid.
Proof.
  intros pre mid suf.
  rewrite offsets_window_equivalence.
  rewrite (normalize_seq (length pre) (length mid)).
  unfold offsets_of. now rewrite length_tokenize.
Qed.

(* --- Multi-window arithmetic and smallstep relation for outside edits --- *)

Lemma seq_app : forall s n m,
  seq s n ++ seq (s+n) m = seq s (n+m).
Proof.
  intros s n m. revert s m. induction n; intros s m; simpl; auto.
  simpl. f_equal.
  rewrite <- Nat.add_succ_comm.
  apply IHn.
Qed.

(* Smallstep edits that change only prefix/suffix, not the mid bytes. *)
Inductive step_outside : list byte -> list byte -> list byte -> list byte -> list byte -> Prop :=
| StepPrefix : forall pre1 pre2 mid suf, step_outside pre1 mid suf pre2 suf
| StepSuffix : forall pre mid suf1 suf2, step_outside pre mid suf1 pre suf2.

Lemma step_outside_preserves_mid_tokens : forall pre mid suf pre' suf',
  step_outside pre mid suf pre' suf' ->
  firstn (length mid) (skipn (length pre) (tokenize (pre ++ mid ++ suf))) =
  firstn (length mid) (skipn (length pre') (tokenize (pre' ++ mid ++ suf'))).
Proof.
  intros pre mid suf pre' suf' H.
  destruct H; rewrite !tokenize_window_equivalence; reflexivity.
Qed.

Lemma step_outside_preserves_mid_offsets_normalized : forall pre mid suf pre' suf',
  step_outside pre mid suf pre' suf' ->
  normalize (length pre)
    (firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf)))) =
  normalize (length pre')
    (firstn (length mid) (skipn (length pre') (offsets_of (pre' ++ mid ++ suf')))).
Proof.
  intros pre mid suf pre' suf' H.
  destruct H; repeat rewrite normalized_offsets_window; reflexivity.
Qed.

(* Reflexive–transitive closure of outside edits *)
Inductive steps_outside : list byte -> list byte -> list byte -> list byte -> list byte -> Prop :=
| SO_Refl : forall pre mid suf, steps_outside pre mid suf pre suf
| SO_Step : forall pre mid suf pre1 suf1 pre2 suf2,
    step_outside pre mid suf pre1 suf1 ->
    steps_outside pre1 mid suf1 pre2 suf2 ->
    steps_outside pre mid suf pre2 suf2.

Lemma steps_outside_preserves_mid_tokens : forall pre mid suf pre' suf',
  steps_outside pre mid suf pre' suf' ->
  firstn (length mid) (skipn (length pre) (tokenize (pre ++ mid ++ suf))) =
  firstn (length mid) (skipn (length pre') (tokenize (pre' ++ mid ++ suf'))).
Proof.
  intros pre mid suf pre' suf' H; induction H.
  - reflexivity.
  - etransitivity; [apply step_outside_preserves_mid_tokens; eauto| exact IHsteps_outside].
Qed.

Lemma steps_outside_preserves_mid_offsets_normalized : forall pre mid suf pre' suf',
  steps_outside pre mid suf pre' suf' ->
  normalize (length pre)
    (firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf)))) =
  normalize (length pre')
    (firstn (length mid) (skipn (length pre') (offsets_of (pre' ++ mid ++ suf')))).
Proof.
  intros pre mid suf pre' suf' H; induction H.
  - reflexivity.
  - etransitivity; [apply step_outside_preserves_mid_offsets_normalized; eauto| exact IHsteps_outside].
Qed.

(* --- Concrete edits inside the window (insert/delete at head) --- *)

Inductive mid_edit : list byte -> list byte -> Prop :=
| ME_InsertHead : forall b mid, mid_edit mid (b :: mid)
| ME_DeleteHead : forall (x:byte) xs, mid_edit (x :: xs) xs.

Lemma normalized_offsets_window_insert_head : forall pre mid suf b,
  normalize (length pre)
    (firstn (length (b::mid)) (skipn (length pre) (offsets_of (pre ++ (b::mid) ++ suf))))
  = offsets_of (b::mid).
Proof.
  intros. rewrite normalized_offsets_window. reflexivity.
Qed.

Lemma normalized_offsets_window_delete_head : forall pre (x:byte) xs suf,
  normalize (length pre)
    (firstn (length xs) (skipn (length pre) (offsets_of (pre ++ xs ++ suf))))
  = offsets_of xs.
Proof.
  intros. rewrite normalized_offsets_window. reflexivity.
Qed.

Lemma mid_edit_normalized_offsets : forall pre mid' mid suf,
  mid_edit mid mid' ->
  normalize (length pre)
    (firstn (length mid') (skipn (length pre) (offsets_of (pre ++ mid' ++ suf))))
  = offsets_of mid'.
Proof.
  intros pre mid' mid suf H.
  destruct H; [apply normalized_offsets_window_insert_head|apply normalized_offsets_window].
Qed.

(* General edits at arbitrary position: split mid = l ++ r *)
Inductive mid_edit_at : list byte -> list byte -> Prop :=
| MEA_Insert : forall l r b, mid_edit_at (l ++ r) (l ++ b :: r)
| MEA_Delete : forall l (x:byte) r, mid_edit_at (l ++ x :: r) (l ++ r).

Lemma tokenize_window_equivalence_edit_at : forall pre mid mid' suf,
  mid_edit_at mid mid' ->
  firstn (length mid') (skipn (length pre) (tokenize (pre ++ mid' ++ suf))) = tokenize mid'.
Proof.
  intros. apply tokenize_window_equivalence.
Qed.

Lemma mid_edit_at_normalized_offsets : forall pre mid mid' suf,
  mid_edit_at mid mid' ->
  normalize (length pre)
    (firstn (length mid') (skipn (length pre) (offsets_of (pre ++ mid' ++ suf))))
  = offsets_of mid'.
Proof.
  intros. apply normalized_offsets_window.
Qed.

(* Split-based offset composition lemmas *)
Lemma normalized_offsets_split : forall pre l r suf,
  normalize (length pre)
    (firstn (length (l ++ r)) (skipn (length pre) (offsets_of (pre ++ (l ++ r) ++ suf))))
  = seq 0 (length l) ++ seq (length l) (length r).
Proof.
  intros. rewrite normalized_offsets_window.
  unfold offsets_of.
  rewrite length_tokenize.
  rewrite app_length.
  rewrite <- (seq_app 0 (length l) (length r)).
  now rewrite Nat.add_0_l.
Qed.

Lemma normalized_offsets_insert_at_split : forall pre l r b suf,
  normalize (length pre)
    (firstn (length (l ++ b :: r)) (skipn (length pre) (offsets_of (pre ++ (l ++ b :: r) ++ suf))))
  = seq 0 (length l) ++ length l :: seq (S (length l)) (length r).
Proof.
  intros. rewrite normalized_offsets_window.
  unfold offsets_of.
  (* offsets_of (l ++ b :: r) = seq 0 (|l|+1+|r|) = seq 0 |l| ++ seq |l| (1+|r|) then shift rhs by 1 *)
  rewrite length_tokenize.
  rewrite app_length. simpl.
  rewrite <- (seq_app 0 (length l) (S (length r))).
  rewrite Nat.add_0_l.
  simpl.
  reflexivity.
Qed.

Lemma normalized_offsets_delete_at_split : forall pre l (x:byte) r suf,
  normalize (length pre)
    (firstn (length (l ++ r)) (skipn (length pre) (offsets_of (pre ++ (l ++ r) ++ suf))))
  = seq 0 (length l) ++ seq (length l) (length r).
Proof.
  intros. apply normalized_offsets_split.
Qed.

End Incremental.
Local Open Scope nat_scope.

(* Corollaries combining outside edits with mid edits *)
Module Incremental_Corollaries.
  Import Incremental.

  Lemma outside_then_mid_window_tokens : forall pre pre' mid mid' suf suf',
    steps_outside pre mid suf pre' suf' -> mid_edit_at mid mid' ->
    firstn (length mid') (skipn (length pre') (tokenize (pre' ++ mid' ++ suf'))) = tokenize mid'.
  Proof.
    intros. apply tokenize_window_equivalence.
  Qed.

  Lemma outside_then_mid_window_offsets_normalized : forall pre pre' mid mid' suf suf',
    steps_outside pre mid suf pre' suf' -> mid_edit_at mid mid' ->
    normalize (length pre')
      (firstn (length mid') (skipn (length pre') (offsets_of (pre' ++ mid' ++ suf')))) =
    offsets_of mid'.
  Proof.
    intros. apply normalized_offsets_window.
  Qed.
End Incremental_Corollaries.
