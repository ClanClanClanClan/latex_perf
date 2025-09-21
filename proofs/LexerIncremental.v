(* LaTeX Perfectionist v25_R1 — Incremental Lexer Foundations (skeleton)
   Zero-admit lemmas to stage windowed determinism/progress proofs. *)

Require Import List Arith Bool Lia.
Import ListNotations.

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

(* Window extraction on the token stream equals tokenization of the window bytes. *)
Lemma tokenize_window_equivalence : forall pre mid suf,
  firstn (length mid) (skipn (length pre) (tokenize (pre ++ mid ++ suf))) = tokenize mid.
Proof.
  intros pre mid suf.
  rewrite tokenize_app.
  rewrite app_assoc.
  rewrite tokenize_app.
  rewrite skipn_app.
  rewrite firstn_app.
  rewrite firstn_all.
  replace (skipn (length pre) (tokenize pre)) with (@nil token).
  2:{ rewrite <- firstn_all with (l:=tokenize pre) at 1.
      rewrite firstn_skipn. reflexivity. }
  simpl. rewrite app_nil_l.
  rewrite firstn_all. reflexivity.
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

Lemma length_tokenize : forall bs, length (tokenize bs) = length bs.
Proof. induction bs; simpl; congruence. Qed.

(* Helpers over seq/firstn/skipn to avoid admits. *)
Lemma length_seq : forall s n, length (seq s n) = n.
Proof. induction n; simpl; congruence. Qed.

Lemma skipn_seq : forall s n k,
  skipn k (seq s n) = seq (s+k) (n - k).
Proof.
  intros s n k. revert s n.
  induction k; intros s n; simpl.
  - now rewrite Nat.sub_0_r.
  - destruct n; simpl; [now rewrite Nat.sub_0_r|]. now apply IHk.
Qed.

Lemma firstn_seq : forall s n m,
  firstn m (seq s n) = seq s (Nat.min m n).
Proof.
  intros s n m. revert s n.
  induction m; intros s n; simpl; auto.
  destruct n; simpl; auto. now rewrite IHm.
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
  intros. unfold normalize, offsets_of.
  rewrite offsets_window_equivalence.
  (* normalize seq(pre, len(mid)) → seq(0, len(mid)) *)
  revert pre mid suf. intros pre mid suf.
  (* map (fun o => o - pre) (seq pre (length mid)) = seq 0 (length mid) *)
  (* Prove normalization on seq directly. *)
  assert (forall k m, map (fun o => o - k) (seq k m) = seq 0 m) as Hnorm.
  { intros k m. revert k. induction m; intros k; simpl; auto. now rewrite IHm. }
  rewrite Hnorm. unfold offsets_of. now rewrite length_tokenize.
Qed.

(* --- Multi-window arithmetic and smallstep relation for outside edits --- *)

Lemma seq_app : forall s n m,
  seq s n ++ seq (s+n) m = seq s (n+m).
Proof.
  intros s n m. revert s m. induction n; intros s m; simpl; auto.
  now rewrite IHn.
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
  destruct H; rewrite !offsets_window_equivalence.
  all: (* map (fun o => o - k) (seq k (len mid)) = seq 0 (len mid) *)
       assert (forall k m, map (fun o => o - k) (seq k m) = seq 0 m) as Hnorm by
           (intros k m; revert k; induction m; intros; simpl; auto; now rewrite IHm);
       rewrite !Hnorm; reflexivity.
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
| ME_DeleteHead : forall x xs, mid_edit (x :: xs) xs.

Lemma normalized_offsets_window_insert_head : forall pre mid suf b,
  normalize (length pre)
    (firstn (length (b::mid)) (skipn (length pre) (offsets_of (pre ++ (b::mid) ++ suf))))
  = offsets_of (b::mid).
Proof.
  intros. rewrite normalized_offsets_window. reflexivity.
Qed.

Lemma normalized_offsets_window_delete_head : forall pre x xs suf,
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
| MEA_Delete : forall l x r, mid_edit_at (l ++ x :: r) (l ++ r).

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
  (* offsets_of (l ++ r) = seq 0 (|l|+|r|) = seq 0 |l| ++ seq |l| |r| *)
  rewrite app_length.
  replace (seq 0 (length l + length r)) with (seq 0 (length l) ++ seq (length l) (length r)).
  2:{
    revert l r. intros l r. induction l; simpl; auto.
    now rewrite IHl.
  }
  reflexivity.
Qed.

Lemma normalized_offsets_insert_at_split : forall pre l r b suf,
  normalize (length pre)
    (firstn (length (l ++ b :: r)) (skipn (length pre) (offsets_of (pre ++ (l ++ b :: r) ++ suf))))
  = seq 0 (length l) ++ seq (length l + 1) (length r).
Proof.
  intros. rewrite normalized_offsets_window.
  (* offsets_of (l ++ b :: r) = seq 0 (|l|+1+|r|) = seq 0 |l| ++ seq |l| (1+|r|) then shift rhs by 1 *)
  rewrite app_length. simpl.
  (* seq 0 (|l|+1+|r|) = (seq 0 |l|) ++ seq |l| (1+|r|) *)
  replace (seq 0 (length l + (1 + length r))) with (seq 0 (length l) ++ seq (length l) (1 + length r)).
  2:{
    revert l r. intros l r. induction l; simpl; auto. now rewrite IHl.
  }
  (* Now drop the first element of the second seq to express it as starting at |l|+1 of length |r| *)
  simpl. (* we want: seq (length l) (1+|r|) = (length l) :: seq (length l + 1) |r| *)
  reflexivity.
Qed.

Lemma normalized_offsets_delete_at_split : forall pre l x r suf,
  normalize (length pre)
    (firstn (length (l ++ r)) (skipn (length pre) (offsets_of (pre ++ (l ++ r) ++ suf))))
  = seq 0 (length l) ++ seq (length l) (length r).
Proof.
  intros. apply normalized_offsets_split.
Qed.

(* Index-based contextual mapping for normalized offsets under pre/suf *)
Lemma normalized_offsets_insert_at_index_map_pre_suf : forall pre mid suf k b,
  k <= length mid ->
  let l := firstn k mid in
  let r := skipn k mid in
  map (fun o => if o <? length l then o else S o)
    (normalize (length pre)
      (firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf))))) =
  normalize (length pre)
    (firstn (length (l ++ b :: r)) (skipn (length pre) (offsets_of (pre ++ (l ++ b :: r) ++ suf)))).
Proof.
  intros pre mid suf k b Hk l r.
  rewrite normalized_offsets_window.
  (* length mid = length l + length r *)
  assert (length mid = length l + length r) as HL.
  { subst l r. rewrite <- firstn_skipn with (l:=mid) (n:=k) at 1.
    rewrite app_length. now rewrite !firstn_length, !skipn_length; lia. }
  rewrite HL. now apply map_shift_insert_seq.
Qed.

Lemma normalized_offsets_delete_at_index_map_pre_suf : forall pre mid suf k,
  k < length mid ->
  let l := firstn k mid in
  let r := skipn (S k) mid in
  map (fun o => if o <? length l then o else o - 1)
    (remove_nth (length l)
      (normalize (length pre)
        (firstn (length mid) (skipn (length pre) (offsets_of (pre ++ mid ++ suf)))))) =
  normalize (length pre)
    (firstn (length (l ++ r)) (skipn (length pre) (offsets_of (pre ++ (l ++ r) ++ suf)))).
Proof.
  intros pre mid suf k Hlt l r.
  rewrite normalized_offsets_window.
  assert (length mid = length l + S (length r)) as HL.
  { subst l r. rewrite <- firstn_skipn with (l:=mid) (n:=k) at 1.
    rewrite app_length. simpl. now rewrite !firstn_length, !skipn_length; lia. }
  rewrite HL. now apply map_shift_delete_seq.
Qed.

(* --- Mapping lemmas for explicit shift at index k --- *)

Fixpoint remove_nth (k:nat) (xs:list nat) : list nat :=
  match k, xs with
  | 0, _ :: tl => tl
  | S k', x :: tl => x :: remove_nth k' tl
  | _, [] => []
  end.

Lemma map_seq_S : forall s n, map S (seq s n) = seq (S s) n.
Proof.
  intros s n. revert s. induction n; intros s; simpl; auto.
  now rewrite IHn.
Qed.

(* --- Token alignment lemmas for insert/delete at arbitrary split --- *)

Lemma tokenize_insert_at_split : forall l r b,
  tokenize (l ++ b :: r) = tokenize l ++ b :: tokenize r.
Proof.
  intros. rewrite tokenize_app. simpl. reflexivity.
Qed.

Lemma tokenize_delete_at_split : forall l x r,
  tokenize (l ++ r) = tokenize l ++ tokenize r.
Proof.
  intros. now rewrite tokenize_app.
Qed.

Lemma mid_edit_at_tokenize_alignment : forall l r mid',
  mid_edit_at (l ++ r) mid' ->
  (exists b, tokenize mid' = tokenize l ++ b :: tokenize r) \/
  (tokenize mid' = tokenize l ++ tokenize r).
Proof.
  intros l r mid' H.
  inversion H; subst; [left; eexists; apply tokenize_insert_at_split|right; apply tokenize_delete_at_split].
Qed.

Lemma map_pred_seq : forall k m,
  map (fun o => o - 1) (seq (S k) m) = seq k m.
Proof.
  intros k m. revert k. induction m; intros k; simpl; auto.
  rewrite IHm. reflexivity.
Qed.

Lemma remove_nth_seq : forall k m,
  remove_nth k (seq 0 (S (k + m))) = seq 0 k ++ seq (S k) m.
Proof.
  intros k m. revert m. induction k; intros m; simpl.
  - (* k=0 *)
    simpl. reflexivity.
  - (* k=S k' *)
    simpl. rewrite IHk. reflexivity.
Qed.

Lemma map_shift_insert_seq : forall k m,
  map (fun o => if o <? k then o else S o) (seq 0 (k + m)) = seq 0 k ++ seq (S k) m.
Proof.
  intros k m.
  (* split sequence at k *)
  replace (seq 0 (k + m)) with (seq 0 k ++ seq k m).
  2:{
    revert m. induction k; intros m; simpl; auto.
    now rewrite IHk.
  }
  rewrite map_app. f_equal.
  - (* first part: o < k so identity *)
    induction k; simpl; auto. now rewrite IHk.
  - (* second part: o >= k so S o maps seq k m to seq (S k) m *)
    replace (map (fun o => if o <? k then o else S o) (seq k m)) with (map S (seq k m)).
    2:{
      revert k. induction m; intros k; simpl; auto.
      rewrite IHm. reflexivity.
    }
    (* Now shift seq by S *)
    revert k. induction m; intros k; simpl; auto.
    now rewrite IHm.
Qed.

Lemma map_shift_delete_seq : forall k m,
  map (fun o => if o <? k then o else o - 1) (remove_nth k (seq 0 (S (k + m)))) =
  seq 0 k ++ seq k m.
Proof.
  intros k m.
  rewrite remove_nth_seq.
  rewrite map_app. f_equal.
  - (* first part: o < k so identity *)
    induction k; simpl; auto. now rewrite IHk.
  - (* second part: o >= k so subtract 1 *)
    replace (map (fun o => if o <? k then o else o - 1) (seq (S k) m)) with (map (fun o => o - 1) (seq (S k) m)).
    2:{
      revert k. induction m; intros k; simpl; auto. now rewrite IHm.
    }
    now apply map_pred_seq.
Qed.

(* Index-based insert/delete lemmas using splits at k via firstn/skipn *)
Lemma tokenize_insert_at_index : forall (mid:list byte) k b,
  k <= length mid ->
  let l := firstn k mid in
  let r := skipn k mid in
  tokenize (l ++ b :: r) = tokenize l ++ b :: tokenize r.
Proof.
  intros mid k b Hk l r. apply tokenize_insert_at_split.
Qed.

Lemma tokenize_delete_at_index : forall (mid:list byte) k x,
  k < length mid ->
  let l := firstn k mid in
  let r := skipn (S k) mid in
  tokenize (l ++ r) = tokenize l ++ tokenize r.
Proof.
  intros mid k x Hk l r. apply tokenize_delete_at_split.
Qed.

Lemma offsets_insert_at_index_map : forall (mid:list byte) k b,
  k <= length mid ->
  let l := firstn k mid in
  let r := skipn k mid in
  map (fun o => if o <? length l then o else S o) (offsets_of (l ++ r)) = offsets_of (l ++ b :: r).
Proof.
  intros mid k b Hk l r.
  unfold offsets_of.
  rewrite app_length.
  (* offsets_of (l++r) = seq 0 (|l|+|r|) *)
  replace (length (tokenize (l ++ r))) with (length l + length r) by (rewrite tokenize_app, !length_tokenize; lia).
  rewrite map_shift_insert_seq with (k:=length l) (m:=length r).
  (* RHS offsets_of (l++b::r) equals seq 0 |l| ++ seq (|l|+1) |r| *)
  rewrite app_length. simpl.
  replace (length (tokenize (l ++ b :: r))) with (length l + 1 + length r) by (rewrite tokenize_app, !length_tokenize; simpl; lia).
  reflexivity.
Qed.

Lemma offsets_delete_at_index_map : forall (mid:list byte) k x,
  k < length mid ->
  let l := firstn k mid in
  let r := skipn (S k) mid in
  map (fun o => if o <? length l then o else o - 1)
      (remove_nth (length l) (offsets_of (l ++ x :: r))) =
  offsets_of (l ++ r).
Proof.
  intros mid k x Hk l r.
  unfold offsets_of.
  rewrite app_length. simpl.
  replace (length (tokenize (l ++ x :: r))) with (length l + 1 + length r) by (rewrite tokenize_app, !length_tokenize; simpl; lia).
  rewrite map_shift_delete_seq with (k:=length l) (m:=length r).
  replace (length (tokenize (l ++ r))) with (length l + length r) by (rewrite tokenize_app, !length_tokenize; lia).
  reflexivity.
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
