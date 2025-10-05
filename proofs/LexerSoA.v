From Coq Require Import List Arith Lia.
Require Import Catcode.
Import ListNotations.

(* A simple SoA-style lexer small-step: input is a list of bytes; output is
   three parallel arrays (lists) for kinds, offsets, and codes. One step
   consumes one byte and appends one entry to each array. *)

Module L0SoA.

  Definition byte := nat.
  Definition kind := nat.
  Definition code := nat.
  Definition offset := nat.
  Definition issue := nat.

  Record state := {
    inp : list byte;
    kinds : list kind;
    offs : list offset;
    codes : list code
  }.

  (* Total classifiers (placeholders for real ones). *)
  (* Faithful ASCII catcode mapping to a 0..15 kind code. *)
  Definition catcode_to_kind (c:Catcode.catcode) : kind :=
    match c with
    | Catcode.Escape => 0 | Catcode.BeginGrp => 1 | Catcode.EndGrp => 2 | Catcode.Math => 3
    | Catcode.AlignTab => 4 | Catcode.Newline => 5 | Catcode.Param => 6 | Catcode.Superscr => 7
    | Catcode.Subscr => 8 | Catcode.Ignored => 9 | Catcode.Space => 10 | Catcode.Letter => 11
    | Catcode.Other => 12 | Catcode.Active => 13 | Catcode.Comment => 14 | Catcode.Invalid => 15
    end.

  Definition classify_kind (b:byte) : kind :=
    let c := Catcode.classify_ascii b in catcode_to_kind c.

  Definition classify_code (b:byte) : code := b.

  (* Example issue classifier: mark issue code 1 on NUL bytes; otherwise None. *)
  Definition classify_issue (b:byte) : option issue := if Nat.eqb b 0 then Some 1 else None.

  Fixpoint issues_from (i:list byte) : list (option issue) :=
    match i with
    | [] => []
    | b::rest => classify_issue b :: issues_from rest
    end.

  Lemma issues_app : forall a b,
    issues_from (a ++ b) = issues_from a ++ issues_from b.
  Proof.
    induction a as [|x xs IH]; intros b; simpl; [reflexivity|now rewrite IH].
  Qed.

  Lemma issues_skipn_prefix : forall pre rest,
    skipn (length pre) (issues_from (pre ++ rest)) = issues_from rest.
  Proof.
    induction pre as [|b pre IH]; intros rest; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma issues_firstn_prefix : forall pre rest,
    firstn (length pre) (issues_from (pre ++ rest)) = issues_from pre.
  Proof.
    induction pre as [|b pre IH]; intros rest; simpl.
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  Lemma issues_length : forall i, length (issues_from i) = length i.
  Proof.
    induction i as [|b rest IH]; simpl; [reflexivity|now rewrite IH].
  Qed.

  (* The next offset is the current number of tokens (SoA length). *)
  Definition next_offset (s:state) : offset := length (kinds s).

  Inductive step : state -> state -> Prop :=
  | Step : forall b rest ks os cs,
      b < 256 ->
      step {| inp := b :: rest; kinds := ks; offs := os; codes := cs |}
           {| inp := rest;
              kinds := ks ++ [classify_kind b];
              offs := os ++ [length ks];
              codes := cs ++ [classify_code b] |}.

  Theorem step_deterministic : forall s s1 s2,
    step s s1 -> step s s2 -> s1 = s2.
  Proof.
    intros s s1 s2 H1 H2.
    inversion H1; subst.
    inversion H2; subst.
    repeat match goal with
           | H : {| inp := _; kinds := _; offs := _; codes := _ |} = _ |- _ =>
               inversion H; subst; clear H
           end.
    reflexivity.
  Qed.

  (* Issues window locality *)
  Lemma issues_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (issues_from (pre ++ mid ++ post)))
    = issues_from mid.
  Proof.
    intros pre mid post.
    set (rest := mid ++ post).
    replace (issues_from (pre ++ mid ++ post))
      with (issues_from (pre ++ rest)) by (subst rest; rewrite app_assoc; reflexivity).
    rewrite issues_skipn_prefix with (pre := pre) (rest := rest).
    subst rest.
    rewrite issues_firstn_prefix with (pre := mid) (rest := post).
    reflexivity.
  Qed.

  Lemma issues_prefix_invariance : forall pre mid post,
    firstn (length pre) (issues_from (pre ++ mid ++ post)) = issues_from pre.
  Proof.
    intros pre mid post.
    set (rest := mid ++ post).
    replace (issues_from (pre ++ mid ++ post))
      with (issues_from (pre ++ rest)) by (subst rest; rewrite app_assoc; reflexivity).
    rewrite issues_firstn_prefix with (pre := pre) (rest := rest).
    reflexivity.
  Qed.

  Lemma issues_suffix_invariance : forall pre mid post,
    skipn (length pre + length mid) (issues_from (pre ++ mid ++ post)) = issues_from post.
  Proof.
    intros pre mid post.
    set (rest := mid ++ post).
    replace (issues_from (pre ++ mid ++ post))
      with (issues_from (pre ++ rest)) by (subst rest; rewrite app_assoc; reflexivity).
    rewrite Nat.add_comm.
    rewrite <- skipn_skipn.
    rewrite issues_skipn_prefix with (pre := pre) (rest := rest).
    subst rest.
    rewrite issues_skipn_prefix with (pre := mid) (rest := post).
    reflexivity.
  Qed.

  (* classify_kind result is always in 0..15 per mapping. *)
  Lemma classify_kind_bound : forall b, classify_kind b < 16.
  Proof.
    intro b. unfold classify_kind, catcode_to_kind.
    destruct (Catcode.classify_ascii b); lia.
  Qed.

  Theorem step_progress : forall s,
    s.(inp) <> [] ->
    Forall (fun b => b < 256) s.(inp) ->
    exists s', step s s'.
  Proof.
    intros [i ks os cs] Hne Hall.
    destruct i as [|b rest]; [contradiction|].
    inversion Hall; subst.
    exists {| inp := rest;
              kinds := ks ++ [classify_kind b];
              offs := os ++ [length ks];
              codes := cs ++ [classify_code b] |}.
    constructor; assumption.
  Qed.

  (* Functional big-step to ease locality/spec proofs. *)
  Fixpoint run_from (ks : list kind) (os : list offset) (cs : list code) (i : list byte)
    : (list kind * list offset * list code) :=
    match i with
    | [] => (ks, os, cs)
    | b::rest =>
        let ks' := ks ++ [classify_kind b] in
        let os' := os ++ [length ks] in
        let cs' := cs ++ [classify_code b] in
        run_from ks' os' cs' rest
    end.

  Definition run (i:list byte) : state :=
    let '(ks,os,cs) := run_from [] [] [] i in {| inp := []; kinds := ks; offs := os; codes := cs |}.

  Lemma run_from_app : forall ks os cs i1 i2,
    run_from ks os cs (i1 ++ i2) =
    let '(ks1,os1,cs1) := run_from ks os cs i1 in run_from ks1 os1 cs1 i2.
  Proof.
    revert ks os cs.
    induction i1 as [|b rest IH]; intros ks os cs i2; simpl.
    - reflexivity.
    - destruct (run_from (ks ++ [classify_kind b])
                        (os ++ [length ks])
                        (cs ++ [classify_code b]) rest) as [[ks1 os1] cs1] eqn:E.
      specialize (IH (ks ++ [classify_kind b])
                    (os ++ [length ks])
                    (cs ++ [classify_code b]) i2).
      rewrite E in IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma run_from_props : forall ks os cs i ks' os' cs',
    run_from ks os cs i = (ks', os', cs') ->
    length ks' = length cs' /\ length os' = length ks' /\
    ks' = ks ++ List.map classify_kind i /\
    cs' = cs ++ List.map classify_code i /\
    os' = os ++ List.seq (length ks) (length i).
  Proof.
    induction i as [|b rest IH]; intros ks os cs ks' os' cs' H; simpl in H.
    - inversion H; subst; repeat split; try reflexivity.
    - remember (ks ++ [classify_kind b]) as ks1.
      remember (os ++ [length ks]) as os1.
      remember (cs ++ [classify_code b]) as cs1.
      specialize (IH ks1 os1 cs1 ks' os' cs').
      apply IH in H as (Hkc & Hos & Hks & Hcs & Hos'); subst ks1 os1 cs1.
      repeat split.
      + rewrite app_length in Hkc; simpl in Hkc; exact Hkc.
      + rewrite app_length in Hos; simpl in Hos; exact Hos.
      + now rewrite Hks, <- app_assoc.
      + now rewrite Hcs, <- app_assoc.
      + rewrite Hos'.
        rewrite app_length; simpl.
        (* seq a (S n) = seq a n ++ [a+n] *)
        rewrite List.seq_app; [reflexivity|].
        all: lia.
  Qed.

  Lemma run_lengths : forall i,
    let s := run i in length (kinds s) = length (offs s) /\ length (kinds s) = length (codes s) /\ length (kinds s) = length i.
  Proof.
    intros i; unfold run.
    destruct (run_from [] [] [] i) as [[ks os] cs] eqn:E.
    specialize (run_from_props [] [] [] i ks os cs E) as (Hkc & Hos & Hks & _ & _).
    repeat split; auto.
    - now rewrite Hks, app_length, map_length.
  Qed.

  Lemma run_app : forall a b,
    kinds (run (a ++ b)) = kinds (run a) ++ kinds (run b) /\
    codes (run (a ++ b)) = codes (run a) ++ codes (run b) /\
    offs (run (a ++ b)) = offs (run a) ++ List.seq (length (kinds (run a))) (length b).
  Proof.
    intros a b.
    unfold run.
    repeat
      match goal with
      | |- context [run_from [] [] [] (a ++ b)] => rewrite run_from_app
      end.
    destruct (run_from [] [] [] a) as [[ksa osa] csa] eqn:EA.
    destruct (run_from ksa osa csa b) as [[ksb osb] csb] eqn:EB.
    destruct (run_from [] [] [] b) as [[ksb0 osb0] csb0] eqn:EB0.
    specialize (run_from_props [] [] [] a ksa osa csa EA) as (_&_&Hksa&_&Hosa).
    specialize (run_from_props [] [] [] b ksb0 osb0 csb0 EB0) as (_&_&Hksb0&Hcsb0&Hosb0).
    specialize (run_from_props ksa osa csa b ksb osb csb EB) as (_&_&Hksb&Hcsb&Hosb).
    subst.
    repeat split; auto.
    - now rewrite Hksb, Hksb0.
    - now rewrite Hcsb, Hcsb0.
    - now rewrite Hosb0, Hosb, Hosa, app_assoc.
  Qed.

  Lemma kinds_run_length : forall i, length (kinds (run i)) = length i.
  Proof.
    intros i. pose proof (run_lengths i) as (A&_&C).
    exact C.
  Qed.

  Lemma kinds_run_app3 : forall a b c,
    kinds (run (a ++ b ++ c)) = kinds (run a) ++ kinds (run b) ++ kinds (run c).
  Proof.
    intros a b c.
    destruct (run_app a (b ++ c)) as (K1&_&_).
    destruct (run_app b c) as (K2&_&_).
    now rewrite K1, K2, app_assoc.
  Qed.

  Lemma codes_run_app3 : forall a b c,
    codes (run (a ++ b ++ c)) = codes (run a) ++ codes (run b) ++ codes (run c).
  Proof.
    intros a b c.
    destruct (run_app a (b ++ c)) as (_&C1&_).
    destruct (run_app b c) as (_&C2&_).
    now rewrite C1, C2, app_assoc.
  Qed.

  (* Window locality for kinds/codes: mid segment extracted from full run equals
     the run of the mid window, using firstn/skipn and length equalities. *)
  Lemma kinds_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (kinds (run (pre ++ mid ++ post))))
    = kinds (run mid).
  Proof.
    intros pre mid post.
    rewrite kinds_run_app3.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag.
    simpl.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_0_r.
    simpl. now rewrite firstn_O.
  Qed.

  Lemma codes_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (codes (run (pre ++ mid ++ post))))
    = codes (run mid).
  Proof.
    intros pre mid post.
    rewrite codes_run_app3.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag.
    simpl.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_0_r.
    simpl. now rewrite firstn_O.
  Qed.

  Lemma offs_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (offs (run (pre ++ mid ++ post))))
    = List.seq (length (kinds (run pre))) (length mid).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (_&_&O1).
    rewrite O1.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_0_r; simpl.
    now rewrite firstn_O.
  Qed.

  (* Helpers about seq and normalization of offsets *)
  Lemma map_minus_seq_succ : forall base n,
    List.map (fun x => x - base) (List.seq (S base) n) = List.seq 1 n.
  Proof.
    induction n as [|n IH]; simpl; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  Lemma map_minus_seq : forall base n,
    List.map (fun x => x - base) (List.seq base n) = List.seq 0 n.
  Proof.
    intros base n.
    destruct n; simpl; [reflexivity|].
    rewrite map_minus_seq_succ. reflexivity.
  Qed.

  (* Normalized offsets window equivalence: window offsets, after subtracting the
     base (length of kinds before the window), are canonical seq 0..len-1. *)
  Lemma offs_window_mid_normalized : forall pre mid post,
    List.map (fun o => o - length (kinds (run pre)))
      (firstn (length mid)
        (skipn (length pre) (offs (run (pre ++ mid ++ post)))))
    = List.seq 0 (length mid).
  Proof.
    intros pre mid post.
    rewrite offs_window_mid.
    rewrite map_minus_seq. reflexivity.
  Qed.

  (* Stability under edits outside window (kinds/codes): if two inputs share the
     same mid window, the mid kinds/codes match. Offsets differ by a base shift
     captured by normalization. *)
  Lemma kinds_window_stability : forall pre1 pre2 mid post1 post2,
    firstn (length mid) (skipn (length pre1) (kinds (run (pre1 ++ mid ++ post1))))
    = firstn (length mid) (skipn (length pre2) (kinds (run (pre2 ++ mid ++ post2)))).
  Proof.
    intros. now rewrite !kinds_window_mid.
  Qed.

  Lemma codes_window_stability : forall pre1 pre2 mid post1 post2,
    firstn (length mid) (skipn (length pre1) (codes (run (pre1 ++ mid ++ post1))))
    = firstn (length mid) (skipn (length pre2) (codes (run (pre2 ++ mid ++ post2)))).
  Proof.
    intros. now rewrite !codes_window_mid.
  Qed.

  Lemma offs_window_stability_normalized : forall pre1 pre2 mid post1 post2,
    List.map (fun o => o - length (kinds (run pre1)))
      (firstn (length mid) (skipn (length pre1) (offs (run (pre1 ++ mid ++ post1)))))
    = List.map (fun o => o - length (kinds (run pre2)))
      (firstn (length mid) (skipn (length pre2) (offs (run (pre2 ++ mid ++ post2))))).
  Proof.
    intros. rewrite !offs_window_mid_normalized. reflexivity.
  Qed.

  (* Combined window equivalence lemma (kinds, codes, offs normalized, issues). *)
  Lemma window_equivalence : forall pre mid post,
    firstn (length mid) (skipn (length pre) (kinds (run (pre ++ mid ++ post)))) = kinds (run mid) /\
    firstn (length mid) (skipn (length pre) (codes (run (pre ++ mid ++ post)))) = codes (run mid) /\
    List.map (fun o => o - length (kinds (run pre)))
      (firstn (length mid) (skipn (length pre) (offs (run (pre ++ mid ++ post))))) = List.seq 0 (length mid) /\
    firstn (length mid) (skipn (length pre) (issues_from (pre ++ mid ++ post))) = issues_from mid.
  Proof.
    intros pre mid post.
    repeat split.
    - apply kinds_window_mid.
    - apply codes_window_mid.
    - apply offs_window_mid_normalized.
    - apply issues_window_mid.
  Qed.

  (* Combined stability lemma for two contexts with identical mid window. *)
  Lemma window_equivalence_stability : forall pre1 pre2 mid post1 post2,
    (* kinds equal on mid slice *)
    firstn (length mid) (skipn (length pre1) (kinds (run (pre1 ++ mid ++ post1))))
    = firstn (length mid) (skipn (length pre2) (kinds (run (pre2 ++ mid ++ post2)))) /\
    (* codes equal on mid slice *)
    firstn (length mid) (skipn (length pre1) (codes (run (pre1 ++ mid ++ post1))))
    = firstn (length mid) (skipn (length pre2) (codes (run (pre2 ++ mid ++ post2)))) /\
    (* normalized offsets equal on mid slice *)
    List.map (fun o => o - length (kinds (run pre1)))
      (firstn (length mid) (skipn (length pre1) (offs (run (pre1 ++ mid ++ post1)))))
    = List.map (fun o => o - length (kinds (run pre2)))
      (firstn (length mid) (skipn (length pre2) (offs (run (pre2 ++ mid ++ post2))))) /\
    (* issues equal on mid slice *)
    firstn (length mid) (skipn (length pre1) (issues_from (pre1 ++ mid ++ post1)))
    = firstn (length mid) (skipn (length pre2) (issues_from (pre2 ++ mid ++ post2))).
  Proof.
    intros. repeat split.
    - apply kinds_window_stability.
    - apply codes_window_stability.
    - apply offs_window_stability_normalized.
    - now rewrite !issues_window_mid.
  Qed.

  (* General edit-locality corollary using offsets/lengths rather than explicit
     concatenations. If two inputs share the same window slice, then their mid
     kinds/codes are identical, offsets match up to a base shift, and issues
     are identical on that window. *)
  Definition window (s:list byte) (off len:nat) := firstn len (skipn off s).

  Lemma edit_locality_corollary : forall s1 s2 off1 off2 len,
    window s1 off1 len = window s2 off2 len ->
    let pre1 := firstn off1 s1 in
    let mid  := window s1 off1 len in
    let post1 := skipn (off1 + len) s1 in
    let pre2 := firstn off2 s2 in
    let post2 := skipn (off2 + len) s2 in
    (* kinds equal on mid window *)
    firstn len (skipn off1 (kinds (run s1))) = firstn len (skipn off2 (kinds (run s2))) /\
    (* codes equal on mid window *)
    firstn len (skipn off1 (codes (run s1))) = firstn len (skipn off2 (codes (run s2))) /\
    (* normalized offsets equal on mid window *)
    List.map (fun o => o - length (kinds (run pre1))) (firstn len (skipn off1 (offs (run s1))))
    = List.map (fun o => o - length (kinds (run pre2))) (firstn len (skipn off2 (offs (run s2)))) /\
    (* issues equal on mid window *)
    firstn len (skipn off1 (issues_from s1)) = firstn len (skipn off2 (issues_from s2)).
  Proof.
    intros s1 s2 off1 off2 len Heq.
    set (pre1 := firstn off1 s1).
    set (mid := window s1 off1 len).
    set (post1 := skipn (off1 + len) s1).
    set (pre2 := firstn off2 s2).
    set (post2 := skipn (off2 + len) s2).
    (* s1 = pre1 ++ mid ++ post1 and s2 = pre2 ++ mid ++ post2 *)
    assert (Hdecomp1: s1 = pre1 ++ mid ++ post1).
    { unfold pre1, mid, post1, window. rewrite firstn_skipn with (l:=s1) (n:=off1) at 1.
      rewrite firstn_skipn with (l:=skipn off1 s1) (n:=len) at 1. reflexivity. }
    assert (Hdecomp2: s2 = pre2 ++ mid ++ post2).
    { unfold pre2, mid, post2, window in *.
      specialize (Heq). rewrite Heq.
      rewrite firstn_skipn with (l:=s2) (n:=off2) at 1.
      rewrite firstn_skipn with (l:=skipn off2 s2) (n:=len) at 1. reflexivity. }
    subst s1 s2.
    (* Apply stability lemma *)
    destruct (window_equivalence_stability pre1 pre2 mid post1 post2) as (A&B&C&D).
    repeat split; assumption.
  Qed.

  (* Prefix invariance (kinds/codes/offs): prefix of full run depends only on prefix input. *)
  Lemma kinds_prefix_invariance : forall pre mid post,
    firstn (length pre) (kinds (run (pre ++ mid ++ post))) = kinds (run pre).
  Proof.
    intros pre mid post.
    rewrite kinds_run_app3.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    now rewrite firstn_O, app_nil_r.
  Qed.

  Lemma codes_prefix_invariance : forall pre mid post,
    firstn (length pre) (codes (run (pre ++ mid ++ post))) = codes (run pre).
  Proof.
    intros pre mid post.
    rewrite codes_run_app3.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    now rewrite firstn_O, app_nil_r.
  Qed.

  Lemma offs_prefix_invariance : forall pre mid post,
    firstn (length pre) (offs (run (pre ++ mid ++ post))) = offs (run pre).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (_&_&O1).
    rewrite O1.
    rewrite firstn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    now rewrite firstn_O, app_nil_r.
  Qed.

  (* Suffix invariance for kinds/codes and normalized offs. *)
  Lemma kinds_suffix_invariance : forall pre mid post,
    skipn (length pre + length mid) (kinds (run (pre ++ mid ++ post))) = kinds (run post).
  Proof.
    intros pre mid post.
    rewrite kinds_run_app3.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    now rewrite skipn_app, kinds_run_length, Nat.sub_diag.
  Qed.

  Lemma codes_suffix_invariance : forall pre mid post,
    skipn (length pre + length mid) (codes (run (pre ++ mid ++ post))) = codes (run post).
  Proof.
    intros pre mid post.
    rewrite codes_run_app3.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    now rewrite skipn_app, kinds_run_length, Nat.sub_diag.
  Qed.

  Lemma offs_suffix_invariance_normalized : forall pre mid post,
    let base := length (kinds (run pre)) + length (kinds (run mid)) in
    List.map (fun o => o - base)
      (skipn (length pre + length mid) (offs (run (pre ++ mid ++ post))))
    = List.seq 0 (length post).
  Proof.
    intros pre mid post base.
    (* offs(run (pre ++ (mid ++ post))) = offs(run pre) ++ seq(len pre) (len mid++post) *)
    destruct (run_app pre (mid ++ post)) as (_&_&O1).
    rewrite O1.
    (* Drop pre len and then mid len over the seq *)
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    rewrite skipn_app.
    rewrite kinds_run_length.
    rewrite Nat.sub_diag; simpl.
    (* Normalize subtracting base = len pre + len mid *)
    unfold base.
    rewrite kinds_run_length.
    rewrite kinds_run_length with (i:=mid).
    now rewrite map_minus_seq.
  Qed.

End L0SoA.
