From Coq Require Import List Arith Lia.
Require Import Catcode ListWindow.
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
    intros ks0 os0 cs0 i1 i2.
    revert ks0 os0 cs0 i2.
    induction i1 as [|b rest IH]; intros ks os cs i2; simpl.
    - reflexivity.
    - specialize (IH (ks ++ [classify_kind b])
                    (os ++ [length ks])
                    (cs ++ [classify_code b]) i2).
      exact IH.
  Qed.

  Lemma run_from_props_strong : forall ks os cs i ks' os' cs',
    run_from ks os cs i = (ks', os', cs') ->
    length ks' = length ks + length i /\
    length cs' = length cs + length i /\
    length os' = length os + length i /\
    ks' = ks ++ List.map classify_kind i /\
    cs' = cs ++ List.map classify_code i /\
    os' = os ++ List.seq (length ks) (length i).
  Proof.
    intros ks os cs i.
    revert ks os cs.
    induction i as [|b rest IH]; intros ks os cs ks' os' cs' H; simpl in H.
    - inversion H; subst; clear H.
      repeat split; simpl; try lia; now rewrite ?app_nil_r.
    - destruct (run_from (ks ++ [classify_kind b])
                         (os ++ [length ks])
                         (cs ++ [classify_code b]) rest) as [[ks1 os1] cs1] eqn:E.
      simpl in H. inversion H; subst; clear H.
      specialize (IH _ _ _ _ _ _ E).
      destruct IH as (Lk & Lc & Lo & HK & HC & HO).
      repeat split.
      + rewrite HK.
        rewrite app_length with (l:=ks ++ [classify_kind b])
                               (l':=List.map classify_kind rest).
        rewrite app_length with (l:=ks) (l':=[classify_kind b]).
        simpl.
        rewrite map_length.
        lia.
      + rewrite HC.
        rewrite app_length with (l:=cs ++ [classify_code b])
                               (l':=List.map classify_code rest).
        rewrite app_length with (l:=cs) (l':=[classify_code b]).
        simpl.
        rewrite map_length.
        lia.
      + rewrite HO.
        rewrite app_length with (l:=os ++ [length ks])
                               (l':=List.seq (length (ks ++ [classify_kind b])) (length rest)).
        rewrite app_length with (l:=os) (l':=[length ks]).
        simpl.
        rewrite seq_length.
        lia.
      + rewrite HK.
        rewrite <- app_assoc.
        simpl. reflexivity.
      + rewrite HC.
        rewrite <- app_assoc.
        simpl. reflexivity.
      + rewrite HO.
        rewrite <- app_assoc.
        simpl. f_equal.
        replace (length (ks ++ [classify_kind b])) with (length ks + 1)
          by (rewrite app_length; simpl; lia).
        replace (length ks + 1) with (S (length ks)) by lia.
        reflexivity.
  Qed.

  Lemma run_from_props : forall ks os cs i ks_out os_out cs_out,
    length ks = length cs ->
    length os = length ks ->
    run_from ks os cs i = (ks_out, os_out, cs_out) ->
    length ks_out = length cs_out /\ length os_out = length ks_out /\
    ks_out = ks ++ List.map classify_kind i /\
    cs_out = cs ++ List.map classify_code i /\
    os_out = os ++ List.seq (length ks) (length i).
  Proof.
    intros ks os cs i ks_out os_out cs_out Hkc Hos H.
    destruct (run_from_props_strong _ _ _ _ _ _ _ H)
      as (Lk & Lc & Lo & HK & HC & HO).
    split.
    - rewrite Lk, Lc, Hkc. lia.
    - split.
      { rewrite Lo, Lk, Hos, Hkc. lia. }
      repeat split; assumption.
  Qed.

  Lemma run_lengths : forall i,
    let s := run i in length (kinds s) = length (offs s) /\ length (kinds s) = length (codes s) /\ length (kinds s) = length i.
  Proof.
    intros i; unfold run.
    destruct (run_from [] [] [] i) as [[ks os] cs] eqn:E.
    specialize (run_from_props [] [] [] i ks os cs eq_refl eq_refl E)
      as (Hkc & Hos & Hks & Hcs & Hos').
    repeat split.
    - symmetry. exact Hos.
    - exact Hkc.
    - rewrite Hks.
      simpl.
      rewrite map_length.
      reflexivity.
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
    destruct (run_from_props_strong [] [] [] a ksa osa csa EA)
      as (_&_&_&Hksa&Hcsa&Hosa).
    destruct (run_from_props_strong [] [] [] b ksb0 osb0 csb0 EB0)
      as (_&_&_&Hksb0&Hcsb0&Hosb0).
    destruct (run_from_props_strong ksa osa csa b ksb osb csb EB)
      as (_&_&_&Hksb&Hcsb&Hosb).
    simpl.
    split.
    - rewrite Hksb.
      rewrite Hksb0.
      simpl.
      reflexivity.
    - split.
      + rewrite Hcsb.
        rewrite Hcsb0.
        simpl.
        reflexivity.
      + rewrite Hosb.
        reflexivity.
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
    rewrite <- (kinds_run_length pre).
    rewrite <- (kinds_run_length mid).
    apply (@firstn_skipn_middle_list kind
             (kinds (run pre)) (kinds (run mid)) (kinds (run post))).
  Qed.

  Lemma codes_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (codes (run (pre ++ mid ++ post))))
    = codes (run mid).
  Proof.
    intros pre mid post.
    rewrite codes_run_app3.
    pose proof (run_lengths pre) as (_&Hkc_pre&_).
    pose proof (run_lengths mid) as (_&Hkc_mid&_).
    pose proof (kinds_run_length pre) as Hlen_pre.
    pose proof (kinds_run_length mid) as Hlen_mid.
    assert (LCpre : length (codes (run pre)) = length pre)
      by (rewrite <- Hkc_pre; exact Hlen_pre).
    assert (LCmid : length (codes (run mid)) = length mid)
      by (rewrite <- Hkc_mid; exact Hlen_mid).
    rewrite <- LCpre.
    rewrite <- LCmid at 1.
    apply (@firstn_skipn_middle_list code
             (codes (run pre)) (codes (run mid)) (codes (run post))).
  Qed.

  Lemma firstn_seq_prefix : forall start len1 len2,
    firstn len1 (List.seq start (len1 + len2)) = List.seq start len1.
  Proof.
    intros start len1 len2.
    revert start len2.
    induction len1 as [|n IH]; intros start len2; simpl.
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  Lemma offs_window_mid : forall pre mid post,
    firstn (length mid)
      (skipn (length pre) (offs (run (pre ++ mid ++ post))))
    = List.seq (length (kinds (run pre))) (length mid).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (_&_&O1).
    rewrite O1.
    pose proof (run_lengths pre) as (Hk_offs & _ & _).
    pose proof (kinds_run_length pre) as Hlen_pre.
    assert (Hlen_offs_pre : length (offs (run pre)) = length pre)
      by (rewrite <- Hk_offs; exact Hlen_pre).
    rewrite <- Hlen_offs_pre.
    rewrite ListWindow.skipn_length_append.
    replace (length (mid ++ post)) with (length mid + length post)
      by (rewrite app_length; reflexivity).
    apply firstn_seq_prefix.
  Qed.

  (* Helpers about seq and normalization of offsets *)
  Lemma map_minus_seq_offset : forall base offset n,
    List.map (fun x => x - base) (List.seq (base + offset) n) = List.seq offset n.
  Proof.
    intros base offset n.
    revert offset.
    induction n as [|n IH]; intros offset; simpl.
    - reflexivity.
    - rewrite <- Nat.add_succ_r.
      simpl.
      f_equal; [lia|].
      apply IH.
  Qed.

  Lemma map_minus_seq : forall base n,
    List.map (fun x => x - base) (List.seq base n) = List.seq 0 n.
  Proof.
    intros base n.
    pose proof (map_minus_seq_offset base 0 n) as H.
    rewrite Nat.add_0_r in H.
    exact H.
  Qed.

  Lemma skipn_seq : forall start len off,
    skipn off (List.seq start len) = List.seq (start + off) (len - off).
  Proof.
    intros start len off.
    revert start len.
    induction off as [|off IH]; intros start len; simpl.
    - now rewrite Nat.add_0_r, Nat.sub_0_r.
    - destruct len as [|len]; simpl.
      + reflexivity.
      + rewrite IH with (start:=S start) (len:=len).
        rewrite Nat.add_succ_l.
        rewrite <- Nat.add_succ_comm.
        replace (len - off) with (S len - S off) by lia.
        reflexivity.
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
    firstn (length mid)
      (skipn (length pre1) (kinds (run (pre1 ++ mid ++ post1))))
    = firstn (length mid)
      (skipn (length pre2) (kinds (run (pre2 ++ mid ++ post2)))) /\
    (* codes equal on mid window *)
    firstn (length mid)
      (skipn (length pre1) (codes (run (pre1 ++ mid ++ post1))))
    = firstn (length mid)
      (skipn (length pre2) (codes (run (pre2 ++ mid ++ post2)))) /\
    (* normalized offsets equal on mid window *)
    List.map (fun o => o - length (kinds (run pre1)))
      (firstn (length mid)
        (skipn (length pre1) (offs (run (pre1 ++ mid ++ post1)))))
    = List.map (fun o => o - length (kinds (run pre2)))
      (firstn (length mid)
        (skipn (length pre2) (offs (run (pre2 ++ mid ++ post2))))) /\
    (* issues equal on mid window *)
    firstn (length mid)
      (skipn (length pre1) (issues_from (pre1 ++ mid ++ post1)))
    = firstn (length mid)
      (skipn (length pre2) (issues_from (pre2 ++ mid ++ post2))).
  Proof.
    intros s1 s2 off1 off2 len Heq.
    set (pre1 := firstn off1 s1).
    set (mid := window s1 off1 len).
    set (post1 := skipn (off1 + len) s1).
    set (pre2 := firstn off2 s2).
    set (post2 := skipn (off2 + len) s2).
    (* s1 = pre1 ++ mid ++ post1 and s2 = pre2 ++ mid ++ post2 *)
    assert (Hdecomp1: s1 = pre1 ++ mid ++ post1).
    { unfold pre1, mid, post1, window.
      apply ListWindow.decompose_firstn_skipn. }
    assert (Hdecomp2: s2 = pre2 ++ mid ++ post2).
    { unfold pre2, mid, post2, window in *.
      specialize (Heq). rewrite Heq.
      apply ListWindow.decompose_firstn_skipn. }
    clearbody pre1 mid post1 pre2 post2.
    subst s1 s2.
    (* Apply stability lemma *)
    destruct (window_equivalence_stability pre1 pre2 mid post1 post2)
      as (Hk & (Hc & (Ho & Hi))).
    repeat split; assumption.
  Qed.

  (* Prefix invariance (kinds/codes/offs): prefix of full run depends only on prefix input. *)

  Lemma len_kinds_run (i : list byte) : length (kinds (run i)) = length i.
  Proof. destruct (run_lengths i) as (_ & _ & L); exact L. Qed.

  Lemma len_codes_run (i : list byte) : length (codes (run i)) = length i.
  Proof.
    destruct (run_lengths i) as (_ & Hkc & Hki).
    rewrite <- Hkc.
    exact Hki.
  Qed.

  Lemma len_offs_run (i : list byte) : length (offs (run i)) = length i.
  Proof.
    destruct (run_lengths i) as (Hko & _ & Hki).
    rewrite <- Hko.
    exact Hki.
  Qed.

  Lemma kinds_prefix_invariance : forall pre mid post,
    firstn (length pre) (kinds (run (pre ++ mid ++ post))) = kinds (run pre).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (K & _ & _).
    rewrite K.
    rewrite firstn_app.
    replace (length pre - length (kinds (run pre))) with 0 by
      (rewrite (len_kinds_run pre); lia).
    simpl.
    rewrite firstn_all2 by (rewrite <- (len_kinds_run pre); lia).
    now rewrite app_nil_r.
  Qed.

  Lemma codes_prefix_invariance : forall pre mid post,
    firstn (length pre) (codes (run (pre ++ mid ++ post))) = codes (run pre).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (_ & C & _).
    rewrite C.
    rewrite firstn_app.
    replace (length pre - length (codes (run pre))) with 0 by
      (rewrite (len_codes_run pre); lia).
    simpl.
    rewrite firstn_all2 by (rewrite <- (len_codes_run pre); lia).
    now rewrite app_nil_r.
  Qed.

  Lemma offs_prefix_invariance : forall pre mid post,
    firstn (length pre) (offs (run (pre ++ mid ++ post))) = offs (run pre).
  Proof.
    intros pre mid post.
    destruct (run_app pre (mid ++ post)) as (_ & _ & O).
    rewrite O.
    rewrite firstn_app.
    replace (length pre - length (offs (run pre))) with 0 by
      (rewrite (len_offs_run pre); lia).
    simpl.
    rewrite firstn_all2 by (rewrite <- (len_offs_run pre); lia).
    now rewrite app_nil_r.
  Qed.

  (* Suffix invariance for kinds/codes and normalized offs. *)
  Lemma kinds_suffix_invariance : forall pre mid post,
    skipn (length pre + length mid) (kinds (run (pre ++ mid ++ post))) = kinds (run post).
  Proof.
    intros pre mid post.
    rewrite kinds_run_app3.
    rewrite skipn_app.
    rewrite (len_kinds_run pre).
    rewrite skipn_all2.
    2: { rewrite (len_kinds_run pre). apply Nat.le_add_r. }
    simpl.
    replace (length pre + length mid - length pre) with (length mid) by lia.
    rewrite skipn_app.
    rewrite (len_kinds_run mid).
    replace (length mid) with (length (kinds (run mid))) by (apply len_kinds_run).
    rewrite skipn_all.
    simpl.
    replace (length (kinds (run mid)) - length (kinds (run mid))) with 0 by lia.
    simpl. reflexivity.
  Qed.

  Lemma codes_suffix_invariance : forall pre mid post,
    skipn (length pre + length mid) (codes (run (pre ++ mid ++ post))) = codes (run post).
  Proof.
    intros pre mid post.
    rewrite codes_run_app3.
    rewrite skipn_app.
    rewrite (len_codes_run pre).
    rewrite skipn_all2.
    2: { rewrite (len_codes_run pre). apply Nat.le_add_r. }
    simpl.
    replace (length pre + length mid - length pre) with (length mid) by lia.
    rewrite skipn_app.
    rewrite (len_codes_run mid).
    replace (length mid) with (length (codes (run mid))) by (apply len_codes_run).
    rewrite skipn_all.
    simpl.
    replace (length (codes (run mid)) - length (codes (run mid))) with 0 by lia.
    simpl. reflexivity.
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
    rewrite (len_offs_run pre).
    rewrite skipn_all2.
    2: { rewrite (len_offs_run pre). apply Nat.le_add_r. }
    simpl.
    replace (length pre + length mid - length pre) with (length mid) by lia.
    replace (length (mid ++ post)) with (length mid + length post)
      by (rewrite app_length; reflexivity).
    rewrite skipn_seq.
    replace ((length mid + length post) - length mid) with (length post) by lia.
    (* Normalize subtracting base = len pre + len mid *)
    unfold base.
    rewrite (len_kinds_run pre).
    rewrite (len_kinds_run mid).
    now rewrite map_minus_seq.
  Qed.

End L0SoA.
