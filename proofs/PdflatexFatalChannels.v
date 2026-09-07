(* ==================================================================== *)
(*  PdflatexFatalChannels.v — D1, the [model_fatal] characterisation    *)
(*                                                                      *)
(*  The repo (PdflatexModel.v) proves only the SUFFICIENCY half:         *)
(*    project_no_fatal_tokens : premises -> the token stream is          *)
(*    fatal-free.  This file supplies the missing ONLY-IF half and       *)
(*    closes it into a biconditional:                                    *)
(*                                                                      *)
(*    model_fatal p pf  <->  ch_edge p \/ ch_decl p pf \/ ch_body p pf   *)
(*                                                                      *)
(*  i.e. the MODEL has EXACTLY THREE fatal channels.                     *)
(*                                                                      *)
(*  READ THAT PRECISELY. It says nothing else in the MODEL'S IMAGE of a  *)
(*  project can make it refuse; it does NOT say "nothing else a document *)
(*  contains", because what a document contains reaches the model only   *)
(*  through the OCaml encoder, which is outside Coq. A real feature the  *)
(*  encoder never turns into a token or an edge is invisible here, and   *)
(*  this theorem is silent about it.                                     *)
(*                                                                      *)
(*  Compile:                                                            *)
(*    coqc -R <repo>/_build/default/proofs LaTeXPerfectionist \         *)
(*         PdflatexFatalChannels.v                                       *)
(*                                                                      *)
(*  Self-contained: requires ONLY the repo's built .vo files.           *)
(*                                                                      *)
(*  SCOPE / WHAT THIS FILE DOES NOT CLAIM.                              *)
(*  Every statement here is about the Coq MODEL of a pdflatex build.     *)
(*  The encoding step (a real .tex tree -> [pdflatex_project]) is OCaml, *)
(*  outside Coq, so NOTHING here licenses an inference about how any     *)
(*  particular real paper is classified.  Claims of that shape were      *)
(*  drafted and then REMOVED from this development because the bridging  *)
(*  step is not machine-checked.                                        *)
(* ==================================================================== *)

From Coq Require Import List Bool Arith Lia.
From LaTeXPerfectionist Require Import
  ProjectClosure BuildProfileSound LexerFaithfulStep PdflatexModel.
Import ListNotations.

(* ==================================================================== *)
(*  §0.  INFRASTRUCTURE                                                 *)
(* ==================================================================== *)

Lemma tok_eq_dec : forall a b : L0Aux.pdflatex_token, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Qed.

Lemma no_fatal_iff_not_in :
  forall toks, L0Log.no_fatal_tokens toks <-> ~ In L0Aux.Tok_fatal toks.
Proof.
  intros toks. unfold L0Log.no_fatal_tokens, L0Log.tok_not_fatal.
  rewrite Forall_forall. split.
  - intros H Hin. exact (H _ Hin eq_refl).
  - intros H t Hin Heq. subst t. exact (H Hin).
Qed.

Lemma fatal_in_dec :
  forall toks, {In L0Aux.Tok_fatal toks} + {~ In L0Aux.Tok_fatal toks}.
Proof. intros. apply in_dec. apply tok_eq_dec. Qed.

(* -- §0.1  the three syntactic fatal channels ------------------------ *)

(* CHANNEL 1 (T2, dangling build edge). *)
Definition ch_edge (p : pdflatex_project) : Prop :=
  exists u v, In (u, v) (bg_edges (proj_graph p))
              /\ (~ node_known (proj_graph p) u \/ ~ node_known (proj_graph p) v).

(* CHANNEL 2 (T3a, a PROFILE-declared feature the engine lacks). *)
(* [p] is deliberately unused: a PROFILE-declared feature is a property of the
   profile alone. The parameter is kept so all three channels share the shape
   [project -> profile -> Prop] and the §1b disjunction reads uniformly.
   Recorded because "a channel of the project that is not a function of the
   project" is a fair thing for a reader to trip over. *)
Definition ch_decl (_p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  exists f, In f pf.(prof_features) /\ compatible f pf.(prof_engine) = false.

(* CHANNEL 3 (T3b, a DOCUMENT-required feature the engine lacks). *)
Definition ch_body (p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  exists f, In (BT_needs_feature f) p.(proj_body)
            /\ compatible f pf.(prof_engine) = false.

(* -- §0.2  component biconditionals ---------------------------------- *)

Lemma edge_tokens_iff :
  forall g, ~ In L0Aux.Tok_fatal (graph_edge_tokens g) <-> edges_closed g.
Proof.
  intros g. unfold graph_edge_tokens, edges_closed. split.
  - intros H u v Hin.
    destruct (node_known_b g u) eqn:Eu; destruct (node_known_b g v) eqn:Ev.
    + split; apply node_known_b_iff; assumption.
    + exfalso. apply H. apply in_map_iff. exists (u,v). split; [| exact Hin].
      unfold edge_token; simpl. rewrite Eu, Ev. reflexivity.
    + exfalso. apply H. apply in_map_iff. exists (u,v). split; [| exact Hin].
      unfold edge_token; simpl. rewrite Eu, Ev. reflexivity.
    + exfalso. apply H. apply in_map_iff. exists (u,v). split; [| exact Hin].
      unfold edge_token; simpl. rewrite Eu, Ev. reflexivity.
  - intros Hcl Hin. apply in_map_iff in Hin. destruct Hin as [[u v] [Ht He]].
    destruct (Hcl u v He) as [Hu Hv].
    apply node_known_b_iff in Hu. apply node_known_b_iff in Hv.
    unfold edge_token in Ht; simpl in Ht. rewrite Hu, Hv in Ht. discriminate.
Qed.

Lemma profile_tokens_iff :
  forall pf, ~ In L0Aux.Tok_fatal (profile_tokens pf)
             <-> profile_admits pf.(prof_features) pf.(prof_engine).
Proof.
  intros pf. unfold profile_tokens, profile_admits. split.
  - intros H f Hf. destruct (compatible f pf.(prof_engine)) eqn:Ec; [reflexivity|].
    exfalso. apply H. apply in_map_iff. exists f. split; [| exact Hf].
    unfold feature_token. rewrite Ec. reflexivity.
  - intros Hadm Hin. apply in_map_iff in Hin. destruct Hin as [f [Ht Hf]].
    unfold feature_token in Ht. rewrite (Hadm f Hf) in Ht. discriminate.
Qed.

Lemma brf_in :
  forall bs f, In f (body_required_features bs) <-> In (BT_needs_feature f) bs.
Proof.
  induction bs as [|b rest IH]; intros f; simpl.
  - split; contradiction.
  - destruct b as [| n | n | g]; simpl.
    + rewrite IH. split.
      * intro H; right; exact H.
      * intros [H|H]; [discriminate H | exact H].
    + rewrite IH. split.
      * intro H; right; exact H.
      * intros [H|H]; [discriminate H | exact H].
    + rewrite IH. split.
      * intro H; right; exact H.
      * intros [H|H]; [discriminate H | exact H].
    + split.
      * intros [->|H]; [left; reflexivity | right; apply IH; exact H].
      * intros [H|H]; [injection H as H; left; exact H
                      | right; apply IH; exact H].
Qed.

Lemma body_tokens_iff :
  forall e bs, ~ In L0Aux.Tok_fatal (map (body_to_tok e) bs)
               <-> profile_admits (body_required_features bs) e.
Proof.
  intros e bs. unfold profile_admits. split.
  - intros H f Hf. apply brf_in in Hf.
    destruct (compatible f e) eqn:Ec; [reflexivity|].
    exfalso. apply H. apply in_map_iff. exists (BT_needs_feature f).
    split; [| exact Hf]. simpl. rewrite Ec. reflexivity.
  - intros Hadm Hin. apply in_map_iff in Hin. destruct Hin as [b [Ht Hb]].
    destruct b as [| n | n | g]; simpl in Ht; try discriminate.
    destruct (compatible g e) eqn:Ec; [discriminate|].
    assert (Hg : In g (body_required_features bs)) by (apply brf_in; exact Hb).
    rewrite (Hadm g Hg) in Ec. discriminate.
Qed.

(* -- §0.3  token-level characterisation ------------------------------ *)

Theorem project_no_fatal_tokens_iff :
  forall p pf,
    L0Log.no_fatal_tokens (project_tokens p pf)
    <-> ( edges_closed (proj_graph p)
          /\ profile_admits pf.(prof_features) pf.(prof_engine)
          /\ profile_admits (body_required_features p.(proj_body))
                            pf.(prof_engine) ).
Proof.
  intros p pf. rewrite no_fatal_iff_not_in. unfold project_tokens.
  rewrite !in_app_iff.
  split.
  - intros H. split; [| split].
    + apply edge_tokens_iff. intro Hc. apply H. right; left; exact Hc.
    + apply profile_tokens_iff. intro Hc. apply H. right; right; exact Hc.
    + apply (body_tokens_iff pf.(prof_engine)). intro Hc. apply H. left; exact Hc.
  - intros [He [Hd Hb]] [Hc | [Hc | Hc]].
    + revert Hc. apply (body_tokens_iff pf.(prof_engine)). exact Hb.
    + revert Hc. apply edge_tokens_iff. exact He.
    + revert Hc. apply profile_tokens_iff. exact Hd.
Qed.

Theorem fatal_channel_iff :
  forall p pf,
    In L0Aux.Tok_fatal (project_tokens p pf)
    <-> (ch_edge p \/ ch_decl p pf \/ ch_body p pf).
Proof.
  intros p pf. split.
  - intro Hin.
    destruct (fatal_in_dec (graph_edge_tokens (proj_graph p))) as [He|He].
    { left. apply in_map_iff in He. destruct He as [[u v] [Ht Hev]].
      exists u, v. split; [exact Hev|].
      unfold edge_token in Ht; simpl in Ht.
      destruct (node_known_b (proj_graph p) u) eqn:Eu;
      destruct (node_known_b (proj_graph p) v) eqn:Ev; simpl in Ht;
        try discriminate.
      - right. intro Hk. apply node_known_b_iff in Hk.
        rewrite Hk in Ev; discriminate.
      - left. intro Hk. apply node_known_b_iff in Hk.
        rewrite Hk in Eu; discriminate.
      - left. intro Hk. apply node_known_b_iff in Hk.
        rewrite Hk in Eu; discriminate. }
    destruct (fatal_in_dec (profile_tokens pf)) as [Hd|Hd].
    { right; left. apply in_map_iff in Hd. destruct Hd as [f [Ht Hf]].
      exists f. split; [exact Hf|].
      unfold feature_token in Ht.
      destruct (compatible f pf.(prof_engine)) eqn:Ec;
        [discriminate | reflexivity]. }
    right; right.
    unfold project_tokens in Hin. rewrite !in_app_iff in Hin.
    destruct Hin as [Hb | [Hc|Hc]]; [| contradiction | contradiction].
    apply in_map_iff in Hb. destruct Hb as [b [Ht Hb]].
    destruct b as [| n | n | g]; simpl in Ht; try discriminate.
    exists g. destruct (compatible g pf.(prof_engine)) eqn:Ec;
      [discriminate | split; [exact Hb | reflexivity]].
  - intros Hch. unfold project_tokens. rewrite !in_app_iff.
    destruct Hch as [[u [v [He Hk]]] | [[f [Hf Ec]] | [f [Hb Ec]]]].
    + right; left. apply in_map_iff. exists (u,v). split; [| exact He].
      unfold edge_token; simpl.
      destruct (node_known_b (proj_graph p) u) eqn:Eu;
      destruct (node_known_b (proj_graph p) v) eqn:Ev; simpl;
        try reflexivity.
      exfalso. destruct Hk as [Hk|Hk]; apply Hk; apply node_known_b_iff;
        [exact Eu | exact Ev].
    + right; right. apply in_map_iff. exists f. split; [| exact Hf].
      unfold feature_token. rewrite Ec. reflexivity.
    + left. apply in_map_iff. exists (BT_needs_feature f). split; [| exact Hb].
      simpl. rewrite Ec. reflexivity.
Qed.

(* -- §0.4  lifting a fatal TOKEN to a fatal LOG ----------------------
   The repo proves only the singleton case (fatal_token_is_fatal,
   LexerFaithfulStep.v:623).  The general converse is built here. *)

Import L0Aux. Import L0Log. Import L0Pass.

Lemma prefix_match_extend :
  forall pre seq suf,
    prefix_match pre seq = true -> prefix_match pre (seq ++ suf) = true.
Proof.
  induction pre as [|x xs IH]; intros seq suf H; simpl in *; [reflexivity|].
  destruct seq as [|y ys]; [discriminate|]. simpl.
  apply andb_true_iff in H. destruct H as [Hxy Hrest].
  apply andb_true_iff. split; [exact Hxy | apply IH; exact Hrest].
Qed.

Lemma prefix_match_self :
  forall pre rest, prefix_match pre (pre ++ rest) = true.
Proof.
  induction pre as [|x xs IH]; intros rest; simpl; [reflexivity|].
  apply andb_true_iff. split; [apply Nat.eqb_refl | apply IH].
Qed.

Lemma contains_subseq_here :
  forall sub B, contains_subseq sub (sub ++ B) = true.
Proof.
  intros sub B. destruct sub as [|x xs]; simpl.
  - destruct B; reflexivity.
  - apply orb_true_iff. left. simpl.
    apply andb_true_iff. split; [apply Nat.eqb_refl | apply prefix_match_self].
Qed.

Lemma contains_subseq_skip_left :
  forall A sub seq,
    contains_subseq sub seq = true -> contains_subseq sub (A ++ seq) = true.
Proof.
  induction A as [|a A IH]; intros sub seq H; simpl; [exact H|].
  apply orb_true_iff. right. apply IH. exact H.
Qed.

Lemma contains_subseq_extend_right :
  forall seq sub suf,
    contains_subseq sub seq = true -> contains_subseq sub (seq ++ suf) = true.
Proof.
  induction seq as [|a seq IH]; intros sub suf H; simpl in *.
  - destruct sub as [|x xs]; [| discriminate].
    destruct suf; reflexivity.
  - apply orb_true_iff in H. apply orb_true_iff.
    destruct H as [H|H].
    + left. apply (prefix_match_extend sub (a :: seq) suf H).
    + right. apply IH. exact H.
Qed.

Lemma log_step_pass_grows :
  forall toks s aux,
    exists suf, log_bytes (log_step_pass s toks aux) = log_bytes s ++ suf.
Proof.
  induction toks as [|t rest IH]; intros s aux; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (log_step_token s t aux) aux) as [suf Hsuf].
    rewrite Hsuf. destruct t as [| n | n |]; simpl.
    + exists suf. reflexivity.
    + exists suf. reflexivity.
    + destruct (in_dec Nat.eq_dec n (defined_labels aux)); simpl.
      * exists suf. reflexivity.
      * exists (warn_bytes ++ suf). rewrite app_assoc. reflexivity.
    + exists (fatal_marker_emergency_stop ++ suf).
      rewrite app_assoc. reflexivity.
Qed.

Lemma fatal_token_in_log_bytes :
  forall toks s aux,
    In Tok_fatal toks ->
    contains_subseq fatal_marker_emergency_stop
                    (log_bytes (log_step_pass s toks aux)) = true.
Proof.
  induction toks as [|t rest IH]; intros s aux Hin; simpl in *; [contradiction|].
  destruct Hin as [Heq | Hin].
  - subst t. simpl.
    destruct (log_step_pass_grows rest
                (mk_log (warnings s)
                        (log_bytes s ++ fatal_marker_emergency_stop)) aux)
      as [suf Hsuf].
    rewrite Hsuf. simpl. rewrite <- app_assoc.
    apply contains_subseq_skip_left. apply contains_subseq_here.
  - apply IH. exact Hin.
Qed.

Lemma pass_step_grows :
  forall s input,
    exists suf,
      log_bytes (log (pdflatex_pass_step s input)) = log_bytes (log s) ++ suf.
Proof. intros s input. unfold pdflatex_pass_step; simpl.
       apply log_step_pass_grows. Qed.

Lemma iterate_grows :
  forall k s input,
    exists suf,
      log_bytes (log (iterate_pass_step s k input)) = log_bytes (log s) ++ suf.
Proof.
  induction k as [|k IH]; intros s input; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (pdflatex_pass_step s input) input) as [suf1 H1].
    destruct (pass_step_grows s input) as [suf0 H0].
    exists (suf0 ++ suf1). rewrite H1, H0, app_assoc. reflexivity.
Qed.

Theorem fatal_token_reaches_fatal_log :
  forall k input,
    1 <= k ->
    In Tok_fatal input ->
    ~ log_no_fatal (log (iterate_pass_step initial_pass_state k input)).
Proof.
  intros k input Hk Hin Hno.
  assert (Hm : In fatal_marker_emergency_stop fatal_markers)
    by (simpl; right; left; reflexivity).
  specialize (Hno fatal_marker_emergency_stop Hm).
  destruct k as [|k']; [lia|]. simpl in Hno.
  destruct (iterate_grows k' (pdflatex_pass_step initial_pass_state input) input)
    as [suf Hsuf].
  rewrite Hsuf in Hno.
  assert (Hstep : contains_subseq fatal_marker_emergency_stop
                    (log_bytes (log (pdflatex_pass_step initial_pass_state input)))
                  = true).
  { unfold pdflatex_pass_step; simpl.
    apply fatal_token_in_log_bytes. exact Hin. }
  rewrite (contains_subseq_extend_right _ _ suf Hstep) in Hno. discriminate.
Qed.

(* ==================================================================== *)
(*  §1.  THE CHARACTERISATION                                           *)
(* ==================================================================== *)

Definition model_fatal (p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  ~ pdflatex_compilation_succeeds p pf.

(* -- 1a. POSITIVE FORM ------------------------------------------------
   NOTE the right-hand side is [edges_closed], NOT [project_closed].
   [project_closed = edges_closed /\ acyclic_graph], and the acyclicity
   conjunct is provably NOT a fatal channel (see §2).  Stating this
   theorem with [project_closed] would make it FALSE. *)
Theorem model_compiles_iff :
  forall p pf,
    pdflatex_compilation_succeeds p pf
    <-> ( edges_closed (proj_graph p)
          /\ profile_admits pf.(prof_features) pf.(prof_engine)
          /\ profile_admits (body_required_features p.(proj_body))
                            pf.(prof_engine) ).
Proof.
  intros p pf. split.
  - intros [k [Hk [Hconv Hsafe]]].
    apply project_no_fatal_tokens_iff.
    apply no_fatal_iff_not_in. intro Hin.
    destruct k as [|k'].
    { unfold faithful_run in Hconv. simpl in Hconv. discriminate. }
    apply (fatal_token_reaches_fatal_log (S k') (project_tokens p pf));
      [ lia | exact Hin | exact Hsafe ].
  - intros Hconj.
    assert (Hnf : L0Log.no_fatal_tokens (project_tokens p pf))
      by (apply project_no_fatal_tokens_iff; exact Hconj).
    exists 2. split; [unfold pdflatex_pass_max; lia |].
    split.
    + unfold faithful_run. apply L0Pass.converged_at_two.
    + unfold faithful_run. apply L0Pass.pass_iteration_no_fatal. exact Hnf.
Qed.

(* -- 1b. THE HEADLINE: the explicit three-channel disjunction --------- *)
Theorem model_fatal_iff :
  forall p pf,
    model_fatal p pf <-> (ch_edge p \/ ch_decl p pf \/ ch_body p pf).
Proof.
  intros p pf. unfold model_fatal. split.
  - intros Hfat. apply fatal_channel_iff.
    destruct (fatal_in_dec (project_tokens p pf)) as [Hin|Hout]; [exact Hin|].
    exfalso. apply Hfat. apply model_compiles_iff.
    apply project_no_fatal_tokens_iff. apply no_fatal_iff_not_in. exact Hout.
  - intros Hch Hsucc.
    apply model_compiles_iff in Hsucc.
    apply project_no_fatal_tokens_iff in Hsucc.
    apply no_fatal_iff_not_in in Hsucc.
    apply Hsucc. apply fatal_channel_iff. exact Hch.
Qed.

(* The two directions, named separately.  ONLY-IF is the half the repo
   did not have: it says the three channels are EXHAUSTIVE. *)
Corollary model_fatal_only_if :
  forall p pf, model_fatal p pf -> (ch_edge p \/ ch_decl p pf \/ ch_body p pf).
Proof. intros p pf H. apply model_fatal_iff. exact H. Qed.

Corollary model_fatal_if :
  forall p pf, (ch_edge p \/ ch_decl p pf \/ ch_body p pf) -> model_fatal p pf.
Proof. intros p pf H. apply model_fatal_iff. exact H. Qed.

(* -- 1c. COMPUTATIONAL FORM ------------------------------------------
   [model_ok_b] is a decision procedure for the same condition: it is
   built from [forallb], [node_known_b] and the [compatible] table, and
   reduces to a closed boolean on any concrete input, which is what makes
   the witnesses in §3 [vm_compute; reflexivity].

   HONESTY NOTE.  Do NOT read [model_ok_b] as independent evidence that
   the characterisation is non-trivial.  It is not: [model_ok_b] is
   PROVABLY EQUAL to the token test [forallb (negb o tok_fatal_b)
   (project_tokens p pf)] — see [model_ok_b_is_the_token_test] in §1d,
   which is Qed'd below precisely so this caveat is machine-checked
   rather than asserted.  The real non-triviality evidence in this file
   is §2 (a genuine separation: T2 is strictly stronger than
   fatal-freeness) and §3 (all three channels, and the negative
   polarity, are separately inhabited). *)

Definition model_ok_b (p : pdflatex_project) (pf : pdflatex_profile) : bool :=
  forallb (fun e => andb (node_known_b (proj_graph p) (fst e))
                         (node_known_b (proj_graph p) (snd e)))
          (bg_edges (proj_graph p))
  && all_features_compatible pf.(prof_features) pf.(prof_engine)
  && all_features_compatible (body_required_features p.(proj_body))
                             pf.(prof_engine).

Definition model_fatal_b (p : pdflatex_project) (pf : pdflatex_profile) : bool :=
  negb (model_ok_b p pf).

Lemma edges_ok_b_iff :
  forall g,
    forallb (fun e => andb (node_known_b g (fst e)) (node_known_b g (snd e)))
            (bg_edges g) = true
    <-> edges_closed g.
Proof.
  intros g. unfold edges_closed. rewrite forallb_forall. split.
  - intros H u v Hin. specialize (H (u,v) Hin). simpl in H.
    apply andb_true_iff in H. destruct H as [Hu Hv].
    split; apply node_known_b_iff; assumption.
  - intros H [u v] Hin. simpl. destruct (H u v Hin) as [Hu Hv].
    apply andb_true_iff.
    split; apply node_known_b_iff; assumption.
Qed.

Theorem model_ok_b_iff :
  forall p pf, model_ok_b p pf = true <-> pdflatex_compilation_succeeds p pf.
Proof.
  intros p pf. unfold model_ok_b. rewrite model_compiles_iff.
  rewrite !andb_true_iff, edges_ok_b_iff.
  split.
  - intros [[He Hd] Hb]. split; [exact He | split].
    + apply T3_profile_compatible; exact Hd.
    + apply T3_profile_compatible; exact Hb.
  - intros [He [Hd Hb]]. split; [split; [exact He |] |].
    + apply profile_admits_implies_bulk; exact Hd.
    + apply profile_admits_implies_bulk; exact Hb.
Qed.

(* THE REFLECTION THEOREM.  Left: a negated existential over runs of the
   pass machine, whose fatality is a byte-substring test.  Right: a
   decidable boolean on the project's SYNTAX. *)
Theorem model_fatal_reflect :
  forall p pf, model_fatal p pf <-> model_fatal_b p pf = true.
Proof.
  intros p pf. unfold model_fatal, model_fatal_b.
  destruct (model_ok_b p pf) eqn:E; simpl; split.
  - intros H. exfalso. apply H. apply model_ok_b_iff. exact E.
  - discriminate.
  - reflexivity.
  - intros _ Hs. apply model_ok_b_iff in Hs. rewrite E in Hs. discriminate.
Qed.

Theorem model_compiles_reflect :
  forall p pf, pdflatex_compilation_succeeds p pf <-> model_fatal_b p pf = false.
Proof.
  intros p pf. unfold model_fatal_b.
  rewrite <- model_ok_b_iff, negb_false_iff. reflexivity.
Qed.

(* -- 1d.  THE HONESTY LEMMA -------------------------------------------
   [model_ok_b] is NOT a token-free reformulation.  It is EQUAL, as a
   function, to "no Tok_fatal in the project's token stream".  Proving
   this is what stops anyone quoting [model_ok_b] as if it were
   independent corroboration of §1. *)

Definition tok_fatal_b (t : pdflatex_token) : bool :=
  match t with Tok_fatal => true | _ => false end.

Lemma fb_app :
  forall (A : Type) (f : A -> bool) (l1 l2 : list A),
    forallb f (l1 ++ l2) = forallb f l1 && forallb f l2.
Proof.
  intros A f l1 l2. induction l1 as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. apply andb_assoc.
Qed.

Lemma fb_edge_tokens :
  forall g,
    forallb (fun t => negb (tok_fatal_b t)) (graph_edge_tokens g)
    = forallb (fun e => andb (node_known_b g (fst e)) (node_known_b g (snd e)))
              (bg_edges g).
Proof.
  intros g. unfold graph_edge_tokens.
  induction (bg_edges g) as [|e es IH]; simpl; [reflexivity|].
  rewrite IH. unfold edge_token.
  destruct (node_known_b g (fst e)); destruct (node_known_b g (snd e));
    reflexivity.
Qed.

Lemma fb_profile_tokens :
  forall pf,
    forallb (fun t => negb (tok_fatal_b t)) (profile_tokens pf)
    = all_features_compatible pf.(prof_features) pf.(prof_engine).
Proof.
  intros pf. unfold profile_tokens.
  induction (prof_features pf) as [|f fs IH]; simpl; [reflexivity|].
  rewrite IH. unfold feature_token.
  destruct (compatible f (prof_engine pf)); reflexivity.
Qed.

Lemma fb_body_tokens :
  forall e bs,
    forallb (fun t => negb (tok_fatal_b t)) (map (body_to_tok e) bs)
    = all_features_compatible (body_required_features bs) e.
Proof.
  intros e. induction bs as [|b bs IH]; simpl; [reflexivity|].
  destruct b as [| n | n | f]; simpl; rewrite IH; [reflexivity|reflexivity|reflexivity|].
  destruct (compatible f e); reflexivity.
Qed.

Theorem model_ok_b_is_the_token_test :
  forall p pf,
    model_ok_b p pf
    = forallb (fun t => negb (tok_fatal_b t)) (project_tokens p pf).
Proof.
  intros p pf. unfold model_ok_b, project_tokens.
  rewrite !fb_app, fb_body_tokens, fb_edge_tokens, fb_profile_tokens.
  apply andb_comm.
Qed.

(* ==================================================================== *)
(*  §2.  A GENUINE SEPARATION                                           *)
(*                                                                      *)
(*  If the characterisation were vacuous it could not REFUTE anything.  *)
(*  It refutes the natural reading of D1: T2 (= project_closed =        *)
(*  edges_closed /\ acyclic_graph) is STRICTLY STRONGER than            *)
(*  fatal-freeness.  Root cause: edge_tokens_no_fatal (PdflatexModel.v) *)
(*  opens `intros g [Hedges _]`, discarding the acyclicity half; so     *)
(*  acyclicity is dead weight in the whole capstone.                    *)
(*                                                                      *)
(*  THAT IS A MODEL DEFECT, NOT AN ACHIEVEMENT, and the theorem name    *)
(*  [acyclicity_is_not_a_fatal_channel] must NOT be read as "cycles do  *)
(*  not matter". The witness below is a node with an edge to ITSELF --  *)
(*  a .tex file that \inputs itself -- and REAL pdflatex does not build *)
(*  it; it recurses until "TeX capacity exceeded". So the separation is *)
(*  genuine (the model really does ignore acyclicity) AND it is a place *)
(*  where the model is WEAKER than the engine: it certifies a project   *)
(*  the engine would refuse. The honest reading is that T2 carries a    *)
(*  conjunct the fatality proof never consumes, and closing that gap    *)
(*  means giving cycles a fatal channel, not deleting T2.               *)
(*                                                                      *)
(*  [project_well_typed] is by definition [pdflatex_T2_closed]; both    *)
(*  phrasings are stated so neither can be read as a weaker claim.      *)
(* ==================================================================== *)

Theorem acyclicity_is_not_a_fatal_channel :
  exists p pf,
    pdflatex_compilation_succeeds p pf
    /\ ~ pdflatex_T2_closed p
    /\ ~ project_well_typed p.
Proof.
  exists (mk_project (mk_graph [mk_node 0 Tex]
                               [(mk_node 0 Tex, mk_node 0 Tex)]) []).
  exists pf_ok.
  assert (Hcyc : ~ pdflatex_T2_closed
                   (mk_project (mk_graph [mk_node 0 Tex]
                                         [(mk_node 0 Tex, mk_node 0 Tex)]) [])).
  { intros [_ [order Htopo]].
    assert (Hin : In (mk_node 0 Tex, mk_node 0 Tex)
                     (bg_edges (mk_graph [mk_node 0 Tex]
                                         [(mk_node 0 Tex, mk_node 0 Tex)])))
      by (simpl; left; reflexivity).
    specialize (Htopo (mk_node 0 Tex) (mk_node 0 Tex) Hin).
    destruct (index_of (mk_node 0 Tex) order) as [i|]; [lia | exact Htopo]. }
  split; [| split; [exact Hcyc | exact Hcyc]].
  apply model_compiles_iff. split; [| split].
  - intros u v Hin. simpl in Hin. destruct Hin as [Heq | []].
    injection Heq as H1 H2. subst.
    split; unfold node_known; simpl; left; reflexivity.
  - intros f Hf. simpl in Hf. contradiction.
  - intros f Hf. simpl in Hf. contradiction.
Qed.

(* ==================================================================== *)
(*  §3.  NON-VACUITY, BY CONSTRUCTION                                   *)
(*                                                                      *)
(*  All THREE channels are separately inhabited, and the negative side  *)
(*  is inhabited too.  A characterisation with an empty side is         *)
(*  worthless.  These are model-internal witnesses; none of them stands *)
(*  for any particular real document.                                   *)
(* ==================================================================== *)

Definition tex_node (i : nat) : ProjectClosure.node := mk_node i Tex.

(* --- 3.1 NEGATIVE polarity: a project that COMPILES in the model ---- *)
Definition p_compiles : pdflatex_project :=
  mk_project (mk_graph [tex_node 0; tex_node 1] [(tex_node 0, tex_node 1)])
             [BT_text; BT_label_def 1; BT_label_ref 1; BT_text].

Example p_compiles_b : model_fatal_b p_compiles pf_ok = false.
Proof. vm_compute. reflexivity. Qed.

Theorem p_compiles_succeeds : pdflatex_compilation_succeeds p_compiles pf_ok.
Proof. apply model_compiles_reflect. vm_compute. reflexivity. Qed.

Theorem p_compiles_not_fatal : ~ model_fatal p_compiles pf_ok.
Proof.
  intro H. apply model_fatal_reflect in H. vm_compute in H. discriminate.
Qed.

(* --- 3.2 POSITIVE polarity, CHANNEL 1: dangling build edge ---------- *)
(* tex_node 1 is referenced by an edge but is NOT in bg_nodes. *)
Definition p_fatal_edge : pdflatex_project :=
  mk_project (mk_graph [tex_node 0] [(tex_node 0, tex_node 1)]) [BT_text].

Example p_fatal_edge_b : model_fatal_b p_fatal_edge pf_ok = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p_fatal_edge_is_fatal : model_fatal p_fatal_edge pf_ok.
Proof. apply model_fatal_reflect. vm_compute. reflexivity. Qed.

Theorem p_fatal_edge_channel : ch_edge p_fatal_edge.
Proof.
  exists (tex_node 0), (tex_node 1). split.
  - simpl. left. reflexivity.
  - right. unfold node_known. simpl. intros [H | []]. discriminate.
Qed.

(* --- 3.3 POSITIVE polarity, CHANNEL 2: profile-declared feature ----- *)
Definition pf_lua_on_pdflatex : pdflatex_profile :=
  mk_pdflatex_profile Pdflatex [Lua_scripting].

Definition p_plain : pdflatex_project :=
  mk_project (mk_graph [tex_node 0] []) [BT_text].

Example p_fatal_decl_b : model_fatal_b p_plain pf_lua_on_pdflatex = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p_fatal_decl_is_fatal : model_fatal p_plain pf_lua_on_pdflatex.
Proof. apply model_fatal_reflect. vm_compute. reflexivity. Qed.

Theorem p_fatal_decl_channel : ch_decl p_plain pf_lua_on_pdflatex.
Proof. exists Lua_scripting. split; [simpl; left; reflexivity | reflexivity]. Qed.

(* --- 3.4 POSITIVE polarity, CHANNEL 3: document-required feature ---- *)
Definition p_fatal_body : pdflatex_project :=
  mk_project (mk_graph [tex_node 0] [])
             [BT_text; BT_needs_feature Opentype_fonts; BT_text].

Example p_fatal_body_b : model_fatal_b p_fatal_body pf_ok = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p_fatal_body_is_fatal : model_fatal p_fatal_body pf_ok.
Proof. apply model_fatal_reflect. vm_compute. reflexivity. Qed.

Theorem p_fatal_body_channel : ch_body p_fatal_body pf_ok.
Proof.
  exists Opentype_fonts. split; [simpl; right; left; reflexivity | reflexivity].
Qed.

(* The SAME body under an engine that HAS the feature compiles — so the
   profile really is load-bearing, the channel is not a constant. *)
Example p_fatal_body_ok_on_xelatex :
  model_fatal_b p_fatal_body (mk_pdflatex_profile Xelatex []) = false.
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================== *)
(*  §4.  THE MODEL'S FATAL VOCABULARY                                   *)
(*                                                                      *)
(*  Consequences of §1 about WHAT THE MODEL CAN SEE.  Both are          *)
(*  statements about the Coq model only.  In particular §4.2 is NOT a   *)
(*  statement about any corpus: it says nothing about how many real     *)
(*  papers encode to feature-free bodies, because the encoder is not    *)
(*  modelled here.                                                      *)
(* ==================================================================== *)

(* --- 4.1  the model's ENTIRE feature-fatal vocabulary under pdflatex -

   ⚠ Read the theorem as a statement about the [compatible] TABLE, not about
   the pdfTeX binary.  It is a complete description of what the MODEL treats
   as feature-fatal under pdflatex.

   HISTORY, kept because it is the reason this list is four entries and not
   five.  [UTF8_direct] used to appear here: the table marked it incompatible
   with [Pdflatex], and this note recorded that as a known MODEL-vs-REALITY
   divergence, latent because no detector emits [BT_needs_feature UTF8_direct].
   The divergence is now CLOSED rather than merely recorded — pdfTeX has
   defaulted to UTF-8 input since TeX Live 2018, MEASURED at the pin (rc 0, and
   pdftotext recovers the accented text), so the row was corrected in
   BuildProfileSound.v together with its two hand mirrors
   (compile_contract.feature_compatible and
   specs/v26/compilation_profiles.yaml).

   ⚠ THIS THEOREM IS WHAT CAUGHT THE CHANGE.  Correcting the table made the
   old five-element statement FALSE, and the [intuition congruence] proof
   failed on the next build, which is precisely the value of stating a
   vocabulary as a biconditional instead of a comment. *)
Theorem pdflatex_body_fatal_vocabulary :
  forall f, compatible f Pdflatex = false
            <-> In f [Unicode_math; Opentype_fonts;
                      Lua_scripting; Japanese_cjk].
Proof. intros f. destruct f; simpl; intuition congruence. Qed.

(* --- 4.2  feature-free bodies are never model-fatal ------------------
   No matter what the body CONTAINS — arbitrary length, arbitrary text,
   arbitrary labels — if it declares no engine feature and the build
   graph is edge-closed, the model says it COMPILES. *)
Theorem feature_free_body_never_fatal :
  forall g bs,
    edges_closed g ->
    (forall f, ~ In (BT_needs_feature f) bs) ->
    pdflatex_compilation_succeeds (mk_project g bs) pf_ok.
Proof.
  intros g bs Hcl Hnf. apply model_compiles_iff. simpl.
  split; [exact Hcl | split].
  - intros f Hf. simpl in Hf. contradiction.
  - intros f Hf. exfalso. apply (Hnf f). apply brf_in. exact Hf.
Qed.

(* ==================================================================== *)
(*  §5.  PRINT ASSUMPTIONS — every Lemma / Theorem / Corollary / Example *)
(* ==================================================================== *)

Print Assumptions tok_eq_dec.
Print Assumptions no_fatal_iff_not_in.
Print Assumptions fatal_in_dec.
Print Assumptions edge_tokens_iff.
Print Assumptions profile_tokens_iff.
Print Assumptions brf_in.
Print Assumptions body_tokens_iff.
Print Assumptions project_no_fatal_tokens_iff.
Print Assumptions fatal_channel_iff.
Print Assumptions prefix_match_extend.
Print Assumptions prefix_match_self.
Print Assumptions contains_subseq_here.
Print Assumptions contains_subseq_skip_left.
Print Assumptions contains_subseq_extend_right.
Print Assumptions log_step_pass_grows.
Print Assumptions fatal_token_in_log_bytes.
Print Assumptions pass_step_grows.
Print Assumptions iterate_grows.
Print Assumptions fatal_token_reaches_fatal_log.
Print Assumptions model_compiles_iff.
Print Assumptions model_fatal_iff.
Print Assumptions model_fatal_only_if.
Print Assumptions model_fatal_if.
Print Assumptions edges_ok_b_iff.
Print Assumptions model_ok_b_iff.
Print Assumptions model_fatal_reflect.
Print Assumptions model_compiles_reflect.
Print Assumptions fb_app.
Print Assumptions fb_edge_tokens.
Print Assumptions fb_profile_tokens.
Print Assumptions fb_body_tokens.
Print Assumptions model_ok_b_is_the_token_test.
Print Assumptions acyclicity_is_not_a_fatal_channel.
Print Assumptions p_compiles_b.
Print Assumptions p_compiles_succeeds.
Print Assumptions p_compiles_not_fatal.
Print Assumptions p_fatal_edge_b.
Print Assumptions p_fatal_edge_is_fatal.
Print Assumptions p_fatal_edge_channel.
Print Assumptions p_fatal_decl_b.
Print Assumptions p_fatal_decl_is_fatal.
Print Assumptions p_fatal_decl_channel.
Print Assumptions p_fatal_body_b.
Print Assumptions p_fatal_body_is_fatal.
Print Assumptions p_fatal_body_channel.
Print Assumptions p_fatal_body_ok_on_xelatex.
Print Assumptions pdflatex_body_fatal_vocabulary.
Print Assumptions feature_free_body_never_fatal.
