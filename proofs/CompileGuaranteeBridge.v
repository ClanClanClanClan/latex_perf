(** * CompileGuaranteeBridge — a DECIDABLE checker of the capstone premises.

    This file closes the "flagship" gap: it connects a *runtime, computable*
    decision to the PROVEN headline theorem [PdflatexModel.pdflatex_compile_safe].

    [pdflatex_compile_safe] is UNCONDITIONAL modulo two genuine, falsifiable
    hypotheses:

      - [project_well_typed p]   := [pdflatex_T2_closed p]  (= [project_closed]),
      - [profile_supported p pf] :=
            [profile_admits pf.(prof_features) pf.(prof_engine)]  /\
            [profile_admits (body_required_features p.(proj_body))
                            pf.(prof_engine)].

    We additionally certify the T4 coherence obligation
    [pdflatex_T4_coherent p] := [NoDup (body_label_defs p.(proj_body))], which
    the OCaml extractor also computes (duplicate-\label detection).

    The problem: [project_closed] contains an EXISTENTIAL — [acyclic_graph g :=
    exists order, valid_topo g order].  A pure [bool] cannot conjure the
    witnessing topological order.  So the decision procedure here is
    WITNESS-CARRYING: it consumes a candidate order (which the OCaml side
    produces by a real topological sort of the build graph) and CERTIFIES it.
    Everything else (edge closure, feature admissibility, label uniqueness) is
    genuinely first-order decidable and checked outright.

    [project_wf_dec] returns [true] ==> (via [project_wf_dec_sound], Qed, no
    admits) EXACTLY the hypotheses [pdflatex_compile_safe] needs; the corollary
    [project_wf_dec_compile_safe] discharges the capstone from a [true] verdict.

    [Print Assumptions project_wf_dec_compile_safe] must print [Closed under the
    global context]. *)

From Coq Require Import List Bool Arith Lia.
From LaTeXPerfectionist Require Import
  ProjectClosure
  BuildProfileSound
  LexerFaithfulStep
  PdflatexModel.
Import ListNotations.

(** ── T2a: boolean edge-closure ─────────────────────────────────────── *)

Definition node_in_b (n : node) (ns : list node) : bool :=
  existsb (fun m => node_eqb m n) ns.

Lemma node_in_b_sound :
  forall n ns, node_in_b n ns = true -> In n ns.
Proof.
  intros n ns H. unfold node_in_b in H.
  apply existsb_exists in H. destruct H as [m [Hin Heq]].
  (* node_eqb m n = true -> m = n *)
  assert (Hmn : m = n).
  { unfold node_eqb in Heq. apply andb_true_iff in Heq. destruct Heq as [Hf Hk].
    apply Nat.eqb_eq in Hf.
    destruct m as [mf mk], n as [nf nk]; simpl in *; subst mf.
    f_equal. destruct mk, nk; simpl in Hk; try discriminate; reflexivity. }
  subst m. exact Hin.
Qed.

Definition edges_closed_b (g : build_graph) : bool :=
  forallb (fun e => andb (node_in_b (fst e) g.(bg_nodes))
                         (node_in_b (snd e) g.(bg_nodes)))
          g.(bg_edges).

Lemma edges_closed_b_sound :
  forall g, edges_closed_b g = true -> edges_closed g.
Proof.
  intros g H u v Hin. unfold edges_closed_b in H.
  rewrite forallb_forall in H.
  specialize (H (u, v) Hin). simpl in H.
  apply andb_true_iff in H. destruct H as [Hu Hv].
  split; [ apply node_in_b_sound; exact Hu
         | apply node_in_b_sound; exact Hv ].
Qed.

(** ── T2b: boolean topological-order certification ──────────────────── *)

Definition index_lt_b (order : list node) (u v : node) : bool :=
  match index_of u order, index_of v order with
  | Some iu, Some iv => Nat.ltb iv iu
  | _, _ => false
  end.

Definition valid_topo_b (g : build_graph) (order : list node) : bool :=
  forallb (fun e => index_lt_b order (fst e) (snd e)) g.(bg_edges).

Lemma valid_topo_b_sound :
  forall g order, valid_topo_b g order = true -> valid_topo g order.
Proof.
  intros g order H u v Hin. unfold valid_topo_b in H.
  rewrite forallb_forall in H.
  specialize (H (u, v) Hin). simpl in H.
  unfold index_lt_b in H.
  destruct (index_of u order) as [iu|] eqn:Eu;
    destruct (index_of v order) as [iv|] eqn:Ev; try discriminate.
  apply Nat.ltb_lt in H. exact H.
Qed.

(** A witnessed order certifies acyclicity. *)
Lemma valid_topo_b_acyclic :
  forall g order, valid_topo_b g order = true -> acyclic_graph g.
Proof.
  intros g order H. exists order. apply valid_topo_b_sound. exact H.
Qed.

(** ── T2: boolean project closure (witness-carrying) ────────────────── *)

Definition project_closed_b (g : build_graph) (order : list node) : bool :=
  andb (edges_closed_b g) (valid_topo_b g order).

Lemma project_closed_b_sound :
  forall g order, project_closed_b g order = true -> project_closed g.
Proof.
  intros g order H. unfold project_closed_b in H.
  apply andb_true_iff in H. destruct H as [Hc Ht].
  split.
  - apply edges_closed_b_sound. exact Hc.
  - eapply valid_topo_b_acyclic. exact Ht.
Qed.

(** ── T4: boolean NoDup on the body's label definitions ─────────────── *)

Fixpoint mem_nat_b (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => orb (Nat.eqb x n) (mem_nat_b n xs)
  end.

Lemma mem_nat_b_iff :
  forall n l, mem_nat_b n l = true <-> In n l.
Proof.
  intros n l. induction l as [|x xs IH]; simpl.
  - split; [discriminate | contradiction].
  - split.
    + intro H. apply orb_true_iff in H. destruct H as [H | H].
      * left. apply Nat.eqb_eq in H. exact H.
      * right. apply IH. exact H.
    + intro H. apply orb_true_iff. destruct H as [H | H].
      * left. apply Nat.eqb_eq. exact H.
      * right. apply IH. exact H.
Qed.

Fixpoint nodup_nat_b (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => andb (negb (mem_nat_b x xs)) (nodup_nat_b xs)
  end.

Lemma nodup_nat_b_sound :
  forall l, nodup_nat_b l = true -> NoDup l.
Proof.
  induction l as [|x xs IH]; simpl; intro H.
  - constructor.
  - apply andb_true_iff in H. destruct H as [Hx Hrest].
    constructor.
    + intro Hin. apply mem_nat_b_iff in Hin.
      rewrite Hin in Hx. simpl in Hx. discriminate.
    + apply IH. exact Hrest.
Qed.

(** ── The capstone-premise checker ──────────────────────────────────── *)

(** [project_wf_dec p pf order = true] certifies, in one boolean, EXACTLY the
    conditions [pdflatex_compile_safe p pf] needs (T2 + T3) PLUS the T4
    coherence obligation.  [order] is the caller-supplied topological order of
    the build graph (produced by the OCaml [Build_graph] topo sort); the
    checker verifies it rather than re-searching for it. *)
Definition project_wf_dec
    (p : pdflatex_project) (pf : pdflatex_profile)
    (order : list node) : bool :=
  (* T2 — build graph closed + acyclic (via the witnessed order) *)
  project_closed_b p.(proj_graph) order &&
  (* T3 — engine admits the profile's declared features *)
  all_features_compatible pf.(prof_features) pf.(prof_engine) &&
  (* T3 — engine admits every feature THE DOCUMENT BODY requires *)
  all_features_compatible (body_required_features p.(proj_body))
                          pf.(prof_engine) &&
  (* T4 — the body defines each label at most once *)
  nodup_nat_b (body_label_defs p.(proj_body)).

(** ── SOUNDNESS: true ==> the capstone's exact hypotheses (+T4) ─────── *)

Theorem project_wf_dec_sound :
  forall p pf order,
    project_wf_dec p pf order = true ->
    project_well_typed p
    /\ profile_supported p pf
    /\ pdflatex_T4_coherent p.
Proof.
  intros p pf order H. unfold project_wf_dec in H.
  apply andb_true_iff in H. destruct H as [H Hnd].
  apply andb_true_iff in H. destruct H as [H Hbody].
  apply andb_true_iff in H. destruct H as [Hclosed Hdecl].
  (* T2 *)
  assert (Hwt : project_well_typed p).
  { unfold project_well_typed, pdflatex_T2_closed.
    eapply project_closed_b_sound. exact Hclosed. }
  (* T3 — both admissibility obligations *)
  assert (Hsupp : profile_supported p pf).
  { unfold profile_supported. split.
    - apply T3_profile_compatible. exact Hdecl.
    - apply T3_profile_compatible. exact Hbody. }
  (* T4 *)
  assert (Hcoh : pdflatex_T4_coherent p).
  { unfold pdflatex_T4_coherent. apply nodup_nat_b_sound. exact Hnd. }
  auto.
Qed.

(** ── CAPSTONE COROLLARY: a [true] verdict discharges [pdflatex_compile_safe].

    This is the payload: a purely computational check whose success PROVES the
    document compiles safely, converges in ≤2 passes, stays fatal-free, and
    warns iff a \ref is unresolved — the full conclusion of the headline
    theorem, now GOVERNED by a decidable premise-check. *)
Theorem project_wf_dec_compile_safe :
  forall p pf order,
    project_wf_dec p pf order = true ->
    exists out,
      pdflatex_produces p pf out /\
      pdflatex_compilation_succeeds p pf /\
      pdflatex_output_format_well_formed out /\
      (faithful_run p pf 2).(L0Pass.converged) = true /\
      L0Log.log_no_fatal (L0Pass.log (faithful_run p pf 2)) /\
      (L0Log.warnings (L0Pass.log (faithful_run p pf 2)) <> []
         <-> project_has_unresolved_ref p pf) /\
      out = faithful_artefact p pf 2.
Proof.
  intros p pf order H.
  destruct (project_wf_dec_sound p pf order H) as [Hwt [Hsupp _Hcoh]].
  apply pdflatex_compile_safe; assumption.
Qed.

(** ── COMPLETENESS side (mirror-equivalence sanity): a [true] verdict is
    also NECESSARY for the three decidable obligations, so the OCaml mirror
    check and this Coq check agree structurally, not just one-directionally.
    (We prove the T3/T4 direction; the T2 direction is order-relative and
    covered by [project_closed_b_sound]'s witness use above.) *)
Theorem project_wf_dec_complete_T3T4 :
  forall p pf order,
    project_closed_b p.(proj_graph) order = true ->
    profile_supported p pf ->
    pdflatex_T4_coherent p ->
    project_wf_dec p pf order = true.
Proof.
  intros p pf order Hclosed [Hdecl Hbody] Hcoh.
  unfold project_wf_dec.
  rewrite Hclosed. simpl.
  rewrite (profile_admits_implies_bulk _ _ Hdecl). simpl.
  rewrite (profile_admits_implies_bulk _ _ Hbody). simpl.
  (* nodup_nat_b (body_label_defs …) = true from NoDup … *)
  unfold pdflatex_T4_coherent in Hcoh.
  induction (body_label_defs p.(proj_body)) as [|x xs IH]; simpl; [reflexivity|].
  inversion Hcoh as [| x0 l0 Hnin Hnd']; subst.
  apply andb_true_iff. split.
  - destruct (mem_nat_b x xs) eqn:Em; [| reflexivity].
    exfalso. apply Hnin. apply mem_nat_b_iff. exact Em.
  - apply IH. exact Hnd'.
Qed.

(** ── NON-VACUITY: the checker fires [true] on the clean witness project and
    [false] on the duplicate-label / unsupported-feature witnesses. *)

(** Clean project (from PdflatexModel): defines label 5, references it, single
    Tex node, empty edges — order = [that node]. *)
Definition clean_order : list node := [mk_node 0 Tex].

Example project_wf_dec_true_clean :
  project_wf_dec p_clean pf_ok clean_order = true.
Proof. vm_compute. reflexivity. Qed.

(** T4 violation: body defines label 5 twice. *)
Definition p_dup : pdflatex_project :=
  mk_project (mk_graph [mk_node 0 Tex] [])
             [BT_label_def 5; BT_label_def 5].

Example project_wf_dec_false_dup :
  project_wf_dec p_dup pf_ok clean_order = false.
Proof. vm_compute. reflexivity. Qed.

(** T3 violation: body needs OpenType fonts under pdflatex (incompatible). *)
Definition p_otf : pdflatex_project :=
  mk_project (mk_graph [mk_node 0 Tex] [])
             [BT_needs_feature Opentype_fonts].

Example project_wf_dec_false_otf :
  project_wf_dec p_otf pf_ok clean_order = false.
Proof. vm_compute. reflexivity. Qed.

(** …and the SAME OpenType body IS accepted on xelatex (engine-compatible). *)
Definition pf_xe : pdflatex_profile := mk_pdflatex_profile Xelatex [].

Example project_wf_dec_true_otf_on_xe :
  project_wf_dec p_otf pf_xe clean_order = true.
Proof. vm_compute. reflexivity. Qed.
