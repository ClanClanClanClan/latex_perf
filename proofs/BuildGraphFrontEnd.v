(** * BuildGraphFrontEnd — what D1's Channel 1 actually says about the SHIPPED
      encoder.

    D1 ([PdflatexFatalChannels.model_fatal_iff]) proves

        model_fatal p pf  <->  ch_edge p \/ ch_decl p pf \/ ch_body p pf

    and its own header warns that this is a statement about THE MODEL'S IMAGE
    OF A PROJECT, because what a real document contains reaches the model only
    through an unverified OCaml encoder. OPEN-077 recorded that two of the
    three channels look unreachable in production and recommended making
    Channel 1 reachable as the next proof.

    MEASURING THE ENCODER FIRST CHANGED THAT RECOMMENDATION. The shipped
    [Build_graph.of_project] (latex-parse/src/build_graph.ml:30) emits, per
    project file, a Tex node, a predicted Aux node and the edge Tex->Aux, plus
    a Pdf node and Tex->Pdf for the root. EVERY EDGE IT CREATES HAS BOTH
    ENDPOINTS IN THE NODE LIST, by construction. So no graph it builds can
    carry a dangling edge, and Channel 1 cannot fire on one.

    This file proves that, rather than asserting it. The payoff is a precise
    statement of a LIMIT of the guarantee:

        for every project the encoder can build, model_fatal collapses to
        ch_decl \/ ch_body

    and, with OPEN-077's finding that [declared_features] is hard-wired empty
    so ch_decl is also unreachable, to ch_body alone.

    ⚠ WHAT THIS DOES NOT SAY. It does NOT say real projects have no missing
    inputs. It says the ENCODER never reports one through this channel. The
    shipped missing-input check is a FILESYSTEM PROBE — [Compile_contract.t2_check]
    filters [Project_model.all_files] on [Sys.file_exists] — and reaches the
    verdict as [T2_project_not_closed (`Missing_file _)] without ever touching
    [bg_edges]. So the model's Channel 1 and the tool's T2 are DISJOINT
    mechanisms that happen to share a name. Recorded as OPEN-095. *)

From Coq Require Import List Arith Bool.
Import ListNotations.

From LaTeXPerfectionist Require Import ProjectClosure PdflatexModel
  PdflatexFatalChannels.

(** ── The encoder's shape, in Coq ──────────────────────────────────────

    A faithful mirror of [Build_graph.of_project]'s STRUCTURE. A project file
    is characterised, for graph purposes, by one bit: is it the root (which
    additionally predicts a .pdf)? Paths and existence do not enter the graph
    the model sees — [Compile_evidence.graph_of_build_graph] projects each node
    onto [n_file], a sequential index, and [n_kind].

    Node numbering mirrors the OCaml exactly: ids are minted in creation order
    ([mk_id] increments per node) and [graph_of_build_graph] re-indexes by
    POSITION in [Build_graph.nodes], which after the final [List.rev] is that
    same creation order. The two coincide, so a single counter models both. *)

Fixpoint gen (i : nat) (roots : list bool) : list node * list edge :=
  match roots with
  | [] => ([], [])
  | r :: rest =>
      let tex := mk_node i Tex in
      let aux := mk_node (S i) Aux in
      if r then
        let pdf := mk_node (S (S i)) Pdf in
        let p := gen (S (S (S i))) rest in
        (tex :: aux :: pdf :: fst p, (tex, aux) :: (tex, pdf) :: snd p)
      else
        let p := gen (S (S i)) rest in
        (tex :: aux :: fst p, (tex, aux) :: snd p)
  end.

Definition graph_of_files (roots : list bool) : build_graph :=
  let p := gen 0 roots in mk_graph (fst p) (snd p).

(** ── Theorem 1: every graph the encoder can build is edge-closed ─────

    Generalised over the starting index, which is what makes the induction go
    through: the recursive call starts at [S (S i)] or [S (S (S i))], so the
    statement cannot be fixed at 0. *)

Lemma gen_edges_closed :
  forall roots i u v,
    In (u, v) (snd (gen i roots)) ->
    In u (fst (gen i roots)) /\ In v (fst (gen i roots)).
Proof.
  induction roots as [| r rest IH]; intros i u v Hin.
  - simpl in Hin. contradiction.
  - destruct r; simpl in Hin |- *.
    + (* root: two edges, three nodes *)
      destruct Hin as [Heq | [Heq | Hrest]].
      * inversion Heq; subst; split; simpl; auto.
      * inversion Heq; subst; split; simpl; auto.
      * apply IH in Hrest. destruct Hrest as [Hu Hv].
        split; simpl; auto.
    + (* non-root: one edge, two nodes *)
      destruct Hin as [Heq | Hrest].
      * inversion Heq; subst; split; simpl; auto.
      * apply IH in Hrest. destruct Hrest as [Hu Hv].
        split; simpl; auto.
Qed.

Theorem graph_of_files_edges_closed :
  forall roots, edges_closed (graph_of_files roots).
Proof.
  intros roots u v Hin.
  unfold graph_of_files, node_known in *. simpl in *.
  apply gen_edges_closed in Hin. exact Hin.
Qed.

(** ── Theorem 2 (the payoff): Channel 1 is UNREACHABLE for encoder graphs ── *)

Theorem encoder_graph_no_ch_edge :
  forall roots body, ~ ch_edge (mk_project (graph_of_files roots) body).
Proof.
  intros roots body [u [v [Hin Hbad]]]. simpl in Hin, Hbad.
  pose proof (graph_of_files_edges_closed roots u v Hin) as [Hu Hv].
  unfold node_known in Hu, Hv. simpl in Hu, Hv.
  destruct Hbad as [H | H]; [apply H; exact Hu | apply H; exact Hv].
Qed.

(** ── Corollary: what model_fatal REDUCES TO in production ────────────

    Composed with D1. For any project the encoder can build, the three-channel
    disjunction loses its first disjunct — not because the channel is wrong,
    but because nothing the encoder produces can satisfy it. *)

Corollary encoder_model_fatal_iff :
  forall roots body pf,
    let p := mk_project (graph_of_files roots) body in
    model_fatal p pf <-> (ch_decl p pf \/ ch_body p pf).
Proof.
  intros roots body pf p. split.
  - intro Hf. apply model_fatal_iff in Hf.
    destruct Hf as [He | Hrest].
    + exfalso. exact (encoder_graph_no_ch_edge roots body He).
    + exact Hrest.
  - intro H. apply model_fatal_iff. right. exact H.
Qed.

(** ── Zero-admit witness ───────────────────────────────────────────── *)
Definition build_graph_front_end_zero_admits : True := I.
