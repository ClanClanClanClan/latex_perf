(** * ProjectClosure — T2 project closure theorem (memo §5, §5.5).

    Models the T2 pre-compile gate: a project is "closed" iff every
    referenced file resolves within the project and the build DAG is
    acyclic. This is the Coq counterpart of
    [Compile_contract.check_ready_to_compile] T2 branch.

    Extends [ProjectSemantics.v] (single-project graph) with a build-
    artefact layer that matches the OCaml [Build_graph] module.

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** ── Project model ────────────────────────────────────────────────── *)

Definition file_id := nat.

Inductive artefact_kind : Type :=
  | Tex | Aux | Bbl | Bib | Pdf | Log.

Definition artefact_kind_eqb (a b : artefact_kind) : bool :=
  match a, b with
  | Tex, Tex | Aux, Aux | Bbl, Bbl
  | Bib, Bib | Pdf, Pdf | Log, Log => true
  | _, _ => false
  end.

Record node := mk_node {
  n_file : file_id;
  n_kind : artefact_kind;
}.

Definition node_eqb (a b : node) : bool :=
  andb (Nat.eqb a.(n_file) b.(n_file))
       (artefact_kind_eqb a.(n_kind) b.(n_kind)).

Definition edge := (node * node)%type.

(** A build graph: a node set + directed edges [(producer, consumer)]. *)
Record build_graph := mk_graph {
  bg_nodes : list node;
  bg_edges : list edge;
}.

(** ── Closure: every referenced node is known ──────────────────────── *)

Definition node_known (g : build_graph) (n : node) : Prop :=
  In n g.(bg_nodes).

Definition edges_closed (g : build_graph) : Prop :=
  forall u v, In (u, v) g.(bg_edges) -> node_known g u /\ node_known g v.

(** ── Acyclicity via topological order (mirrors IncludeGraphSound) ── *)

Fixpoint index_of (n : node) (l : list node) : option nat :=
  match l with
  | [] => None
  | x :: xs =>
      if node_eqb x n then Some 0
      else match index_of n xs with
           | Some i => Some (S i)
           | None => None
           end
  end.

Definition valid_topo (g : build_graph) (order : list node) : Prop :=
  forall u v, In (u, v) g.(bg_edges) ->
    match index_of u order, index_of v order with
    | Some iu, Some iv => iv < iu
    | _, _ => False
    end.

Definition acyclic_graph (g : build_graph) : Prop :=
  exists order, valid_topo g order.

(** ── T2: project closure predicate ────────────────────────────────── *)

Definition project_closed (g : build_graph) : Prop :=
  edges_closed g /\ acyclic_graph g.

(** ── Theorem 1: empty graph is closed ─────────────────────────────── *)

Theorem empty_graph_closed :
  project_closed (mk_graph [] []).
Proof.
  split.
  - intros u v Hin. simpl in Hin. destruct Hin.
  - exists []. unfold valid_topo. intros u v Hin. simpl in Hin. destruct Hin.
Qed.

(** ── Theorem 2: closed ⇒ every edge endpoint is known ─────────────── *)

Theorem closed_edges_resolve :
  forall g u v,
    project_closed g ->
    In (u, v) g.(bg_edges) ->
    node_known g u /\ node_known g v.
Proof.
  intros g u v [Hedges _] Hin. apply Hedges. exact Hin.
Qed.

(** ── Supporting lemma: index_of reflects membership ───────────────── *)

Lemma index_of_Some_in :
  forall n l i, index_of n l = Some i -> In n l.
Proof.
  intros n l. induction l as [|x xs IH]; intros i H.
  - simpl in H. discriminate.
  - simpl in H. destruct (node_eqb x n) eqn:E.
    + left. unfold node_eqb in E.
      apply andb_prop in E. destruct E as [Ef Ek].
      apply Nat.eqb_eq in Ef.
      destruct x as [xf xk]. destruct n as [nf nk]. simpl in *.
      subst xf. f_equal.
      destruct xk, nk; simpl in Ek; try reflexivity; discriminate.
    + right. destruct (index_of n xs) as [j|] eqn:Ej.
      * apply (IH j). reflexivity.
      * discriminate.
Qed.

(** ── Theorem 3: every edge endpoint appears in any valid topo ─────── *)

Theorem topo_covers_edge_endpoints :
  forall g order u v,
    valid_topo g order ->
    In (u, v) g.(bg_edges) ->
    (exists iu, index_of u order = Some iu) /\
    (exists iv, index_of v order = Some iv).
Proof.
  intros g order u v Hvalid Hin.
  specialize (Hvalid u v Hin).
  destruct (index_of u order) as [iu|] eqn:Eu;
    destruct (index_of v order) as [iv|] eqn:Ev;
    try contradiction.
  split; [exists iu | exists iv]; reflexivity.
Qed.

(** ── Theorem 4: a two-node cycle is not closed ─────────────────────── *)

Theorem two_node_cycle_not_closed :
  forall u v,
    u <> v ->
    ~ project_closed (mk_graph [u; v] [(u, v); (v, u)]).
Proof.
  intros u v Hne [_ [order Hvalid]].
  assert (Huv := Hvalid u v (or_introl eq_refl)).
  assert (Hvu := Hvalid v u (or_intror (or_introl eq_refl))).
  destruct (index_of u order) as [iu|]; [| exact Huv].
  destruct (index_of v order) as [iv|]; [| exact Huv].
  lia.
Qed.

(** ── Theorem 5: single-node graph with no edges is closed ─────────── *)

Theorem singleton_closed :
  forall n, project_closed (mk_graph [n] []).
Proof.
  intros n. split.
  - intros u v Hin. simpl in Hin. destruct Hin.
  - exists [n]. unfold valid_topo. intros u v Hin. simpl in Hin. destruct Hin.
Qed.

(** ── Theorem 6: closure is preserved under edge-free node addition ── *)

Theorem closure_stable_under_node_addition :
  forall g n,
    project_closed g ->
    project_closed (mk_graph (n :: g.(bg_nodes)) g.(bg_edges)).
Proof.
  intros g n [Hedges [order Hvalid]].
  split.
  - intros u v Hin. simpl. specialize (Hedges u v Hin).
    destruct Hedges as [Hu Hv]. split; right; assumption.
  - exists order. unfold valid_topo. simpl. exact Hvalid.
Qed.

(** ── Decidability of artefact_kind equality ───────────────────────── *)

Theorem artefact_kind_eq_dec :
  forall (a b : artefact_kind), {a = b} + {a <> b}.
Proof.
  intros a b. destruct a, b;
    try (left; reflexivity); right; discriminate.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition project_closure_zero_admits : True := I.
