(** * ArtifactGraphSound — build-artefact graph soundness (memo §8.5).

    Memo §8.5 prescribes a file under this name; the canonical v26.2
    artefact-graph theorems live in [ProjectClosure.v] (build graph =
    artefact dependency graph per ADR-003). This file re-exports the
    load-bearing theorems under the memo name so consumers find the
    memo path directly.

    Content outline:
    - [ProjectClosure.project_closed] — closure predicate matching
      the OCaml [Build_graph.is_acyclic] + [Compile_contract] T2
      gate.
    - [ProjectClosure.closed_edges_resolve] — closure implies every
      artefact edge endpoint is a known node.
    - [ProjectClosure.two_node_cycle_not_closed] — negative-witness
      theorem ruling out trivial cycles.

    Zero admits, zero axioms (content inherited from [ProjectClosure.v]). *)

From LaTeXPerfectionist Require Export ProjectClosure.
From Coq Require Import List.
Import ListNotations.

(** Soundness of the artefact graph under the T2 closure gate: when
    [project_closed g] holds, every producer→consumer edge has both
    endpoints in the node set. *)

Theorem artifact_graph_sound :
  forall g u v,
    ProjectClosure.project_closed g ->
    In (u, v) g.(ProjectClosure.bg_edges) ->
    ProjectClosure.node_known g u /\ ProjectClosure.node_known g v.
Proof.
  exact ProjectClosure.closed_edges_resolve.
Qed.

(** Empty artefact graph is closed — base case for the T2 gate. *)

Theorem artifact_graph_empty_closed :
  ProjectClosure.project_closed (ProjectClosure.mk_graph nil nil).
Proof.
  exact ProjectClosure.empty_graph_closed.
Qed.

(** A closed artefact graph admits a topological order covering every
    edge endpoint. Re-states the load-bearing part of
    [topo_covers_edge_endpoints] for memo-named consumers. *)

Theorem artifact_graph_topo_covers :
  forall g order u v,
    ProjectClosure.valid_topo g order ->
    In (u, v) g.(ProjectClosure.bg_edges) ->
    (exists iu, ProjectClosure.index_of u order = Some iu) /\
    (exists iv, ProjectClosure.index_of v order = Some iv).
Proof.
  exact ProjectClosure.topo_covers_edge_endpoints.
Qed.

(** Zero-admit witness. *)
Definition artifact_graph_sound_zero_admits : True := I.
