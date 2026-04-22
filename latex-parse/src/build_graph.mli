(** Build-pipeline dependency graph (memo §5.5, v26.2).

    Distinct from [project_graph] (include graph of .tex files), from
    [dependency_graph] (semantic chunk invalidation), and from [Validator_dag]
    (rule dependencies). See [docs/FOUR_GRAPHS.md].

    Nodes are BUILD ARTEFACTS: `.tex`, `.aux`, `.bbl`, `.bib`, `.pdf`, `.log`.
    Edges are "produced-from" relationships:
    - tex → aux (pdflatex pass produces .aux from .tex)
    - bib → bbl (bibtex produces .bbl from .bib + .aux)
    - tex → pdf (final pdflatex pass produces .pdf)

    T2 project-closure check (`Compile_contract`) uses this graph to verify
    required artefacts resolve and no cycles exist. *)

type node_id
type artefact_kind = Tex | Aux | Bbl | Bib | Pdf | Log

type node = {
  id : node_id;
  kind : artefact_kind;
  path : string;
  exists : bool;
      (** Whether the file currently exists on disk. Informational; pre-compile
          state always has tex existing and aux/bbl/pdf possibly not. *)
}

type edge = { from_id : node_id; to_id : node_id; reason : string }
type t

val of_project : Project_model.t -> t
(** Build a [t] from a project_model. Adds one [Tex] node per .tex file, one
    [Aux] per tex (predicted path, may not exist yet), and the corresponding
    produce-from edges.

    This function does NOT read .bib files to resolve them — that requires
    aux_state parsing. v26.2 [of_project] provides the scaffolding;
    [Compile_contract] enriches the graph with .bbl nodes after aux_state runs. *)

val nodes : t -> node list
(** All nodes (artefact + file) in the graph. *)

val edges : t -> edge list
(** All producer→consumer edges. *)

val find_node : t -> node_id -> node option
(** Look up a node by its [node_id]. *)

val find_by_path : t -> string -> node option
(** Look up the [Tex] node for a given source path, if any. *)

val is_acyclic : t -> bool
(** DFS-based acyclicity check. A healthy build_graph is always acyclic (no
    build artefact circularly depends on itself); this is the T2 precondition. *)

val kind_to_string : artefact_kind -> string
