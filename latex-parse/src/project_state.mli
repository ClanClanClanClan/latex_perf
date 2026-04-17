(** Project state: per-file semantic analysis with global projection. *)

type file_state = { path : string; sem : Semantic_state.semantic_state }

type project_state = {
  graph : Project_graph.project_graph;
  file_states : file_state list;
  global_labels : (string * string) list;  (** [(key, defining_file)]. *)
  global_refs : (string * string) list;  (** [(key, referencing_file)]. *)
  cross_file_duplicates : (string * string list) list;  (** [(key, files)]. *)
  cross_file_undefined : (string * string) list;
      (** [(key, referencing_file)]. *)
}

val build : Project_graph.project_graph -> project_state
(** Analyze all files in the graph, compute global label/ref projection. *)
