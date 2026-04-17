(** Project graph: directed inclusion graph with cycle detection. *)

type edge = {
  src : string;  (** Including file (absolute path). *)
  dst : string;  (** Included file (absolute path). *)
  command : string;  (** ["input"] or ["include"]. *)
}

type project_graph = {
  root : string;
  files : string list;  (** All reachable files in topological order. *)
  edges : edge list;
  cycles : string list list;  (** Cycle paths, if any. *)
  unresolved : (string * string) list;  (** [(source_file, raw_path)]. *)
}

val build : root:string -> project_graph
(** Build the inclusion graph starting from [root]. Recursively follows [\input]
    and [\include], respects [\includeonly] from root file. *)

val is_acyclic : project_graph -> bool
val file_count : project_graph -> int
