(* ══════════════════════════════════════════════════════════════════════
   Project_state — per-file semantic analysis with global projection

   Analyzes each file in a project graph via Semantic_state.analyze, then merges
   label/ref tables to detect cross-file duplicates and undefined references.
   ══════════════════════════════════════════════════════════════════════ *)

type file_state = { path : string; sem : Semantic_state.semantic_state }

type project_state = {
  graph : Project_graph.project_graph;
  file_states : file_state list;
  global_labels : (string * string) list;
  global_refs : (string * string) list;
  cross_file_duplicates : (string * string list) list;
  cross_file_undefined : (string * string) list;
}

let read_file path =
  try
    let ic = open_in path in
    Fun.protect
      ~finally:(fun () -> close_in ic)
      (fun () ->
        let n = in_channel_length ic in
        really_input_string ic n)
  with Sys_error _ -> ""

let build (graph : Project_graph.project_graph) : project_state =
  (* Analyze each file *)
  let file_states =
    List.map
      (fun path ->
        let src = read_file path in
        let sem = Semantic_state.analyze src in
        { path; sem })
      graph.files
  in
  (* Collect global labels: (key, file) *)
  let global_labels =
    List.concat_map
      (fun fs ->
        List.map
          (fun (l : Semantic_state.label_entry) -> (l.key, fs.path))
          fs.sem.labels)
      file_states
  in
  (* Collect global refs: (key, file) *)
  let global_refs =
    List.concat_map
      (fun fs ->
        List.map
          (fun (r : Semantic_state.ref_entry) -> (r.key, fs.path))
          fs.sem.refs)
      file_states
  in
  (* Detect cross-file duplicate labels *)
  let label_files = Hashtbl.create 64 in
  List.iter
    (fun (key, file) ->
      let existing = try Hashtbl.find label_files key with Not_found -> [] in
      if not (List.mem file existing) then
        Hashtbl.replace label_files key (file :: existing))
    global_labels;
  let cross_file_duplicates =
    Hashtbl.fold
      (fun key files acc ->
        if List.length files > 1 then (key, List.rev files) :: acc else acc)
      label_files []
    |> List.sort (fun (a, _) (b, _) -> String.compare a b)
  in
  (* Detect cross-file undefined refs *)
  let label_set = Hashtbl.create 64 in
  List.iter (fun (key, _) -> Hashtbl.replace label_set key ()) global_labels;
  let cross_file_undefined =
    List.filter_map
      (fun (key, file) ->
        if Hashtbl.mem label_set key then None else Some (key, file))
      global_refs
    |> List.sort_uniq (fun (a, _) (b, _) -> String.compare a b)
  in
  {
    graph;
    file_states;
    global_labels;
    global_refs;
    cross_file_duplicates;
    cross_file_undefined;
  }
