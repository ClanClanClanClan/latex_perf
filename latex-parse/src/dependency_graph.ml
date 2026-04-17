(* ══════════════════════════════════════════════════════════════════════
   Dependency_graph — chunk-level dependency graph with BFS propagation

   Builds an adjacency list from semantic edges. Given a dirty set, computes the
   transitive closure of affected chunks via BFS.
   ══════════════════════════════════════════════════════════════════════ *)

type t = { adj : (int, int list) Hashtbl.t; chunk_count : int }

let build (edges : Semantic_edges.edge list) (chunk_count : int) : t =
  let adj = Hashtbl.create (chunk_count * 2) in
  for i = 0 to chunk_count - 1 do
    Hashtbl.replace adj i []
  done;
  List.iter
    (fun (e : Semantic_edges.edge) ->
      let existing =
        try Hashtbl.find adj e.source_chunk with Not_found -> []
      in
      if not (List.mem e.target_chunk existing) then
        Hashtbl.replace adj e.source_chunk (e.target_chunk :: existing))
    edges;
  { adj; chunk_count }

let affected_set (g : t) (dirty : int list) : int list =
  let visited = Hashtbl.create (g.chunk_count * 2) in
  let queue = Queue.create () in
  List.iter
    (fun d ->
      if not (Hashtbl.mem visited d) then (
        Hashtbl.replace visited d ();
        Queue.push d queue))
    dirty;
  while not (Queue.is_empty queue) do
    let node = Queue.pop queue in
    let neighbors = try Hashtbl.find g.adj node with Not_found -> [] in
    List.iter
      (fun nb ->
        if not (Hashtbl.mem visited nb) then (
          Hashtbl.replace visited nb ();
          Queue.push nb queue))
      neighbors
  done;
  let result = Hashtbl.fold (fun k () acc -> k :: acc) visited [] in
  List.sort compare result
