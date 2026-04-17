(* ══════════════════════════════════════════════════════════════════════
   Invalidation — compute minimal chunk invalidation set

   Pipeline: syntactic diff → semantic edge extraction → BFS propagation → union
   = final invalidation set. Replaces the whole-source fallback for cross-chunk
   rules.
   ══════════════════════════════════════════════════════════════════════ *)

let compute ~(old_snap : Chunk_store.snapshot)
    ~(new_snap : Chunk_store.snapshot) : int list =
  (* 1. Syntactic diff: which chunks changed by hash? *)
  let dirty = Chunk_store.diff_snapshots old_snap new_snap in
  (* If chunk count changed, diff_snapshots already returns all indices *)
  if Array.length old_snap.chunks <> Array.length new_snap.chunks then dirty
  else
    (* 2. Extract semantic edges from the new snapshot *)
    let edges = Semantic_edges.extract_edges new_snap.chunks in
    (* 3. Build dependency graph *)
    let graph = Dependency_graph.build edges (Array.length new_snap.chunks) in
    (* 4. Propagate dirty set through dependency edges *)
    Dependency_graph.affected_set graph dirty
