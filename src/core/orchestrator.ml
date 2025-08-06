(** Cross-Layer Orchestrator - LaTeX Perfectionist v25
    
    Coordinates L0-L4 layers using the version vector protocol
    for atomic, consistent updates across all layers.
    
    Performance budget: 40μs p95, 80μs hard cutoff
*)

open Lwt.Syntax

(* Layer modules *)
module L0 = L0_v25
module L1 = L1_v25
module VV = Version_vector

(* Snapshot storage for each layer *)
type layer_snapshots = {
  mutable l0_tokens : (L0.l0_cache_key * Types.token array) list;
  mutable l1_expanded : (L1.l1_cache_key * Types.token array) list;
  (* L2-L4 to be added *)
}

let snapshots = {
  l0_tokens = [];
  l1_expanded = [];
}

(* Publish function for version vector commits *)
let publish_deltas deltas =
  List.iter (fun (layer, delta_obj) ->
    match layer with
    | VV.L0 ->
        let (key, tokens) = Obj.obj delta_obj in
        snapshots.l0_tokens <- (key, tokens) :: snapshots.l0_tokens
        
    | VV.L1 ->
        let (key, expanded) = Obj.obj delta_obj in
        snapshots.l1_expanded <- (key, expanded) :: snapshots.l1_expanded
        
    | _ -> () (* L2-L4 not implemented yet *)
  ) deltas

(* Process a single edit *)
let process_edit bytes =
  let start = Unix.gettimeofday () in
  
  (* Begin transaction *)
  let* tx = VV.begin_transaction () in
  
  (* L0: Lexing *)
  let* l0_result = Lwt.return (
    try
      (* Get previous state if available *)
      let prev_state = None in (* TODO: retrieve from snapshot *)
      
      (* Lex the chunk *)
      let (tokens, new_state) = L0.lex_chunk ?prev:prev_state bytes in
      
      (* Compute cache key *)
      let l0_key = L0.compute_cache_key bytes new_state in
      
      (* Record delta *)
      VV.record_delta tx VV.L0 (l0_key, tokens);
      
      Ok (tokens, l0_key, new_state)
    with exn ->
      Error (`Fatal, Printf.sprintf "L0 error: %s" (Printexc.to_string exn))
  ) in
  
  match l0_result with
  | Error (severity, msg) ->
      (* Handle L0 error *)
      let action = VV.handle_layer_error tx VV.L0 VV.Fatal msg in
      Lwt.return (Error (`L0_error msg))
      
  | Ok (tokens, l0_key, l0_state) ->
      (* L1: Expansion *)
      let* l1_result = Lwt.return (
        try
          (* Initialize L1 state with L0 key *)
          let l1_env = L1.initial_state l0_key in
          
          (* Create delta *)
          let delta = { L1.unexpanded = tokens; expanded = [||]; macros_used = [] } in
          
          (* Expand with fuel limit *)
          let fuel = 2048 in
          let (expanded_delta, new_l1_state) = L1.expand_delta ~fuel ~env:l1_env delta in
          
          (* Compute L1 cache key *)
          let l1_key = { L1.l0 = l0_key; fuel_left = fuel - new_l1_state.L1.fuel_consumed } in
          
          (* Record delta *)
          VV.record_delta tx VV.L1 (l1_key, expanded_delta.L1.expanded);
          
          Ok (expanded_delta.L1.expanded, l1_key)
        with exn ->
          Error (`Warn, Printf.sprintf "L1 warning: %s" (Printexc.to_string exn))
      ) in
      
      let* final_result = match l1_result with
      | Error (severity, msg) ->
          (* Handle L1 error *)
          let action = VV.handle_layer_error tx VV.L1 VV.Warn msg in
          (* Continue with unexpanded tokens *)
          Lwt.return (Ok tokens)
          
      | Ok (expanded_tokens, l1_key) ->
          Lwt.return (Ok expanded_tokens)
      in
      
      (* Commit transaction *)
      let* commit_result = VV.commit_transaction tx publish_deltas in
      
      (* Check orchestrator performance *)
      let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
      if elapsed > 40. then
        Printf.eprintf "Warning: Orchestrator exceeded p95 target: %.0fμs\n" elapsed;
      if elapsed > 80. then
        Printf.eprintf "ERROR: Orchestrator exceeded hard cutoff: %.0fμs\n" elapsed;
      
      match commit_result with
      | VV.Committed ->
          Lwt.return final_result
      | VV.Retry ->
          (* Retry the edit *)
          process_edit bytes
      | VV.Aborted reason ->
          Lwt.return (Error (`Aborted reason))

(* Batch processing for multiple edits *)
let process_edits_batch edits =
  (* Process in parallel when possible *)
  let process_one edit =
    process_edit edit
  in
  Lwt_list.map_p process_one edits

(* Initialize orchestrator *)
let init () =
  (* Warm up caches *)
  let _ = L0.initial_state () in
  let dummy_key = { L0.chunk_id = 0; hash = 0L } in
  let _ = L1.initial_state dummy_key in
  
  (* Start background tasks *)
  (* TODO: Cache persistence, telemetry, etc. *)
  ()

(* Debugging: check layer synchronization *)
let check_sync () =
  VV.debug_print ();
  Printf.printf "L0 cache entries: %d\n" (List.length snapshots.l0_tokens);
  Printf.printf "L1 cache entries: %d\n" (List.length snapshots.l1_expanded)

(* Performance monitoring *)
module Perf = struct
  type stats = {
    mutable total_edits : int;
    mutable l0_time_us : float;
    mutable l1_time_us : float;
    mutable orchestrator_time_us : float;
    mutable cache_hits : int;
    mutable cache_misses : int;
  }
  
  let stats = {
    total_edits = 0;
    l0_time_us = 0.;
    l1_time_us = 0.;
    orchestrator_time_us = 0.;
    cache_hits = 0;
    cache_misses = 0;
  }
  
  let report () =
    if stats.total_edits > 0 then
      let avg_l0 = stats.l0_time_us /. float stats.total_edits in
      let avg_l1 = stats.l1_time_us /. float stats.total_edits in
      let avg_orch = stats.orchestrator_time_us /. float stats.total_edits in
      let hit_rate = float stats.cache_hits /. 
                     float (stats.cache_hits + stats.cache_misses) *. 100. in
      
      Printf.printf "\nPerformance Report:\n";
      Printf.printf "  Total edits: %d\n" stats.total_edits;
      Printf.printf "  Average L0 time: %.1fμs\n" avg_l0;
      Printf.printf "  Average L1 time: %.1fμs\n" avg_l1;
      Printf.printf "  Average orchestrator time: %.1fμs\n" avg_orch;
      Printf.printf "  Cache hit rate: %.1f%%\n" hit_rate;
      Printf.printf "  Total average: %.1fμs (target: <1000μs)\n" 
        (avg_l0 +. avg_l1 +. avg_orch)
end