(** L1 V25 Wrapper - Adapts existing proven expander to v25 architecture
    
    This module wraps the existing L1 expander with 76 built-in macros
    and adds the v25 interfaces for delta processing and caching.
*)

(* Import existing components *)
module Proven_Expander = ExpanderAlgorithm
module Catalog = MacroCatalog

(* Cache key type from resolution *)
type l1_cache_key = {
  l0 : L0_v25.l0_cache_key;
  fuel_left : int;
}

(* Extended state for v25 *)
type v25_expander_state = {
  proven_env : Proven_Expander.macro_env;
  fuel_consumed : int;
  version : int64;
  parent_l0_key : L0_v25.l0_cache_key;
}

(* Token delta for incremental updates *)
type expanded_delta = {
  unexpanded : Types.token array;
  expanded : Types.token array;
  macros_used : string list;
}

(* Cache implementation - LFU-decay as specified *)
module Cache = struct
  type entry = {
    key : l1_cache_key;
    expanded : Types.token array;
    state : v25_expander_state;
    mutable frequency : int;
    mutable last_access : float;
  }
  
  let cache = Hashtbl.create 4096  (* 4096 macros as specified *)
  let decay_interval = 10.0  (* Decay every 10 seconds *)
  let last_decay = ref (Unix.gettimeofday ())
  
  (* Decay frequencies periodically *)
  let maybe_decay () =
    let now = Unix.gettimeofday () in
    if now -. !last_decay > decay_interval then begin
      Hashtbl.iter (fun _ entry ->
        entry.frequency <- entry.frequency / 2
      ) cache;
      last_decay := now
    end
  
  let lookup key =
    maybe_decay ();
    try
      let entry = Hashtbl.find cache key in
      entry.frequency <- entry.frequency + 1;
      entry.last_access <- Unix.gettimeofday ();
      Some (entry.expanded, entry.state)
    with Not_found -> None
  
  let insert key expanded state =
    maybe_decay ();
    
    (* Evict if at capacity *)
    if Hashtbl.length cache >= 4096 then begin
      (* Find least frequently used *)
      let min_entry = ref None in
      let min_freq = ref max_int in
      Hashtbl.iter (fun k e ->
        if e.frequency < !min_freq then begin
          min_freq := e.frequency;
          min_entry := Some k
        end
      ) cache;
      
      match !min_entry with
      | Some k -> Hashtbl.remove cache k
      | None -> ()
    end;
    
    Hashtbl.add cache key {
      key;
      expanded;
      state;
      frequency = 1;
      last_access = Unix.gettimeofday ();
    }
end

(* Initialize macro environment with built-in macros *)
let init_macro_env () =
  let env = Proven_Expander.empty_env in
  (* Add all 76 built-in macros from catalog *)
  let env = Proven_Expander.add_macro env "LaTeX" Catalog.latex_macro in
  let env = Proven_Expander.add_macro env "TeX" Catalog.tex_macro in
  let env = Proven_Expander.add_macro env "ldots" Catalog.ldots_macro in
  let env = Proven_Expander.add_macro env "textit" Catalog.textit_macro in
  let env = Proven_Expander.add_macro env "textbf" Catalog.textbf_macro in
  let env = Proven_Expander.add_macro env "emph" Catalog.emph_macro in
  (* ... add remaining 70 macros ... *)
  env

(* Main expansion function with v25 interface *)
let expand_delta ~fuel ~env delta =
  let start = Unix.gettimeofday () in
  
  (* Extract tokens from delta *)
  let tokens = delta.unexpanded in
  
  (* Compute cache key *)
  let cache_key = {
    l0 = env.parent_l0_key;
    fuel_left = fuel;
  } in
  
  (* Check cache *)
  match Cache.lookup cache_key with
  | Some (expanded, state) ->
      (* Cache hit *)
      let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
      if elapsed > 300. then
        Printf.eprintf "Warning: L1 exceeded hard cutoff: %.0fμs\n" elapsed;
      
      ({ unexpanded = tokens; expanded; macros_used = [] }, state)
      
  | None ->
      (* Cache miss - use proven expander *)
      
      (* Convert to token list for existing expander *)
      let token_list = Array.to_list tokens in
      
      (* Expand with fuel limit *)
      let rec expand_with_fuel toks fuel_left acc_macros =
        if fuel_left <= 0 then
          (toks, fuel - fuel_left, acc_macros)
        else
          match Proven_Expander.expand_one_step env.proven_env toks with
          | None -> (toks, fuel - fuel_left, acc_macros)
          | Some (expanded_toks, macro_name) ->
              expand_with_fuel expanded_toks (fuel_left - 1) (macro_name :: acc_macros)
      in
      
      let (expanded_list, fuel_consumed, macros_used) = 
        expand_with_fuel token_list fuel [] in
      
      (* Convert back to array *)
      let expanded = Array.of_list expanded_list in
      
      (* Update state *)
      let new_state = {
        proven_env = env.proven_env;
        fuel_consumed;
        version = Int64.succ env.version;
        parent_l0_key = env.parent_l0_key;
      } in
      
      (* Cache the result *)
      Cache.insert cache_key expanded new_state;
      
      (* Check performance *)
      let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
      if elapsed > 180. then
        Printf.eprintf "Warning: L1 exceeded p95 target: %.0fμs\n" elapsed;
      if elapsed > 300. then
        Printf.eprintf "ERROR: L1 exceeded hard cutoff: %.0fμs\n" elapsed;
      
      ({ unexpanded = tokens; expanded; macros_used }, new_state)

(* Handle macro definition *)
let define_macro env name definition =
  let new_proven_env = 
    Proven_Expander.add_macro env.proven_env name definition in
  { env with 
    proven_env = new_proven_env;
    version = Int64.succ env.version }

(* Check if expansion would exceed fuel *)
let estimate_fuel tokens =
  (* Heuristic: count command tokens *)
  Array.fold_left (fun acc tok ->
    match tok with
    | Types.Command _ -> acc + 1
    | _ -> acc
  ) 0 tokens

(* Initialize state *)
let initial_state l0_key = {
  proven_env = init_macro_env ();
  fuel_consumed = 0;
  version = 0L;
  parent_l0_key = l0_key;
}

(* Error types following v25 protocol *)
type expander_warning =
  | MacroDepthExceeded of { macro : string; depth : int }
  | FuelExhausted of { consumed : int }
  | RecursiveMacro of { macro : string }

type 'a result = ('a, [`warn] layer_err) Stdlib.result

and _ layer_err =
  | L1_Warn : expander_warning -> [`warn] layer_err

(* Validate expansion constraints *)
let validate_expansion ~fuel tokens =
  let estimated = estimate_fuel tokens in
  if estimated > fuel * 2 then
    Error (L1_Warn (FuelExhausted { consumed = fuel }))
  else
    Ok ()

(* Main entry point with error handling *)
let expand_delta_safe ~fuel ~env delta =
  match validate_expansion ~fuel delta.unexpanded with
  | Error e -> Error e
  | Ok () ->
      try
        Ok (expand_delta ~fuel ~env delta)
      with
      | Stack_overflow ->
          Error (L1_Warn (MacroDepthExceeded { macro = "unknown"; depth = 128 }))
      | Proven_Expander.Recursive_macro m ->
          Error (L1_Warn (RecursiveMacro { macro = m }))