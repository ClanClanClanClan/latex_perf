(* parallel_processor.ml - Multi-core parallel processing for LaTeX documents *)

open Deep_state
open Core_lexer_real

(* Parallel processing configuration *)
type parallel_config = {
  num_workers : int;
  chunk_size : int;
  safe_distance : int;  (* Lines to look ahead for safety check *)
}

let default_config = {
  num_workers = Domain.recommended_domain_count ();
  chunk_size = 1000;
  safe_distance = 10;
}

(* Chunk boundaries with safety information *)
type chunk_boundary = {
  start_line : int;
  end_line : int;
  start_state : deep_lexer_state;
  is_safe : bool;  (* Can be processed independently *)
}

(* Result of parallel processing *)
type chunk_result = {
  boundary : chunk_boundary;
  tokens : token list;
  end_state : deep_lexer_state;
  lines_processed : int;
  cache_hits : int;
}

(* Check if a line is a safe boundary for parallel processing *)
let is_safe_boundary state line =
  (* Safe if:
     - Not in verbatim mode
     - Not in math mode (or just exited)
     - No open groups
     - Not in a comment
     - No open conditionals *)
  state.in_verbatim = false &&
  state.math_mode = NoMath &&
  state.group_level = 0 &&
  state.in_comment = false &&
  state.conditionals.if_level = 0 &&
  state.in_csname = false &&
  (* Check the line doesn't start something multi-line *)
  not (String.contains line '{') &&
  not (String.starts_with ~prefix:"\\begin{" line) &&
  not (String.starts_with ~prefix:"\\if" line)

(* Find safe chunk boundaries in document *)
let find_safe_boundaries lines start_line end_line chunk_size =
  let boundaries = ref [] in
  let current = ref start_line in
  
  while !current < end_line do
    let chunk_end = min (!current + chunk_size) end_line in
    
    (* Look for safe boundary near chunk_end *)
    let rec find_safe pos max_look =
      if pos >= end_line || max_look <= 0 then
        chunk_end  (* Give up and use unsafe boundary *)
      else if is_safe_boundary init_deep_state lines.(pos) then
        pos
      else
        find_safe (pos + 1) (max_look - 1)
    in
    
    let safe_end = find_safe chunk_end 50 in
    boundaries := { 
      start_line = !current;
      end_line = safe_end;
      start_state = init_deep_state;  (* Will be updated *)
      is_safe = (safe_end < end_line - 1);
    } :: !boundaries;
    
    current := safe_end
  done;
  
  List.rev !boundaries

(* Process a chunk of lines *)
let process_chunk lines boundary =
  let tokens = Memory_pool.TokenBuffer.create () in
  let cache_hits = ref 0 in
  
  let rec process_lines line_no state =
    if line_no >= boundary.end_line then
      (Memory_pool.TokenBuffer.to_list tokens, state, line_no - boundary.start_line)
    else begin
      (* Use state cache for speedup *)
      let line = lines.(line_no) in
      let (line_tokens, next_state) = 
        match State_cache.lookup state line with
        | Some result -> 
            incr cache_hits;
            result
        | None ->
            State_cache.process_line_cached state line
      in
      
      List.iter (Memory_pool.TokenBuffer.add_token tokens) line_tokens;
      process_lines (line_no + 1) next_state
    end
  in
  
  let (all_tokens, final_state, lines_proc) = 
    process_lines boundary.start_line boundary.start_state in
  
  {
    boundary = boundary;
    tokens = all_tokens;
    end_state = final_state;
    lines_processed = lines_proc;
    cache_hits = !cache_hits;
  }

(* Worker domain for parallel processing *)
let worker_domain work_queue result_queue =
  let rec process_work () =
    match Queue.take_opt work_queue with
    | None -> ()  (* No more work *)
    | Some (lines, boundary) ->
        let result = process_chunk lines boundary in
        Queue.push result result_queue;
        process_work ()
  in
  process_work ()

(* Main parallel processing function *)
let process_parallel ?(config=default_config) lines start_line end_line initial_state =
  (* Find chunk boundaries *)
  let boundaries = find_safe_boundaries lines start_line end_line config.chunk_size in
  
  (* Update boundary states *)
  let boundaries_with_states = 
    let rec update_states boundaries current_state =
      match boundaries with
      | [] -> []
      | b :: rest ->
          let b_with_state = { b with start_state = current_state } in
          
          (* If this is a safe boundary, remaining chunks can be parallel *)
          if b.is_safe then
            b_with_state :: List.map (fun b -> { b with start_state = init_deep_state }) rest
          else
            (* Must process sequentially to get correct state *)
            let result = process_chunk lines b_with_state in
            b_with_state :: update_states rest result.end_state
    in
    update_states boundaries initial_state
  in
  
  (* Separate safe and unsafe chunks *)
  let safe_chunks, unsafe_chunks = 
    List.partition (fun b -> b.is_safe) boundaries_with_states in
  
  (* Process safe chunks in parallel *)
  let parallel_results = 
    if List.length safe_chunks > 1 && config.num_workers > 1 then begin
      let work_queue = Queue.create () in
      let result_queue = Queue.create () in
      
      (* Add work to queue *)
      List.iter (fun boundary ->
        Queue.push (lines, boundary) work_queue
      ) safe_chunks;
      
      (* Spawn worker domains *)
      let domains = Array.init (min config.num_workers (List.length safe_chunks)) (fun _ ->
        Domain.spawn (fun () -> worker_domain work_queue result_queue)
      ) in
      
      (* Wait for completion *)
      Array.iter Domain.join domains;
      
      (* Collect results *)
      let results = ref [] in
      while not (Queue.is_empty result_queue) do
        results := Queue.pop result_queue :: !results
      done;
      !results
    end else
      (* Too few chunks or workers - process sequentially *)
      List.map (process_chunk lines) safe_chunks
  in
  
  (* Process unsafe chunks sequentially *)
  let sequential_results = List.map (process_chunk lines) unsafe_chunks in
  
  (* Merge results in correct order *)
  let all_results = 
    List.sort (fun r1 r2 -> 
      compare r1.boundary.start_line r2.boundary.start_line
    ) (parallel_results @ sequential_results) in
  
  (* Combine tokens and calculate stats *)
  let all_tokens = List.concat_map (fun r -> r.tokens) all_results in
  let total_lines = List.fold_left (fun acc r -> acc + r.lines_processed) 0 all_results in
  let total_cache_hits = List.fold_left (fun acc r -> acc + r.cache_hits) 0 all_results in
  let final_state = (List.hd (List.rev all_results)).end_state in
  
  (all_tokens, final_state, total_lines, total_cache_hits)

(* Adaptive parallel processing based on document characteristics *)
let process_adaptive lines start_line end_line initial_state =
  let doc_size = end_line - start_line in
  
  (* Choose strategy based on document size and content *)
  let config = 
    if doc_size < 100 then
      (* Small edit - sequential is faster *)
      { default_config with num_workers = 1 }
    else if doc_size < 1000 then
      (* Medium edit - limited parallelism *)
      { default_config with num_workers = 2; chunk_size = 200 }
    else
      (* Large edit - full parallelism *)
      { default_config with 
        num_workers = Domain.recommended_domain_count ();
        chunk_size = 
          if doc_size > 10000 then 2000
          else if doc_size > 5000 then 1000
          else 500
      }
  in
  
  (* Check if document has parallel-friendly structure *)
  let parallel_friendly = 
    let sample_lines = 
      Array.sub lines start_line (min 100 (end_line - start_line)) in
    let verbatim_count = Array.fold_left (fun acc line ->
      if String.contains line '{' && String.contains line '}' then acc
      else if String.starts_with ~prefix:"\\begin{verbatim" line then acc + 10
      else acc
    ) 0 sample_lines in
    verbatim_count < 20  (* Not too much verbatim *)
  in
  
  if parallel_friendly then
    process_parallel ~config lines start_line end_line initial_state
  else
    (* Fall back to sequential with caching *)
    let tokens = ref [] in
    let cache_hits = ref 0 in
    let state = ref initial_state in
    
    for i = start_line to end_line - 1 do
      let (line_tokens, next_state) = 
        match State_cache.lookup !state lines.(i) with
        | Some result ->
            incr cache_hits;
            result
        | None ->
            State_cache.process_line_cached !state lines.(i)
      in
      tokens := List.rev_append line_tokens !tokens;
      state := next_state
    done;
    
    (List.rev !tokens, !state, end_line - start_line, !cache_hits)

(* Benchmark parallel vs sequential processing *)
let benchmark_parallel lines =
  Printf.printf "Benchmarking parallel processing...\n";
  
  (* Test different configurations *)
  let configs = [
    ("Sequential", { default_config with num_workers = 1 });
    ("2 workers", { default_config with num_workers = 2 });
    ("4 workers", { default_config with num_workers = 4 });
    ("Auto", default_config);
  ] in
  
  List.iter (fun (name, config) ->
    (* Warm up cache *)
    State_cache.warm_cache ();
    
    let start = Unix.gettimeofday () in
    let _, _, lines_proc, cache_hits = 
      process_parallel ~config lines 0 (Array.length lines) init_deep_state in
    let elapsed = Unix.gettimeofday () -. start in
    
    Printf.printf "%s: %.2f ms for %d lines (%.0f lines/sec), %d cache hits\n"
      name 
      (elapsed *. 1000.0)
      lines_proc
      (float_of_int lines_proc /. elapsed)
      cache_hits
  ) configs

(* Estimate speedup from parallelization *)
let estimate_parallel_speedup num_workers =
  (* Amdahl's law: speedup = 1 / ((1-p) + p/n) *)
  (* Assume 70% of work is parallelizable *)
  let p = 0.7 in
  1.0 /. ((1.0 -. p) +. p /. float_of_int num_workers)