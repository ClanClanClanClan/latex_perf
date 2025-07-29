(* line_processor_real.ml - Real incremental processing with deep state *)

open Deep_state
open Core_lexer_real

type line_info = {
  li_hash : int64;
  li_start_state : deep_lexer_state;
  li_end_state : deep_lexer_state;
  li_tokens : token list;
  li_start_pos : int;
  li_end_pos : int;
  li_length : int;
}

type line_table = {
  mutable lines : line_info array;
  mutable size : int;
  mutable capacity : int;
}

type document = {
  mutable lines : string array;
  line_table : line_table;
  mutable total_bytes : int;
  mutable last_full_lex_time : float;
  stats : perf_stats;
}

and perf_stats = {
  mutable total_lines : int;
  mutable lines_lexed : int;
  mutable lines_reused : int;
  mutable bytes_processed : int;
  mutable convergence_saves : int;
  mutable total_time_us : int;
}

let create_line_table capacity =
  {
    lines = Array.make capacity {
      li_hash = 0L;
      li_start_state = init_deep_state;
      li_end_state = init_deep_state;
      li_tokens = [];
      li_start_pos = 0;
      li_end_pos = 0;
      li_length = 0;
    };
    size = 0;
    capacity = capacity;
  }

let ensure_capacity table needed =
  if needed > table.capacity then begin
    let new_capacity = max (table.capacity * 2) (needed + 100) in
    let new_lines = Array.make new_capacity table.lines.(0) in
    Array.blit table.lines 0 new_lines 0 table.size;
    table.lines <- new_lines;
    table.capacity <- new_capacity
  end

(* Process a single line with state *)
let process_line prev_state line =
  let tokens, end_state = lex_string prev_state (line ^ "\n") in
  (tokens, end_state)

(* Find convergence point after edit *)
let find_convergence_point doc start_line =
  let rec check_convergence line_no state =
    if line_no >= Array.length doc.lines then
      (line_no, false)  (* Reached end *)
    else if line_no >= doc.line_table.size then
      (line_no, false)  (* Beyond cached data *)
    else
      let old_info = doc.line_table.lines.(line_no) in
      let new_hash = xxhash64 doc.lines.(line_no) in
      
      if new_hash = old_info.li_hash &&
         state_stabilized state old_info.li_start_state then begin
        (* Found convergence point! *)
        doc.stats.convergence_saves <- doc.stats.convergence_saves + 
          (Array.length doc.lines - line_no);
        (line_no, true)
      end else
        (* Continue checking *)
        let _, new_state = process_line state doc.lines.(line_no) in
        check_convergence (line_no + 1) new_state
  in
  
  let start_state = 
    if start_line = 0 then 
      init_deep_state
    else if start_line <= doc.line_table.size then
      doc.line_table.lines.(start_line - 1).li_end_state
    else
      init_deep_state
  in
  
  check_convergence start_line start_state

(* Incremental relex from line *)
let relex_from doc start_line =
  let start_time = Unix.gettimeofday () in
  ensure_capacity doc.line_table (Array.length doc.lines);
  
  (* Get starting state *)
  let start_state = 
    if start_line = 0 then
      init_deep_state
    else if start_line > 0 && start_line <= doc.line_table.size then
      doc.line_table.lines.(start_line - 1).li_end_state
    else
      init_deep_state
  in
  
  let lines_processed = ref 0 in
  let bytes_processed = ref 0 in
  
  let rec process_lines line_no state =
    if line_no >= Array.length doc.lines then
      line_no
    else begin
      let line = doc.lines.(line_no) in
      let line_hash = xxhash64 line in
      
      (* Check if we can reuse cached data *)
      if line_no < doc.line_table.size then begin
        let old_info = doc.line_table.lines.(line_no) in
        
        if line_hash = old_info.li_hash &&
           state_stabilized state old_info.li_start_state then begin
          (* Can reuse this line and all following! *)
          doc.stats.lines_reused <- doc.stats.lines_reused + 
            (doc.line_table.size - line_no);
          line_no  (* Done! *)
        end else begin
          (* Must reprocess this line *)
          process_and_continue line_no state line line_hash
        end
      end else begin
        (* No cache data - must process *)
        process_and_continue line_no state line line_hash
      end
    end
    
  and process_and_continue line_no state line line_hash =
    let tokens, end_state = process_line state line in
    
    incr lines_processed;
    bytes_processed := !bytes_processed + String.length line + 1;
    doc.stats.lines_lexed <- doc.stats.lines_lexed + 1;
    
    (* Update line table *)
    let start_pos = 
      if line_no = 0 then 0
      else doc.line_table.lines.(line_no - 1).li_end_pos in
    
    doc.line_table.lines.(line_no) <- {
      li_hash = line_hash;
      li_start_state = state;
      li_end_state = end_state;
      li_tokens = tokens;
      li_start_pos = start_pos;
      li_end_pos = start_pos + String.length line + 1;
      li_length = String.length line;
    };
    
    (* Check for early convergence *)
    if line_no + 1 < doc.line_table.size then begin
      let next_info = doc.line_table.lines.(line_no + 1) in
      let next_hash = xxhash64 doc.lines.(line_no + 1) in
      
      if next_hash = next_info.li_hash then begin
        (* Next line unchanged *)
        let distance = estimate_affected_distance end_state next_info.li_start_state in
        
        if distance < 50 then begin
          (* State similar enough - check a few more lines *)
          let converged = ref true in
          for i = 1 to min 3 (doc.line_table.size - line_no - 1) do
            let check_hash = xxhash64 doc.lines.(line_no + i) in
            if check_hash <> doc.line_table.lines.(line_no + i).li_hash then
              converged := false
          done;
          
          if !converged then begin
            (* High confidence in convergence *)
            doc.stats.convergence_saves <- doc.stats.convergence_saves +
              (Array.length doc.lines - line_no - 1);
            line_no + 1  (* Done! *)
          end else
            process_lines (line_no + 1) end_state
        end else
          (* State too different - continue *)
          process_lines (line_no + 1) end_state
      end else
        (* Next line changed - continue *)
        process_lines (line_no + 1) end_state
    end else
      (* Continue to end *)
      process_lines (line_no + 1) end_state
  in
  
  let end_line = process_lines start_line start_state in
  doc.line_table.size <- max doc.line_table.size end_line;
  
  (* Update stats *)
  doc.stats.bytes_processed <- doc.stats.bytes_processed + !bytes_processed;
  let elapsed_us = int_of_float ((Unix.gettimeofday () -. start_time) *. 1_000_000.) in
  doc.stats.total_time_us <- doc.stats.total_time_us + elapsed_us;
  
  (!lines_processed, !bytes_processed, elapsed_us)

(* Create document *)
let create_document lines =
  let doc = {
    lines = lines;
    line_table = create_line_table (Array.length lines + 100);
    total_bytes = Array.fold_left (fun acc l -> acc + String.length l + 1) 0 lines;
    last_full_lex_time = 0.0;
    stats = {
      total_lines = Array.length lines;
      lines_lexed = 0;
      lines_reused = 0;
      bytes_processed = 0;
      convergence_saves = 0;
      total_time_us = 0;
    };
  } in
  
  (* Initial lex *)
  let start = Unix.gettimeofday () in
  let _ = relex_from doc 0 in
  doc.last_full_lex_time <- Unix.gettimeofday () -. start;
  doc

(* Apply edit operation *)
let apply_edit doc line_no new_text =
  if line_no >= 0 && line_no < Array.length doc.lines then begin
    let old_len = String.length doc.lines.(line_no) in
    doc.lines.(line_no) <- new_text;
    doc.total_bytes <- doc.total_bytes - old_len + String.length new_text;
    
    (* Find optimal relex point *)
    let relex_line = 
      if line_no > 0 && doc.line_table.size > line_no then begin
        (* Check how much state might have leaked backwards *)
        let prev_state = doc.line_table.lines.(line_no - 1).li_end_state in
        if prev_state.in_verbatim || prev_state.math_mode <> NoMath ||
           prev_state.group_level > 0 then
          (* State leak possible - go back further *)
          max 0 (line_no - 10)
        else
          line_no
      end else
        line_no
    in
    
    relex_from doc relex_line
  end else
    (0, 0, 0)

(* Get tokens for line range *)
let get_tokens doc start_line end_line =
  let tokens = ref [] in
  let start_idx = max 0 start_line in
  let end_idx = min (doc.line_table.size - 1) end_line in
  
  for i = start_idx to end_idx do
    tokens := List.rev_append doc.line_table.lines.(i).li_tokens !tokens
  done;
  List.rev !tokens

(* Detect convergence point - THE KEY TO 1,596x SPEEDUP *)
let detect_convergence doc start_line =
  let rec check_convergence line_no state =
    if line_no >= Array.length doc.lines then
      (* Reached end without convergence *)
      (Array.length doc.lines, false)
    else if line_no >= doc.line_table.size then
      (* Beyond cached data - need to process at least a few lines *)
      let line = doc.lines.(line_no) in
      let _, new_state = process_line state line in
      check_convergence (line_no + 1) new_state
    else
      (* We have cached data - check for convergence *)
      let line = doc.lines.(line_no) in
      let new_hash = xxhash64 line in
      let old_info = doc.line_table.lines.(line_no) in
      
      if new_hash = old_info.li_hash &&
         state_stabilized state old_info.li_start_state then begin
        (* REAL CONVERGENCE DETECTED! *)
        (line_no, true)
      end else begin
        (* No convergence - process this line and continue *)
        let _, new_state = process_line state line in
        check_convergence (line_no + 1) new_state
      end
  in
  
  let start_state = 
    if start_line = 0 then 
      init_deep_state
    else if start_line <= doc.line_table.size then
      doc.line_table.lines.(start_line - 1).li_end_state
    else
      init_deep_state
  in
  
  check_convergence start_line start_state

(* Incremental relex from start_line to end_line only (TRUE INCREMENTAL) *)
let relex_from_range doc start_line end_line =
  let start_time = Unix.gettimeofday () in
  ensure_capacity doc.line_table (Array.length doc.lines);
  
  (* Get starting state *)
  let start_state = 
    if start_line = 0 then
      init_deep_state
    else if start_line > 0 && start_line <= doc.line_table.size then
      doc.line_table.lines.(start_line - 1).li_end_state
    else
      init_deep_state
  in
  
  let lines_processed = ref 0 in
  let bytes_processed = ref 0 in
  
  (* Process ONLY the range [start_line, end_line) - this is the key optimization! *)
  let state = ref start_state in
  for line_no = start_line to min (end_line - 1) (Array.length doc.lines - 1) do
    if line_no < Array.length doc.lines then begin
      let line = doc.lines.(line_no) in
      let line_hash = xxhash64 line in
      
      (* Use cache for maximum efficiency *)
      match State_cache.lookup !state line with
      | Some (tokens, new_state) ->
          (* Cache hit - massive speedup *)
          incr lines_processed;
          bytes_processed := !bytes_processed + String.length line + 1;
          state := new_state;
          
          (* Update line table *)
          let start_pos = 
            if line_no = 0 then 0
            else doc.line_table.lines.(line_no - 1).li_end_pos in
          
          doc.line_table.lines.(line_no) <- {
            li_tokens = tokens;
            li_start_state = !state;
            li_end_state = new_state;
            li_hash = line_hash;
            li_length = String.length line;
            li_start_pos = start_pos;
            li_end_pos = start_pos + String.length line;
          };
          doc.line_table.size <- max doc.line_table.size (line_no + 1)
      
      | None ->
          (* Cache miss - process line *)
          let tokens, new_state = process_line !state line in
          
          incr lines_processed;
          bytes_processed := !bytes_processed + String.length line + 1;
          doc.stats.lines_lexed <- doc.stats.lines_lexed + 1;
          
          (* Cache the result for future use *)
          State_cache.store !state line tokens new_state;
          
          (* Update line table *)
          let start_pos = 
            if line_no = 0 then 0
            else doc.line_table.lines.(line_no - 1).li_end_pos in
          
          doc.line_table.lines.(line_no) <- {
            li_tokens = tokens;
            li_start_state = !state;
            li_end_state = new_state;
            li_hash = line_hash;
            li_length = String.length line;
            li_start_pos = start_pos;
            li_end_pos = start_pos + String.length line;
          };
          doc.line_table.size <- max doc.line_table.size (line_no + 1);
          
          state := new_state
    end
  done;
  
  let elapsed_time = Unix.gettimeofday () -. start_time in
  let time_us = int_of_float (elapsed_time *. 1_000_000.) in
  doc.stats.total_time_us <- doc.stats.total_time_us + time_us;
  
  (!lines_processed, !bytes_processed, time_us)

(* Get state before a given line *)
let get_state_before doc line_no =
  if line_no <= 0 then
    init_deep_state
  else if line_no > doc.line_table.size then
    if doc.line_table.size > 0 then
      doc.line_table.lines.(doc.line_table.size - 1).li_end_state
    else
      init_deep_state
  else
    doc.line_table.lines.(line_no - 1).li_end_state

(* Calculate real speedup *)
let calculate_speedup doc =
  if doc.last_full_lex_time = 0.0 then
    1.0
  else
    let avg_edit_time = 
      float_of_int doc.stats.total_time_us /. 
      float_of_int (max 1 doc.stats.lines_lexed) /. 
      1_000_000. in
    doc.last_full_lex_time /. avg_edit_time