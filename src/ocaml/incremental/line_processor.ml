(* line_processor.ml - Line-based incremental algorithm for v24-R3 *)

open Types

(** xxHash64 binding - placeholder for real implementation *)
module XXHash = struct
  (* Simple hash for now - would use real xxHash in production *)
  let hash64 s =
    let h = ref 0L in
    String.iter (fun c ->
      h := Int64.(add (mul !h 31L) (of_int (int_of_char c)))
    ) s;
    !h
end

(** Line table for incremental processing *)
type line_table = {
  mutable lines : line_info array;
  mutable size : int;
  mutable capacity : int;
}

(** Create new line table *)
let create_line_table initial_capacity =
  {
    lines = Array.make initial_capacity 
      { li_hash = 0L; 
        li_end_state = init_state; 
        li_tokens = [];
        li_start_pos = 0;
        li_end_pos = 0 };
    size = 0;
    capacity = initial_capacity;
  }

(** Resize line table if needed *)
let ensure_capacity table needed =
  if needed > table.capacity then begin
    let new_capacity = max (table.capacity * 2) needed in
    let new_lines = Array.make new_capacity table.lines.(0) in
    Array.blit table.lines 0 new_lines 0 table.size;
    table.lines <- new_lines;
    table.capacity <- new_capacity
  end

(** Document representation *)
type document = {
  lines : string array;
  line_table : line_table;
  mutable total_bytes : int;
  stats : perf_stats;
}

(** Create new document *)
let create_document lines =
  let line_table = create_line_table (Array.length lines + 100) in
  let total_bytes = Array.fold_left (fun acc l -> acc + String.length l + 1) 0 lines in
  {
    lines = lines;
    line_table = line_table;
    total_bytes = total_bytes;
    stats = make_perf_stats ();
  }

(** Get lexer state before line n *)
let get_state_before doc line_no =
  if line_no <= 0 || doc.line_table.size = 0 then
    init_state
  else if line_no - 1 < doc.line_table.size then
    doc.line_table.lines.(line_no - 1).li_end_state
  else
    init_state

(** Find first changed line using hash comparison *)
let find_first_changed_line doc old_table new_lines =
  let rec find_changed n =
    if n >= Array.length new_lines then
      n  (* All lines processed *)
    else if n >= old_table.size then
      n  (* Beyond old table - must relex *)
    else
      let old_hash = old_table.lines.(n).li_hash in
      let new_hash = XXHash.hash64 new_lines.(n) in
      if old_hash <> new_hash then
        n  (* Found first change *)
      else
        find_changed (n + 1)
  in
  find_changed 0

(** Check if state has stabilized (no more changes needed) *)
let state_stabilized old_state new_state =
  old_state.in_math = new_state.in_math &&
  old_state.in_comment = new_state.in_comment &&
  old_state.in_verbatim = new_state.in_verbatim &&
  old_state.mode_stack = new_state.mode_stack

(** Process lines incrementally from start_line *)
let process_incremental doc start_line =
  let start_time = Unix.gettimeofday () in
  let lines_processed = ref 0 in
  let bytes_processed = ref 0 in
  
  (* Ensure capacity *)
  ensure_capacity doc.line_table (Array.length doc.lines);
  
  (* Get starting state *)
  let rec process_line line_no state =
    if line_no >= Array.length doc.lines then
      line_no
    else begin
      incr lines_processed;
      let line = doc.lines.(line_no) in
      bytes_processed := !bytes_processed + String.length line + 1;
      
      (* Lex the line *)
      let tokens, end_state = Core_lexer.lex_line state line in
      
      (* Calculate line info *)
      let start_pos = 
        if line_no = 0 then 0
        else doc.line_table.lines.(line_no - 1).li_end_pos in
      let end_pos = start_pos + String.length line + 1 in
      
      (* Update line table *)
      let line_info = {
        li_hash = XXHash.hash64 line;
        li_end_state = end_state;
        li_tokens = tokens;
        li_start_pos = start_pos;
        li_end_pos = end_pos;
      } in
      doc.line_table.lines.(line_no) <- line_info;
      
      (* Check if we can stop processing *)
      if line_no + 1 < doc.line_table.size then begin
        let old_state = doc.line_table.lines.(line_no + 1).li_end_state in
        if state_stabilized old_state end_state &&
           line_no + 1 < Array.length doc.lines &&
           XXHash.hash64 doc.lines.(line_no + 1) = 
           doc.line_table.lines.(line_no + 1).li_hash then begin
          (* State has stabilized and next line unchanged - can stop *)
          doc.stats.cache_hits <- doc.stats.cache_hits + 
            (Array.length doc.lines - line_no - 1);
          line_no + 1
        end else begin
          (* Continue processing *)
          doc.stats.cache_misses <- doc.stats.cache_misses + 1;
          process_line (line_no + 1) end_state
        end
      end else begin
        (* Continue to end *)
        doc.stats.cache_misses <- doc.stats.cache_misses + 1;
        process_line (line_no + 1) end_state
      end
    end
  in
  
  let start_state = get_state_before doc start_line in
  let end_line = process_line start_line start_state in
  
  (* Update size *)
  doc.line_table.size <- max doc.line_table.size end_line;
  
  (* Update stats *)
  let elapsed_us = int_of_float ((Unix.gettimeofday () -. start_time) *. 1_000_000.) in
  doc.stats.parse_time_us <- doc.stats.parse_time_us + elapsed_us;
  doc.stats.incremental_bytes <- doc.stats.incremental_bytes + !bytes_processed;
  doc.stats.total_bytes <- doc.total_bytes;
  
  (!lines_processed, !bytes_processed)

(** Full document relex *)
let relex_document lines =
  let doc = create_document lines in
  let _ = process_incremental doc 0 in
  doc

(** Apply edit and return affected range *)
let apply_edit doc edit =
  match edit with
  | Insert (line_no, text) ->
      if line_no >= 0 && line_no <= Array.length doc.lines then begin
        let new_lines = Array.make (Array.length doc.lines + 1) "" in
        Array.blit doc.lines 0 new_lines 0 line_no;
        new_lines.(line_no) <- text;
        Array.blit doc.lines line_no new_lines (line_no + 1) 
          (Array.length doc.lines - line_no);
        doc.lines <- new_lines;
        doc.total_bytes <- doc.total_bytes + String.length text + 1;
        line_no
      end else
        0
  | Delete (line_no, count) ->
      if line_no >= 0 && line_no + count <= Array.length doc.lines && count > 0 then begin
        let new_lines = Array.make (Array.length doc.lines - count) "" in
        Array.blit doc.lines 0 new_lines 0 line_no;
        Array.blit doc.lines (line_no + count) new_lines line_no
          (Array.length doc.lines - line_no - count);
        for i = line_no to line_no + count - 1 do
          doc.total_bytes <- doc.total_bytes - String.length doc.lines.(i) - 1
        done;
        doc.lines <- new_lines;
        line_no
      end else
        0
  | Replace (line_no, count, text) ->
      if line_no >= 0 && line_no < Array.length doc.lines then begin
        let old_len = String.length doc.lines.(line_no) in
        doc.lines.(line_no) <- text;
        doc.total_bytes <- doc.total_bytes - old_len + String.length text;
        line_no
      end else
        0

(** Get tokens for a line range *)
let get_tokens doc start_line end_line =
  let tokens = ref [] in
  for i = min start_line (doc.line_table.size - 1) downto max 0 start_line do
    if i < doc.line_table.size && i <= end_line then
      tokens := doc.line_table.lines.(i).li_tokens @ !tokens
  done;
  !tokens

(** Get all tokens *)
let get_all_tokens doc =
  get_tokens doc 0 (doc.line_table.size - 1)

(** Calculate speedup ratio *)
let calculate_speedup doc =
  if doc.stats.total_bytes = 0 then
    1.0
  else
    float_of_int doc.stats.total_bytes /. 
    float_of_int (max 1 doc.stats.incremental_bytes)