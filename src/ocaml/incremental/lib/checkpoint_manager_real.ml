(* checkpoint_manager_real.ml - Optimized checkpoint manager *)

open Deep_state

type checkpoint = {
  cp_offset : int;
  cp_line_no : int;
  cp_state : deep_lexer_state;
  cp_state_hash : int64;
}

type t = {
  mutable checkpoints : checkpoint array;
  mutable size : int;
  capacity : int;
  interval_bytes : int;
  interval_lines : int;
}

let create ?(interval_bytes=1000) ?(interval_lines=50) () =
  {
    checkpoints = Array.make 10000 {
      cp_offset = 0;
      cp_line_no = 0;
      cp_state = init_deep_state;
      cp_state_hash = 0L;
    };
    size = 0;
    capacity = 10000;
    interval_bytes = interval_bytes;
    interval_lines = interval_lines;
  }

let find_recovery_point mgr byte_offset =
  (* Binary search for the LATEST checkpoint STRICTLY BEFORE the edit offset *)
  let rec binary_search low high best_idx =
    if low > high then
      match best_idx with
      | Some idx -> (mgr.checkpoints.(idx).cp_line_no, mgr.checkpoints.(idx).cp_state)
      | None -> (0, init_deep_state)
    else
      let mid = (low + high) / 2 in
      let cp = mgr.checkpoints.(mid) in
      if cp.cp_offset < byte_offset then
        (* This checkpoint is before the edit - it's a candidate *)
        binary_search (mid + 1) high (Some mid)
      else
        (* This checkpoint is at or after the edit - look earlier *)
        binary_search low (mid - 1) best_idx
  in
  
  if mgr.size = 0 then
    (0, init_deep_state)
  else
    binary_search 0 (mgr.size - 1) None

let add_checkpoint mgr offset line_no state =
  if mgr.size < mgr.capacity then begin
    mgr.checkpoints.(mgr.size) <- {
      cp_offset = offset;
      cp_line_no = line_no;
      cp_state = state;
      cp_state_hash = hash_deep_state state;
    };
    mgr.size <- mgr.size + 1
  end

let should_checkpoint mgr offset line_no =
  if mgr.size = 0 then
    true
  else
    let last = mgr.checkpoints.(mgr.size - 1) in
    offset - last.cp_offset >= mgr.interval_bytes ||
    line_no - last.cp_line_no >= mgr.interval_lines

let create_checkpoints_from_doc mgr doc =
  mgr.size <- 0;
  
  let line_table = doc.Line_processor_real.line_table in
  let offset = ref 0 in
  
  for i = 0 to line_table.size - 1 do
    let info = line_table.lines.(i) in
    
    if should_checkpoint mgr !offset i then
      add_checkpoint mgr !offset i info.li_end_state;
    
    offset := !offset + info.li_length + 1
  done

let update_checkpoints_incremental mgr doc start_line =
  (* Find checkpoint index to start updating from *)
  let start_idx = ref 0 in
  while !start_idx < mgr.size && 
        mgr.checkpoints.(!start_idx).cp_line_no < start_line do
    incr start_idx
  done;
  
  (* Truncate checkpoints after start point *)
  mgr.size <- !start_idx;
  
  (* Rebuild checkpoints from start_line *)
  let line_table = doc.Line_processor_real.line_table in
  let offset = ref (if !start_idx > 0 then 
                     mgr.checkpoints.(!start_idx - 1).cp_offset 
                   else 0) in
  
  for i = start_line to line_table.size - 1 do
    let info = line_table.lines.(i) in
    
    if should_checkpoint mgr !offset i then
      add_checkpoint mgr !offset i info.li_end_state;
    
    offset := !offset + info.li_length + 1
  done

(* Convert line number to byte offset using document *)
let line_to_byte_offset doc line_no =
  if line_no <= 0 then
    0
  else if line_no > Array.length doc.Line_processor_real.lines then
    (* Return total document size *)
    doc.Line_processor_real.total_bytes
  else begin
    let offset = ref 0 in
    for i = 0 to min (line_no - 1) (Array.length doc.Line_processor_real.lines - 1) do
      offset := !offset + String.length doc.Line_processor_real.lines.(i) + 1
    done;
    !offset
  end

(* Find recovery point by line number (main interface) *)
let find_recovery_point_by_line mgr doc line_no =
  let byte_offset = line_to_byte_offset doc line_no in
  find_recovery_point mgr byte_offset

let get_stats mgr =
  if mgr.size = 0 then
    (0, 0, 0.0)
  else
    let total_interval = ref 0 in
    let max_interval = ref 0 in
    
    for i = 1 to mgr.size - 1 do
      let interval = mgr.checkpoints.(i).cp_offset - 
                     mgr.checkpoints.(i-1).cp_offset in
      total_interval := !total_interval + interval;
      max_interval := max !max_interval interval
    done;
    
    let avg_interval = !total_interval / max 1 (mgr.size - 1) in
    let coverage = float_of_int mgr.checkpoints.(mgr.size - 1).cp_offset in
    
    (mgr.size, avg_interval, coverage)