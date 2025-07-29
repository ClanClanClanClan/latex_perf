(* checkpoint_manager.ml - Checkpoint creation and management for v24-R3 *)

open Types

(** Checkpoint interval configuration *)
type checkpoint_config = {
  interval_bytes : int;     (* Create checkpoint every N bytes *)
  interval_lines : int;     (* Create checkpoint every N lines *)
  max_checkpoints : int;    (* Maximum number of checkpoints to keep *)
  min_distance : int;       (* Minimum byte distance between checkpoints *)
}

(** Default configuration - checkpoint every 1000 bytes or 50 lines *)
let default_config = {
  interval_bytes = 1000;
  interval_lines = 50;
  max_checkpoints = 1000;
  min_distance = 500;
}

(** Checkpoint manager *)
type t = {
  checkpoints : checkpoint array;
  mutable size : int;
  config : checkpoint_config;
  mutable last_checkpoint_pos : int;
}

(** Create new checkpoint manager *)
let create ?(config=default_config) () =
  {
    checkpoints = Array.make config.max_checkpoints 
      { cp_offset = 0; cp_state = init_state; cp_line_no = 0 };
    size = 0;
    config = config;
    last_checkpoint_pos = -config.min_distance;
  }

(** Binary search for checkpoint *)
let find_checkpoint_before mgr offset =
  if mgr.size = 0 then
    None
  else
    let rec binary_search low high =
      if low > high then
        if high >= 0 then
          Some mgr.checkpoints.(high)
        else
          None
      else
        let mid = (low + high) / 2 in
        let cp = mgr.checkpoints.(mid) in
        if cp.cp_offset = offset then
          Some cp
        else if cp.cp_offset < offset then
          binary_search (mid + 1) high
        else
          binary_search low (mid - 1)
    in
    binary_search 0 (mgr.size - 1)

(** Add checkpoint if conditions are met *)
let maybe_add_checkpoint mgr offset state line_no =
  let should_checkpoint =
    offset - mgr.last_checkpoint_pos >= mgr.config.min_distance &&
    (offset - mgr.last_checkpoint_pos >= mgr.config.interval_bytes ||
     (mgr.size > 0 && 
      line_no - mgr.checkpoints.(mgr.size - 1).cp_line_no >= mgr.config.interval_lines))
  in
  
  if should_checkpoint && mgr.size < mgr.config.max_checkpoints then begin
    mgr.checkpoints.(mgr.size) <- {
      cp_offset = offset;
      cp_state = state;
      cp_line_no = line_no;
    };
    mgr.size <- mgr.size + 1;
    mgr.last_checkpoint_pos <- offset;
    true
  end else
    false

(** Clear all checkpoints *)
let clear mgr =
  mgr.size <- 0;
  mgr.last_checkpoint_pos <- -mgr.config.min_distance

(** Get checkpoint statistics *)
let get_stats mgr =
  if mgr.size = 0 then
    (0, 0, 0)
  else
    let total_distance = ref 0 in
    let max_distance = ref 0 in
    for i = 1 to mgr.size - 1 do
      let dist = mgr.checkpoints.(i).cp_offset - mgr.checkpoints.(i-1).cp_offset in
      total_distance := !total_distance + dist;
      max_distance := max !max_distance dist
    done;
    (mgr.size, !total_distance / max 1 (mgr.size - 1), !max_distance)

(** Integrate with line processor *)
let create_checkpoints_from_doc doc =
  let mgr = create () in
  let line_table = doc.Line_processor.line_table in
  
  for i = 0 to line_table.size - 1 do
    let info = line_table.lines.(i) in
    let _ = maybe_add_checkpoint mgr info.li_end_pos info.li_end_state i in
    ()
  done;
  mgr

(** Find recovery point for edit *)
let find_recovery_point mgr edit_offset =
  match find_checkpoint_before mgr edit_offset with
  | Some cp -> (cp.cp_line_no, cp.cp_state)
  | None -> (0, init_state)

(** Serialize checkpoints to binary *)
let serialize mgr =
  let buf = Buffer.create (mgr.size * 100) in
  (* Write header: version and count *)
  Buffer.add_char buf '\001';  (* Version 1 *)
  Buffer.add_string buf (State_codec.VLQ.encode_int mgr.size);
  
  (* Write each checkpoint *)
  for i = 0 to mgr.size - 1 do
    let cp = mgr.checkpoints.(i) in
    Buffer.add_string buf (State_codec.VLQ.encode_int cp.cp_offset);
    Buffer.add_string buf (State_codec.VLQ.encode_int cp.cp_line_no);
    Buffer.add_string buf (State_codec.encode_state cp.cp_state);
  done;
  
  Buffer.contents buf

(** Deserialize checkpoints from binary *)
let deserialize data =
  try
    if String.length data = 0 then None
    else if data.[0] <> '\001' then None  (* Wrong version *)
    else
      let pos = ref 1 in
      let size, new_pos = State_codec.VLQ.decode_int data !pos in
      pos := new_pos;
      
      let mgr = create () in
      mgr.size <- min size mgr.config.max_checkpoints;
      
      for i = 0 to mgr.size - 1 do
        let offset, new_pos = State_codec.VLQ.decode_int data !pos in
        pos := new_pos;
        let line_no, new_pos = State_codec.VLQ.decode_int data !pos in
        pos := new_pos;
        
        (* Find end of state encoding *)
        let state_start = !pos in
        let rec find_state_end p =
          if p >= String.length data then p
          else
            match State_codec.decode_state (String.sub data state_start (p - state_start + 1)) with
            | Some _ -> p + 1
            | None -> find_state_end (p + 1)
        in
        let state_end = find_state_end state_start in
        
        match State_codec.decode_state (String.sub data state_start (state_end - state_start)) with
        | Some state ->
            mgr.checkpoints.(i) <- {
              cp_offset = offset;
              cp_state = state;
              cp_line_no = line_no;
            };
            pos := state_end
        | None -> raise Exit
      done;
      
      if mgr.size > 0 then
        mgr.last_checkpoint_pos <- mgr.checkpoints.(mgr.size - 1).cp_offset;
      
      Some mgr
  with _ -> None