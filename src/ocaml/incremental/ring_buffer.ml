(* ring_buffer.ml - Memory-efficient token storage for v24-R3 *)

open Types

(** Token entry in ring buffer *)
type token_entry = {
  token : token;
  line_no : int;
  byte_offset : int;
}

(** Ring buffer implementation *)
type t = {
  buffer : token_entry array;
  capacity : int;
  mutable head : int;      (* Write position *)
  mutable tail : int;      (* Read position *)
  mutable size : int;      (* Current number of elements *)
  mutable total_evicted : int;  (* Stats: total tokens evicted *)
}

(** Create new ring buffer *)
let create capacity =
  if capacity <= 0 then
    invalid_arg "Ring buffer capacity must be positive"
  else {
    buffer = Array.make capacity 
      { token = TSpace; line_no = 0; byte_offset = 0 };
    capacity = capacity;
    head = 0;
    tail = 0;
    size = 0;
    total_evicted = 0;
  }

(** Check if buffer is empty *)
let is_empty rb = rb.size = 0

(** Check if buffer is full *)
let is_full rb = rb.size = rb.capacity

(** Advance position with wraparound *)
let advance_pos pos capacity =
  (pos + 1) mod capacity

(** Write token to buffer *)
let write rb token line_no byte_offset =
  let entry = { token; line_no; byte_offset } in
  
  if is_full rb then begin
    (* Evict oldest token *)
    rb.tail <- advance_pos rb.tail rb.capacity;
    rb.total_evicted <- rb.total_evicted + 1;
    rb.size <- rb.size - 1
  end;
  
  rb.buffer.(rb.head) <- entry;
  rb.head <- advance_pos rb.head rb.capacity;
  rb.size <- rb.size + 1

(** Read token at position (if still in buffer) *)
let read_at rb pos =
  if is_empty rb then
    None
  else
    let idx = (rb.tail + pos) mod rb.capacity in
    if pos < rb.size then
      Some rb.buffer.(idx)
    else
      None

(** Get slice of tokens between positions *)
let get_slice rb start_pos count =
  let result = ref [] in
  for i = 0 to count - 1 do
    match read_at rb (start_pos + i) with
    | Some entry -> result := entry :: !result
    | None -> ()
  done;
  List.rev !result

(** Find tokens for a line range *)
let find_line_tokens rb start_line end_line =
  let result = ref [] in
  for i = 0 to rb.size - 1 do
    match read_at rb i with
    | Some entry when entry.line_no >= start_line && 
                      entry.line_no <= end_line ->
        result := entry :: !result
    | _ -> ()
  done;
  List.rev !result

(** Find position of first token after byte offset *)
let find_position_after rb byte_offset =
  let rec search pos =
    if pos >= rb.size then
      None
    else
      match read_at rb pos with
      | Some entry when entry.byte_offset >= byte_offset -> Some pos
      | _ -> search (pos + 1)
  in
  search 0

(** Clear buffer *)
let clear rb =
  rb.head <- 0;
  rb.tail <- 0;
  rb.size <- 0

(** Get buffer statistics *)
let get_stats rb =
  let utilization = float_of_int rb.size /. float_of_int rb.capacity in
  (rb.size, rb.capacity, utilization, rb.total_evicted)

(** Integrate with document *)
let from_document doc =
  (* Estimate capacity based on document size *)
  let estimated_tokens = doc.Line_processor.total_bytes / 5 in (* ~5 bytes per token average *)
  let capacity = min (estimated_tokens * 2) 10_000_000 in (* Cap at 10M tokens *)
  
  let rb = create capacity in
  
  (* Fill buffer with all tokens *)
  let line_table = doc.Line_processor.line_table in
  for i = 0 to line_table.size - 1 do
    let info = line_table.lines.(i) in
    List.iter (fun tok ->
      write rb tok i info.li_start_pos
    ) info.li_tokens
  done;
  
  rb

(** Memory-mapped ring buffer for large documents *)
module MmapRingBuffer = struct
  type mmap_t = {
    base : t;
    filename : string;
    mutable dirty : bool;
  }
  
  (* Placeholder for mmap implementation *)
  let create_mmap filename capacity =
    {
      base = create capacity;
      filename = filename;
      dirty = false;
    }
  
  let write_mmap mrb token line_no byte_offset =
    write mrb.base token line_no byte_offset;
    mrb.dirty <- true
  
  let sync_mmap mrb =
    if mrb.dirty then begin
      (* Would sync to disk here *)
      mrb.dirty <- false
    end
end

(** Token compression for space efficiency *)
module TokenCompression = struct
  (* Encode token to compact representation *)
  let encode_token = function
    | TChar c -> 
        let code = int_of_char c in
        if code < 128 then
          [| code |]
        else
          [| 0x80; code |]
    | TCommand s ->
        let len = String.length s in
        if len < 16 then
          Array.append [| 0x90 + len |] 
            (Array.init len (fun i -> int_of_char s.[i]))
        else
          [| 0x9F; len |] (* Extended encoding *)
    | TNewline -> [| 0xA0 |]
    | TSpace -> [| 0xA1 |]
    | TMath -> [| 0xA2 |]
    | TComment s -> [| 0xA3 |] (* Simplified *)
    | TBeginEnv s -> [| 0xA4 |] (* Simplified *)
    | TEndEnv s -> [| 0xA5 |] (* Simplified *)
    | TError s -> [| 0xAF |] (* Simplified *)
  
  (* Decode would be the inverse *)
end