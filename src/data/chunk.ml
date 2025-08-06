(* Chunk Module - Week 3-6 Foundation *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.1 *)

(** Chunk type for incremental processing *)
type t = {
  id       : int;        (* monotonic identifier *)
  bytes    : bytes;      (* raw UTF-8 content *)
  start_ofs: int;        (* global offset in document *)
  prev_hash: int64;      (* xxHash64 for chain integrity - stub for now *)
}

(** Create a chunk *)
let create ~id ~bytes ~start_ofs ~prev_hash =
  { id; bytes; start_ofs; prev_hash }

(** Create initial chunk *)
let create_initial bytes =
  { id = 0; bytes; start_ofs = 0; prev_hash = 0L }

(** Get chunk size *)
let size chunk = Bytes.length chunk.bytes

(** Get chunk content as string *)
let to_string chunk = Bytes.to_string chunk.bytes

(** Split a large input into chunks of given size *)
let split_into_chunks ?(chunk_size=4096) input =
  let len = String.length input in
  let rec split_aux offset id acc =
    if offset >= len then
      List.rev acc
    else
      let remaining = len - offset in
      let this_chunk_size = min chunk_size remaining in
      let bytes = Bytes.create this_chunk_size in
      String.blit input offset bytes 0 this_chunk_size;
      (* For now, prev_hash is just a placeholder - Week 7-9 will implement xxHash *)
      let prev_hash = match acc with
        | [] -> 0L
        | hd :: _ -> Int64.of_int (hd.id + 1000)  (* Placeholder *)
      in
      let chunk = create ~id ~bytes ~start_ofs:offset ~prev_hash in
      split_aux (offset + this_chunk_size) (id + 1) (chunk :: acc)
  in
  split_aux 0 0 []

(** Check if offset falls within chunk *)
let contains_offset chunk offset =
  offset >= chunk.start_ofs && 
  offset < chunk.start_ofs + Bytes.length chunk.bytes

(** Get character at document offset if within chunk *)
let get_char_at chunk doc_offset =
  if contains_offset chunk doc_offset then
    let local_offset = doc_offset - chunk.start_ofs in
    Some (Bytes.get chunk.bytes local_offset)
  else
    None

(** Find chunk boundary for given offset *)
let find_chunk_boundary chunks offset =
  List.find_opt (fun chunk -> contains_offset chunk offset) chunks

(** Pretty print chunk info *)
let pp fmt chunk =
  Format.fprintf fmt "Chunk{id=%d, start=%d, size=%d, hash=%Ld}"
    chunk.id chunk.start_ofs (size chunk) chunk.prev_hash