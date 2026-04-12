(* ══════════════════════════════════════════════════════════════════════
   Chunk_store — paragraph-level document splitting and caching

   Splits documents at paragraph boundaries (double-newline), hashes each chunk
   with XXH64, and provides snapshot diffing for incremental re-validation. Spec
   W111-120.
   ══════════════════════════════════════════════════════════════════════ *)

type chunk = { id : int64; start : int; length : int; content : string }
type snapshot = { chunks : chunk array }

type chunk_cache = {
  tbl : (int64, Validators_common.result list) Hashtbl.t;
  mutable hits : int;
  mutable misses : int;
}

(* ── Splitting ─────────────────────────────────────────────────────── *)

let min_chunk_size = 64

let hash_chunk_content (content : string) : int64 =
  (* Hash bytes + catcode vector per spec I-3: hash(bytes, catcode_vector) *)
  let n = String.length content in
  let buf = Bytes.create (n * 2) in
  Bytes.blit_string content 0 buf 0 n;
  for i = 0 to n - 1 do
    let b = Char.code content.[i] in
    let cc = Catcode.classify_ascii b in
    Bytes.set buf (n + i) (Char.chr (cc land 0xFF))
  done;
  Xxh64.hash64 buf

let split_into_chunks (src : string) : chunk array =
  let spans = Validators_common.split_into_paragraphs src in
  if spans = [] then
    if String.length src > 0 then
      [|
        {
          id = hash_chunk_content src;
          start = 0;
          length = String.length src;
          content = src;
        };
      |]
    else [||]
  else
    (* Merge tiny chunks into previous *)
    let merged = ref [] in
    List.iter
      (fun (s, len) ->
        let content = String.sub src s len in
        match !merged with
        | (prev_s, prev_len, prev_content) :: rest
          when String.length prev_content < min_chunk_size ->
            merged := (prev_s, prev_len + len, prev_content ^ content) :: rest
        | _ -> merged := (s, len, content) :: !merged)
      spans;
    let merged = List.rev !merged in
    Array.of_list
      (List.map
         (fun (s, len, content) ->
           { id = hash_chunk_content content; start = s; length = len; content })
         merged)

let create_snapshot (src : string) : snapshot =
  { chunks = split_into_chunks src }

(* ── Diffing ───────────────────────────────────────────────────────── *)

let diff_snapshots (old_snap : snapshot) (new_snap : snapshot) : int list =
  let new_len = Array.length new_snap.chunks in
  let old_len = Array.length old_snap.chunks in
  (* If chunk counts differ, mark ALL new chunks as dirty (structural change) *)
  if new_len <> old_len then List.init new_len Fun.id
  else
    let dirty = ref [] in
    for i = 0 to new_len - 1 do
      if new_snap.chunks.(i).id <> old_snap.chunks.(i).id then
        dirty := i :: !dirty
    done;
    List.rev !dirty

(* ── Cache ─────────────────────────────────────────────────────────── *)

let create_cache () : chunk_cache =
  { tbl = Hashtbl.create 128; hits = 0; misses = 0 }

let lookup_chunk (cache : chunk_cache) (id : int64) :
    Validators_common.result list option =
  match Hashtbl.find_opt cache.tbl id with
  | Some _ as r ->
      cache.hits <- cache.hits + 1;
      r
  | None ->
      cache.misses <- cache.misses + 1;
      None

let store_chunk (cache : chunk_cache) (id : int64)
    (results : Validators_common.result list) : unit =
  Hashtbl.replace cache.tbl id results

let invalidate_chunk (cache : chunk_cache) (id : int64) : unit =
  Hashtbl.remove cache.tbl id

let cache_stats (cache : chunk_cache) : string =
  let total = cache.hits + cache.misses in
  let rate =
    if total > 0 then float cache.hits /. float total *. 100.0 else 0.0
  in
  Printf.sprintf "hits=%d misses=%d rate=%.1f%% entries=%d" cache.hits
    cache.misses rate (Hashtbl.length cache.tbl)
