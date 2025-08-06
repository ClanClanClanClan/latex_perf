(** L0 V25 Wrapper - Adapts existing proven lexer to v25 architecture
    
    This module wraps the existing, formally verified lexer from v24
    and adds the v25 interfaces for delta processing and caching.
*)

(* Import the existing proven lexer *)
module Proven_Lexer = Lexer_extracted

(* Import performance monitoring *)
module Perf = struct
  let time_us f =
    let start = Unix.gettimeofday () in
    let result = f () in
    let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
    (result, elapsed)
end

(* Cache types from technical resolution *)
type l0_cache_key = {
  chunk_id : int;
  hash : int64;
}

(* Extended state for v25 *)
type v25_lexer_state = {
  proven_state : Proven_Lexer.lexer_state;
  chunk_id : int;
  version : int64;
  position : Types.position;
}

(* Token delta for incremental updates *)
type token_delta = {
  removed : (int * int) list;  (* start, end positions *)
  added : (int * Types.token array) list;  (* position, new tokens *)
}

(* Cache implementation - 2-hand CLOCK as specified *)
module Cache = struct
  type entry = {
    key : l0_cache_key;
    tokens : Types.token array;
    state : v25_lexer_state;
    mutable clock_bit : bool;
  }
  
  let cache = Hashtbl.create 1024  (* 1k chunks as specified *)
  let hand = ref 0
  
  let lookup key =
    try
      let entry = Hashtbl.find cache key in
      entry.clock_bit <- true;  (* Mark as recently used *)
      Some (entry.tokens, entry.state)
    with Not_found -> None
  
  let insert key tokens state =
    if Hashtbl.length cache >= 1024 then begin
      (* Eviction using 2-hand CLOCK *)
      let rec find_victim () =
        let victim_key = ref None in
        Hashtbl.iter (fun k e ->
          if not e.clock_bit then victim_key := Some k
          else e.clock_bit <- false
        ) cache;
        match !victim_key with
        | Some k -> Hashtbl.remove cache k
        | None -> find_victim ()  (* All have clock_bit set, clear and retry *)
      in
      find_victim ()
    end;
    Hashtbl.add cache key { key; tokens; state; clock_bit = true }
end

(* Main lexing function with v25 interface *)
let lex_chunk ?prev bytes =
  (* Performance tracking *)
  let start = Unix.gettimeofday () in
  
  (* Compute cache key *)
  let chunk_id = match prev with
    | None -> 0
    | Some s -> s.chunk_id + 1
  in
  
  (* Use XXH3 for hashing - stub for now, implement with FFI *)
  let hash = Int64.of_int (Hashtbl.hash bytes) in
  let cache_key = { chunk_id; hash } in
  
  (* Check cache first *)
  match Cache.lookup cache_key with
  | Some (tokens, state) ->
      (* Cache hit - validate timing *)
      let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
      if elapsed > 160. then
        Printf.eprintf "Warning: L0 exceeded hard cutoff: %.0fμs\n" elapsed;
      (tokens, state)
      
  | None ->
      (* Cache miss - use proven lexer *)
      let proven_state = match prev with
        | None -> Proven_Lexer.initial_state
        | Some s -> s.proven_state
      in
      
      (* Convert bytes to string for existing lexer *)
      let input = Bytes.to_string bytes in
      
      (* Call proven lexer *)
      let (tokens_list, new_proven_state) = 
        Proven_Lexer.lex_string_incremental proven_state input in
      
      (* Convert token list to array *)
      let tokens = Array.of_list tokens_list in
      
      (* Create v25 state *)
      let new_state = {
        proven_state = new_proven_state;
        chunk_id;
        version = Int64.succ (match prev with None -> 0L | Some s -> s.version);
        position = {
          byte_offset = Bytes.length bytes;
          line = new_proven_state.line_number;
          column = new_proven_state.column_number;
        };
      } in
      
      (* Insert into cache *)
      Cache.insert cache_key tokens new_state;
      
      (* Check performance *)
      let elapsed = (Unix.gettimeofday () -. start) *. 1_000_000. in
      if elapsed > 80. then
        Printf.eprintf "Warning: L0 exceeded p95 target: %.0fμs\n" elapsed;
      if elapsed > 160. then
        Printf.eprintf "ERROR: L0 exceeded hard cutoff: %.0fμs\n" elapsed;
        
      (tokens, new_state)

(* Compute cache key *)
let compute_cache_key bytes state =
  { chunk_id = state.chunk_id;
    hash = Int64.of_int (Hashtbl.hash bytes) }

(* Delta computation for incremental updates *)
let compute_delta old_tokens new_tokens =
  (* Simple diff algorithm - can be optimized with Myers algorithm *)
  let removed = ref [] in
  let added = ref [] in
  
  (* Find differences *)
  let old_len = Array.length old_tokens in
  let new_len = Array.length new_tokens in
  
  let i = ref 0 in
  let j = ref 0 in
  
  while !i < old_len && !j < new_len do
    if old_tokens.(!i) = new_tokens.(!j) then begin
      incr i;
      incr j
    end else begin
      (* Tokens differ - mark as removed/added *)
      removed := (!i, !i + 1) :: !removed;
      added := (!j, [|new_tokens.(!j)|]) :: !added;
      incr i;
      incr j
    end
  done;
  
  (* Handle remaining tokens *)
  while !i < old_len do
    removed := (!i, !i + 1) :: !removed;
    incr i
  done;
  
  while !j < new_len do
    added := (!j, [|new_tokens.(!j)|]) :: !added;
    incr j
  done;
  
  { removed = List.rev !removed;
    added = List.rev !added }

(* Initialize state *)
let initial_state () = {
  proven_state = Proven_Lexer.initial_state;
  chunk_id = 0;
  version = 0L;
  position = { byte_offset = 0; line = 1; column = 0 };
}

(* SIMD feature detection *)
module Simd = struct
  type path = Scalar | Avx2 | Avx512 | Neon
  
  (* Stub - will be implemented with C FFI *)
  let detect_features () =
    (* For now, always use scalar path (proven implementation) *)
    Scalar
  
  let selected = ref Scalar
  
  let selected_path () = !selected
end

(* Error handling following v25 protocol *)
type lexer_error = 
  | InvalidUtf8 of { offset : int; bytes : bytes }
  | ChunkTooLarge of { size : int; limit : int }
  | CatcodeTableCorrupted

type 'a result = ('a, [`fatal] layer_err) Stdlib.result

and _ layer_err =
  | L0_Fatal : lexer_error -> [`fatal] layer_err

(* Validate chunk size *)
let validate_chunk bytes =
  let size = Bytes.length bytes in
  if size > 4096 then
    Error (L0_Fatal (ChunkTooLarge { size; limit = 4096 }))
  else
    Ok ()

(* Main entry point with error handling *)
let lex_chunk_safe ?prev bytes =
  match validate_chunk bytes with
  | Error e -> Error e
  | Ok () ->
      try
        Ok (lex_chunk ?prev bytes)
      with
      | Invalid_argument msg when String.starts_with ~prefix:"UTF-8" msg ->
          Error (L0_Fatal (InvalidUtf8 { offset = 0; bytes }))
      | _ ->
          Error (L0_Fatal CatcodeTableCorrupted)