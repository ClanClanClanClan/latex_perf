(* PHASE 3 IMPLEMENTATION: Off-heap token storage using Structure of Arrays *)
(* This moves the 13.2MB located_tokens array off OCaml heap to achieve P99 <20ms *)

open Bigarray

(* Structure of Arrays - all token data stored off-heap *)
type tokens_soa = {
  (* All arrays have same length = n_tokens, stored off-heap *)
  kind   : (int32, int32_elt, c_layout) Array1.t;  (* Token type/catcode *)
  data   : (int32, int32_elt, c_layout) Array1.t;  (* Token data/char *)
  start_pos : (int32, int32_elt, c_layout) Array1.t;  (* Start position *)
  end_pos   : (int32, int32_elt, c_layout) Array1.t;  (* End position *)
  line   : (int32, int32_elt, c_layout) Array1.t;  (* Line number *)
  col    : (int32, int32_elt, c_layout) Array1.t;  (* Column number *)
  mutable n : int;  (* Current logical size *)
  capacity : int;   (* Maximum capacity *)
}

(* Create off-heap token storage arena *)
let make_tokens_soa ~capacity =
  let mk () = Array1.create Int32 C_layout capacity in
  { 
    kind = mk (); 
    data = mk ();
    start_pos = mk (); 
    end_pos = mk ();
    line = mk (); 
    col = mk (); 
    n = 0;
    capacity = capacity;
  }

(* Clear arena for reuse (no allocation) *)
let clear_tokens_soa t = t.n <- 0

(* High-performance token insertion *)
let[@inline always] push_token_soa t ~kind ~data ~start_pos ~end_pos ~line ~col =
  if t.n < t.capacity then (
    let i = t.n in
    Array1.unsafe_set t.kind i (Int32.of_int kind);
    Array1.unsafe_set t.data i (Int32.of_int data);
    Array1.unsafe_set t.start_pos i (Int32.of_int start_pos);
    Array1.unsafe_set t.end_pos i (Int32.of_int end_pos);
    Array1.unsafe_set t.line i (Int32.of_int line);
    Array1.unsafe_set t.col i (Int32.of_int col);
    t.n <- i + 1;
    true
  ) else (
    false  (* Arena full *)
  )

(* Safe token access *)
let get_token_soa t i =
  if i >= 0 && i < t.n then (
    let kind = Array1.unsafe_get t.kind i |> Int32.to_int in
    let data = Array1.unsafe_get t.data i |> Int32.to_int in
    let start_pos = Array1.unsafe_get t.start_pos i |> Int32.to_int in
    let end_pos = Array1.unsafe_get t.end_pos i |> Int32.to_int in
    let line = Array1.unsafe_get t.line i |> Int32.to_int in
    let col = Array1.unsafe_get t.col i |> Int32.to_int in
    Some (kind, data, start_pos, end_pos, line, col)
  ) else (
    None
  )

(* Fast unsafe access for performance-critical validators *)
let[@inline always] unsafe_get_kind t i = 
  Array1.unsafe_get t.kind i |> Int32.to_int

let[@inline always] unsafe_get_data t i = 
  Array1.unsafe_get t.data i |> Int32.to_int

let[@inline always] unsafe_get_line t i = 
  Array1.unsafe_get t.line i |> Int32.to_int

let[@inline always] unsafe_get_col t i = 
  Array1.unsafe_get t.col i |> Int32.to_int

(* Statistics type definition *)
type soa_stats = {
  total_tokens: int;
  capacity: int;
  memory_mb: float;
  utilization: float;
}

(* Memory usage calculation *)
let memory_usage_bytes (t : tokens_soa) : int =
  (* Each Array1.t uses capacity * 4 bytes (int32) *)
  (* We have 6 arrays: kind, data, start_pos, end_pos, line, col *)
  t.capacity * 4 * 6

(* Statistics *)
let get_stats (t : tokens_soa) : soa_stats = 
  let stats : soa_stats = {
    total_tokens = t.n;
    capacity = t.capacity;
    memory_mb = float_of_int (memory_usage_bytes t) /. 1_048_576.0;
    utilization = float_of_int t.n /. float_of_int t.capacity;
  } in
  stats