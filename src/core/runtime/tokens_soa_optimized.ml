(* OPTIMIZED SoA: Hot/Cold Split + Validator Fusion *)
(* Implementation of your proposed B+C optimizations *)

open Bigarray

(* Hot path: Only essential data for validation *)
type hot_soa = {
  kind : (int32, int32_elt, c_layout) Array1.t;  (* Token type/catcode *)
  data : (int32, int32_elt, c_layout) Array1.t;  (* Token data/char *)
  mutable n : int;
  capacity : int;
}

(* Cold path: Full location data (allocated lazily) *)
type cold_soa = {
  start_pos : (int32, int32_elt, c_layout) Array1.t;
  end_pos   : (int32, int32_elt, c_layout) Array1.t;
  line      : (int32, int32_elt, c_layout) Array1.t;
  col       : (int32, int32_elt, c_layout) Array1.t;
}

type split_tokens_soa = {
  hot : hot_soa;
  cold : cold_soa option ref;  (* Lazy allocation *)
}

(* Create hot-path arena only *)
let make_hot_soa ~capacity = {
  kind = Array1.create Int32 C_layout capacity;
  data = Array1.create Int32 C_layout capacity;
  n = 0;
  capacity = capacity;
}

(* Lazy cold path allocation *)
let ensure_cold_soa soa =
  match !(soa.cold) with
  | Some cold -> cold
  | None ->
      let cold = {
        start_pos = Array1.create Int32 C_layout soa.hot.capacity;
        end_pos = Array1.create Int32 C_layout soa.hot.capacity;
        line = Array1.create Int32 C_layout soa.hot.capacity;
        col = Array1.create Int32 C_layout soa.hot.capacity;
      } in
      soa.cold := Some cold;
      cold

let make_split_tokens_soa ~capacity = {
  hot = make_hot_soa ~capacity;
  cold = ref None;
}

(* Fast hot-path token insertion *)
let[@inline always] push_token_hot hot ~kind ~data =
  if hot.n < hot.capacity then (
    let i = hot.n in
    Array1.unsafe_set hot.kind i (Int32.of_int kind);
    Array1.unsafe_set hot.data i (Int32.of_int data);
    hot.n <- i + 1;
    true
  ) else false

(* Full token insertion with cold data *)
let push_token_split soa ~kind ~data ~start_pos ~end_pos ~line ~col =
  if push_token_hot soa.hot ~kind ~data then (
    let cold = ensure_cold_soa soa in
    let i = soa.hot.n - 1 in
    Array1.unsafe_set cold.start_pos i (Int32.of_int start_pos);
    Array1.unsafe_set cold.end_pos i (Int32.of_int end_pos);
    Array1.unsafe_set cold.line i (Int32.of_int line);
    Array1.unsafe_set cold.col i (Int32.of_int col);
    true
  ) else false

(* Ultra-fast validation access (hot path only) *)
let[@inline always] unsafe_get_kind_hot hot i = 
  Array1.unsafe_get hot.kind i |> Int32.to_int

let[@inline always] unsafe_get_data_hot hot i = 
  Array1.unsafe_get hot.data i |> Int32.to_int

(* Issues pool for zero-allocation validation *)
type issue_pool = {
  rule_ids : bytes array;
  positions : int array;
  messages : bytes array;
  mutable count : int;
  capacity : int;
}

let make_issue_pool ~capacity = {
  rule_ids = Array.make capacity (Bytes.create 16);
  positions = Array.make capacity 0;
  messages = Array.make capacity (Bytes.create 64);
  count = 0;
  capacity = capacity;
}

let clear_issue_pool pool = pool.count <- 0

let[@inline always] add_issue_hot pool ~rule_id ~position ~message =
  if pool.count < pool.capacity then (
    let i = pool.count in
    let rid_bytes = pool.rule_ids.(i) in
    let msg_bytes = pool.messages.(i) in
    Bytes.blit_string rule_id 0 rid_bytes 0 (min (String.length rule_id) 15);
    Bytes.blit_string message 0 msg_bytes 0 (min (String.length message) 63);
    pool.positions.(i) <- position;
    pool.count <- i + 1;
    true
  ) else false

(* Fused L0→SoA+Validation Fill *)
let fill_and_validate_fused soa pool tokens =
  clear_issue_pool pool;
  soa.hot.n <- 0;
  
  let len = Array.length tokens in
  for i = 0 to len - 1 do
    let packed = tokens.(i) in
    let catcode = Int32.to_int (Int32.logand packed 0x3Fl) in
    let data = Int32.to_int (Int32.shift_right_logical packed 6) in
    
    (* Fill hot SoA *)
    if push_token_hot soa.hot ~kind:catcode ~data then (
      (* Inline validation during fill *)
      
      (* TYPO-001: ASCII quotes *)
      if catcode = 12 && data = 34 then
        ignore (add_issue_hot pool ~rule_id:"TYPO-001" ~position:i ~message:"ASCII quote");
      
      (* TYPO-002: Double hyphens (look ahead) *)
      if catcode = 12 && data = 45 && i < len - 1 then (
        let next_packed = tokens.(i + 1) in
        let next_catcode = Int32.to_int (Int32.logand next_packed 0x3Fl) in
        let next_data = Int32.to_int (Int32.shift_right_logical next_packed 6) in
        if next_catcode = 12 && next_data = 45 then
          ignore (add_issue_hot pool ~rule_id:"TYPO-002" ~position:i ~message:"Double hyphen")
      );
      
      (* TYPO-006: Tabs *)
      if catcode = 12 && data = 9 then
        ignore (add_issue_hot pool ~rule_id:"TYPO-006" ~position:i ~message:"Tab character");
      
    )
  done

(* Memory usage (hot path only) *)
let hot_memory_usage_bytes hot =
  hot.capacity * 4 * 2  (* 2 arrays: kind, data *)

(* Stats *)
type split_soa_stats = {
  hot_tokens: int;
  hot_capacity: int;
  hot_memory_mb: float;
  cold_allocated: bool;
  cold_memory_mb: float;
  total_memory_mb: float;
}

let get_split_stats soa = {
  hot_tokens = soa.hot.n;
  hot_capacity = soa.hot.capacity;
  hot_memory_mb = float_of_int (hot_memory_usage_bytes soa.hot) /. 1_048_576.0;
  cold_allocated = !(soa.cold) <> None;
  cold_memory_mb = if !(soa.cold) <> None then 
    float_of_int (soa.hot.capacity * 4 * 4) /. 1_048_576.0 else 0.0;
  total_memory_mb = float_of_int (
    (hot_memory_usage_bytes soa.hot) + 
    (if !(soa.cold) <> None then soa.hot.capacity * 4 * 4 else 0)
  ) /. 1_048_576.0;
}