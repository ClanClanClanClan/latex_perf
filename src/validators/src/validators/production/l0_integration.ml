(* L0 INTEGRATION HELPERS - For seamless integration with lexer_v25.ml *)

open Validator_types

(* Create interest mask array for L0 to populate *)
let create_interest_mask n_tokens =
  Array1.create int8_unsigned c_layout n_tokens

(* Function for L0 to call during tokenization *)
let[@inline always] write_interest_mask interest_mask token_index ~token_kind ~ascii_code =
  let is_ascii_char = (token_kind = 12) in  (* KIND_OTHER from lexer_v25.ml *)
  let mask = compute_interest_mask ~is_ascii_char ~ascii_code in
  Array1.unsafe_set interest_mask token_index mask

(* Alternative batch interface for performance *)
let write_interest_batch interest_mask token_data start_index count =
  for i = 0 to count - 1 do
    let token_index = start_index + i in
    let (kind, ascii) = token_data.(i) in
    let is_ascii_char = (kind = 12) in
    let mask = compute_interest_mask ~is_ascii_char ~ascii_code:ascii in
    Array1.unsafe_set interest_mask token_index mask
  done

(* Complete integration interface for L0 *)
module L0_Interface = struct
  type integration_state = {
    interest_mask: interest_mask;
    mutable current_index: int;
  }
  
  let create_integration_state capacity = {
    interest_mask = create_interest_mask capacity;
    current_index = 0;
  }
  
  let[@inline always] add_token state ~token_kind ~ascii_code =
    let is_ascii_char = (token_kind = 12) in
    let mask = compute_interest_mask ~is_ascii_char ~ascii_code in
    Array1.unsafe_set state.interest_mask state.current_index mask;
    state.current_index <- state.current_index + 1
  
  let finalize_and_validate state =
    let n_tokens = state.current_index in
    let issues = Single_pass_validator.validate state.interest_mask n_tokens in
    (issues, n_tokens)
  
  let finalize_with_timing state =
    let n_tokens = state.current_index in
    Single_pass_validator.validate_with_timing state.interest_mask n_tokens
end

(* Validation convenience functions *)
let validate_tokens token_array =
  let n = Array.length token_array in
  let interest_mask = create_interest_mask n in
  
  (* Build interest mask from token array *)
  Array.iteri (fun i (kind, ascii) ->
    let is_ascii_char = (kind = 12) in
    let mask = compute_interest_mask ~is_ascii_char ~ascii_code:ascii in
    Array1.unsafe_set interest_mask i mask
  ) token_array;
  
  (* Validate *)
  Single_pass_validator.validate interest_mask n

(* Performance testing helper *)
let benchmark_validation token_array iterations =
  let n = Array.length token_array in
  let interest_mask = create_interest_mask n in
  
  (* Build interest mask once *)
  Array.iteri (fun i (kind, ascii) ->
    let is_ascii_char = (kind = 12) in
    let mask = compute_interest_mask ~is_ascii_char ~ascii_code:ascii in
    Array1.unsafe_set interest_mask i mask
  ) token_array;
  
  (* Warm up *)
  for _ = 1 to 10 do
    ignore (Single_pass_validator.validate interest_mask n)
  done;
  
  (* Benchmark *)
  let times = ref [] in
  for _ = 1 to iterations do
    let (_, stats) = Single_pass_validator.validate_with_timing interest_mask n in
    times := stats.validation_time_ms :: !times
  done;
  
  let sorted_times = List.sort compare !times in
  let p99_index = (iterations * 99) / 100 in
  let p99 = List.nth sorted_times p99_index in
  let mean = List.fold_left (+.) 0.0 sorted_times /. float iterations in
  
  (p99, mean, sorted_times)