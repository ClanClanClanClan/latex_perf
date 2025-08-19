(* PHASE 3: Streaming Adapter for Structure of Arrays - Zero-copy to off-heap storage *)
open Tokens_soa

(* Convert packed tokens directly into SoA - no intermediate allocations *)
let convert_to_soa packed_tokens soa =
  let num_tokens = Array.length packed_tokens in
  
  (* Clear the SoA arena *)
  clear_tokens_soa soa;
  
  (* Check capacity *)
  if num_tokens > soa.capacity then
    failwith (Printf.sprintf "SoA capacity (%d) insufficient for %d tokens" 
                soa.capacity num_tokens);
  
  (* Position tracking state *)
  let line = ref 1 in
  let column = ref 1 in
  let byte_pos = ref 0 in
  
  (* Process each packed token directly into SoA *)
  for i = 0 to num_tokens - 1 do
    let packed = packed_tokens.(i) in
    let catcode = Int32.to_int (Int32.logand packed 0x3Fl) in
    let data = Int32.to_int (Int32.shift_right_logical packed 6) in
    
    let start_pos = !byte_pos in
    let end_pos = !byte_pos + 1 in
    
    (* Push directly to off-heap storage *)
    let success = push_token_soa soa 
      ~kind:catcode 
      ~data:data 
      ~start_pos:start_pos 
      ~end_pos:end_pos 
      ~line:!line 
      ~col:!column in
    
    if not success then
      failwith "Failed to push token to SoA";
    
    (* Update position tracking *)
    if catcode = 5 then begin (* newline *)
      incr line;
      column := 1;
    end else begin
      incr column;
    end;
    incr byte_pos;
  done

(* Ultra-fast minimal adapter - no position tracking for maximum performance *)
let convert_to_soa_minimal packed_tokens soa =
  let num_tokens = Array.length packed_tokens in
  
  clear_tokens_soa soa;
  
  if num_tokens > soa.capacity then
    failwith (Printf.sprintf "SoA capacity insufficient for %d tokens" num_tokens);
  
  (* Tight loop - no position calculations *)
  for i = 0 to num_tokens - 1 do
    let packed = packed_tokens.(i) in
    let catcode = Int32.to_int (Int32.logand packed 0x3Fl) in
    let data = Int32.to_int (Int32.shift_right_logical packed 6) in
    
    (* Minimal position info - focus on speed *)
    let success = push_token_soa soa 
      ~kind:catcode 
      ~data:data 
      ~start_pos:i 
      ~end_pos:(i + 1)
      ~line:1           (* Default line *)
      ~col:i in         (* Simple column *)
    
    if not success then
      failwith "SoA push failed";
  done

(* Memory usage comparison *)
let memory_savings_report old_array_size soa =
  let old_memory = old_array_size * 48 in  (* 48 bytes per located_token *)
  let new_memory = memory_usage_bytes soa in
  let savings = old_memory - new_memory in
  let savings_mb = float_of_int savings /. 1_048_576.0 in
  Printf.sprintf "Memory savings: %d bytes (%.2f MB) - %d%% reduction"
    savings savings_mb (savings * 100 / old_memory)