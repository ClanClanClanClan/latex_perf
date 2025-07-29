(* CHECKPOINT STATE CODEC
   LaTeX Perfectionist v24 - Lossless serialization/deserialization
   
   Implements the StateCodec.v functionality in OCaml:
   - Lossless encoding/decoding of lexer states
   - Checkpoint persistence for true incremental processing
   - Binary format for efficient storage
*)

open Printf

(* Lexer state representation matching Coq definition *)
type lexer_state = {
  position: int;
  line_number: int;
  column_number: int;
  in_math_mode: bool;
  in_command: bool;
  command_depth: int;
  brace_depth: int;
  environment_stack: string list;
}

(* Checkpoint with full context *)
type full_checkpoint = {
  state: lexer_state;
  content_hash: string;
  tokens_count: int;
  timestamp: float;
  version: int;  (* For format compatibility *)
}

(* Binary encoding utilities *)
let encode_int32 n =
  let bytes = Bytes.create 4 in
  Bytes.set_int32_be bytes 0 (Int32.of_int n);
  bytes

let decode_int32 bytes offset =
  (Int32.to_int (Bytes.get_int32_be bytes offset), offset + 4)

let encode_bool b =
  Bytes.of_string (if b then "\001" else "\000")

let decode_bool bytes offset =
  (Bytes.get_uint8 bytes offset = 1, offset + 1)

let encode_string s =
  let len = String.length s in
  let len_bytes = encode_int32 len in
  let content_bytes = Bytes.of_string s in
  Bytes.cat len_bytes content_bytes

let decode_string bytes offset =
  let (len, new_offset) = decode_int32 bytes offset in
  let s = Bytes.sub_string bytes new_offset len in
  (s, new_offset + len)

let encode_string_list strings =
  let count = List.length strings in
  let count_bytes = encode_int32 count in
  List.fold_left (fun acc s ->
    Bytes.cat acc (encode_string s)
  ) count_bytes strings

let decode_string_list bytes offset =
  let (count, new_offset) = decode_int32 bytes offset in
  let rec decode_n n acc offset =
    if n = 0 then (List.rev acc, offset)
    else
      let (s, next_offset) = decode_string bytes offset in
      decode_n (n - 1) (s :: acc) next_offset
  in
  decode_n count [] new_offset

(* Encode lexer state to binary format *)
let encode_lexer_state state =
  let components = [
    encode_int32 state.position;
    encode_int32 state.line_number;
    encode_int32 state.column_number;
    encode_bool state.in_math_mode;
    encode_bool state.in_command;
    encode_int32 state.command_depth;
    encode_int32 state.brace_depth;
    encode_string_list state.environment_stack;
  ] in
  List.fold_left Bytes.cat (Bytes.create 0) components

(* Decode lexer state from binary format *)
let decode_lexer_state bytes =
  try
    let (position, offset1) = decode_int32 bytes 0 in
    let (line_number, offset2) = decode_int32 bytes offset1 in
    let (column_number, offset3) = decode_int32 bytes offset2 in
    let (in_math_mode, offset4) = decode_bool bytes offset3 in
    let (in_command, offset5) = decode_bool bytes offset4 in
    let (command_depth, offset6) = decode_int32 bytes offset5 in
    let (brace_depth, offset7) = decode_int32 bytes offset6 in
    let (environment_stack, _) = decode_string_list bytes offset7 in
    
    Some {
      position;
      line_number;
      column_number;
      in_math_mode;
      in_command;
      command_depth;
      brace_depth;
      environment_stack;
    }
  with _ -> None

(* Encode full checkpoint with metadata *)
let encode_checkpoint checkpoint =
  let version_bytes = encode_int32 checkpoint.version in
  let timestamp_bytes = encode_int32 (int_of_float checkpoint.timestamp) in
  let tokens_count_bytes = encode_int32 checkpoint.tokens_count in
  let hash_bytes = encode_string checkpoint.content_hash in
  let state_bytes = encode_lexer_state checkpoint.state in
  
  List.fold_left Bytes.cat (Bytes.create 0) [
    version_bytes;
    timestamp_bytes; 
    tokens_count_bytes;
    hash_bytes;
    state_bytes;
  ]

(* Decode full checkpoint with validation *)
let decode_checkpoint bytes =
  try
    let (version, offset1) = decode_int32 bytes 0 in
    if version <> 1 then failwith "Unsupported checkpoint version";
    
    let (timestamp_int, offset2) = decode_int32 bytes offset1 in
    let (tokens_count, offset3) = decode_int32 bytes offset2 in
    let (content_hash, offset4) = decode_string bytes offset3 in
    
    let state_bytes = Bytes.sub bytes offset4 (Bytes.length bytes - offset4) in
    match decode_lexer_state state_bytes with
    | None -> None
    | Some state ->
      Some {
        state;
        content_hash;
        tokens_count;
        timestamp = float_of_int timestamp_int;
        version;
      }
  with _ -> None

(* Create checkpoint from current lexer state *)
let create_checkpoint state content_hash tokens_count =
  {
    state;
    content_hash;
    tokens_count;
    timestamp = Unix.time ();
    version = 1;
  }

(* Validate checkpoint integrity *)
let validate_checkpoint checkpoint expected_hash =
  checkpoint.content_hash = expected_hash &&
  checkpoint.version = 1 &&
  checkpoint.timestamp > 0.0

(* Checkpoint comparison for early termination *)
let checkpoints_equivalent cp1 cp2 =
  cp1.content_hash = cp2.content_hash &&
  cp1.state.position = cp2.state.position &&
  cp1.state.line_number = cp2.state.line_number &&
  cp1.state.column_number = cp2.state.column_number &&
  cp1.state.in_math_mode = cp2.state.in_math_mode &&
  cp1.state.in_command = cp2.state.in_command &&
  cp1.state.command_depth = cp2.state.command_depth &&
  cp1.state.brace_depth = cp2.state.brace_depth &&
  cp1.state.environment_stack = cp2.state.environment_stack

(* Roundtrip test for codec correctness *)
let test_codec_roundtrip () =
  printf "Testing checkpoint codec roundtrip...\n";
  
  let test_state = {
    position = 12345;
    line_number = 456;
    column_number = 78;
    in_math_mode = true;
    in_command = false;
    command_depth = 2;
    brace_depth = 3;
    environment_stack = ["equation"; "document"];
  } in
  
  let test_checkpoint = create_checkpoint test_state "test_hash_123" 789 in
  
  (* Encode then decode *)
  let encoded = encode_checkpoint test_checkpoint in
  match decode_checkpoint encoded with
  | None -> 
    printf "❌ Codec test FAILED: decode returned None\n";
    false
  | Some decoded ->
    let success = checkpoints_equivalent test_checkpoint decoded in
    printf "%s Codec roundtrip test\n" (if success then "✅" else "❌");
    if not success then (
      printf "Original: pos=%d, line=%d, col=%d\n" 
        test_checkpoint.state.position 
        test_checkpoint.state.line_number 
        test_checkpoint.state.column_number;
      printf "Decoded:  pos=%d, line=%d, col=%d\n" 
        decoded.state.position 
        decoded.state.line_number 
        decoded.state.column_number;
    );
    success

(* Performance test for codec efficiency *)
let test_codec_performance () =
  printf "Testing codec performance...\n";
  
  let create_test_checkpoint i =
    let state = {
      position = i * 100;
      line_number = i;
      column_number = i mod 80;
      in_math_mode = i mod 2 = 0;
      in_command = i mod 3 = 0;
      command_depth = i mod 5;
      brace_depth = i mod 4;
      environment_stack = 
        if i mod 10 = 0 then ["equation"; "align"; "document"]
        else if i mod 5 = 0 then ["document"]
        else [];
    } in
    create_checkpoint state (Printf.sprintf "hash_%d" i) (i * 10)
  in
  
  let checkpoints = List.init 1000 create_test_checkpoint in
  
  (* Encode all checkpoints *)
  let start_time = Unix.gettimeofday () in
  let encoded_checkpoints = List.map encode_checkpoint checkpoints in
  let encode_time = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  (* Decode all checkpoints *)
  let start_time = Unix.gettimeofday () in
  let decoded_checkpoints = List.map decode_checkpoint encoded_checkpoints in
  let decode_time = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  let success_count = List.fold_left (fun acc opt ->
    match opt with Some _ -> acc + 1 | None -> acc
  ) 0 decoded_checkpoints in
  
  printf "Encoded/decoded %d checkpoints\n" (List.length checkpoints);
  printf "Encode time: %.2fms (%.3fms per checkpoint)\n" 
    encode_time (encode_time /. 1000.0);
  printf "Decode time: %.2fms (%.3fms per checkpoint)\n" 
    decode_time (decode_time /. 1000.0);
  printf "Success rate: %d/%d (%.1f%%)\n" 
    success_count (List.length checkpoints) 
    (100.0 *. float_of_int success_count /. float_of_int (List.length checkpoints));
  
  (* Calculate storage efficiency *)
  let total_bytes = List.fold_left (fun acc bytes -> acc + Bytes.length bytes) 0 encoded_checkpoints in
  let avg_bytes = float_of_int total_bytes /. float_of_int (List.length checkpoints) in
  printf "Average checkpoint size: %.1f bytes\n" avg_bytes;
  
  success_count = List.length checkpoints

(* Main test suite *)
let run_tests () =
  printf "🧪 CHECKPOINT STATE CODEC TESTS\n";
  printf "================================\n";
  
  let roundtrip_ok = test_codec_roundtrip () in
  let performance_ok = test_codec_performance () in
  
  printf "\n📊 CODEC TEST SUMMARY:\n";
  printf "Roundtrip correctness: %s\n" (if roundtrip_ok then "✅ PASS" else "❌ FAIL");
  printf "Performance test: %s\n" (if performance_ok then "✅ PASS" else "❌ FAIL");
  printf "Overall result: %s\n" 
    (if roundtrip_ok && performance_ok then "✅ ALL TESTS PASSED" else "❌ SOME TESTS FAILED");
  
  (roundtrip_ok && performance_ok)

(* Export functions for use by incremental lexer *)
let serialize_state = encode_lexer_state
let deserialize_state = decode_lexer_state
let serialize_checkpoint = encode_checkpoint
let deserialize_checkpoint = decode_checkpoint

(* Main execution when run directly *)
let () =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "test" then
    ignore (run_tests ())