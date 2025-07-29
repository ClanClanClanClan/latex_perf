(* state_codec.ml - Fast state serialization for v24-R3 *)

open Types

(** VLQ (Variable Length Quantity) encoding for compact integers *)
module VLQ = struct
  let encode_int n =
    let rec encode n acc =
      if n < 128 then
        (n land 0x7F) :: acc
      else
        encode (n lsr 7) ((n land 0x7F) lor 0x80 :: acc)
    in
    encode n [] |> List.rev |> 
    List.map char_of_int |> 
    List.to_seq |> 
    String.of_seq

  let decode_int s pos =
    let rec decode pos acc =
      if pos >= String.length s then
        (acc, pos)
      else
        let byte = int_of_char s.[pos] in
        let value = (acc lsl 7) lor (byte land 0x7F) in
        if byte land 0x80 = 0 then
          (value, pos + 1)
        else
          decode (pos + 1) value
    in
    decode pos 0
end

(** Encode mode to byte *)
let mode_to_byte = function
  | MNormal -> '\000'
  | MMath -> '\001'
  | MComment -> '\002'
  | MVerbatim -> '\003'

(** Decode byte to mode *)
let byte_to_mode = function
  | '\000' -> Some MNormal
  | '\001' -> Some MMath
  | '\002' -> Some MComment
  | '\003' -> Some MVerbatim
  | _ -> None

(** Encode lexer state to compact binary format *)
let encode_state state =
  let buf = Buffer.create 50 in
  (* Encode line_no and col_no as VLQ *)
  Buffer.add_string buf (VLQ.encode_int state.line_no);
  Buffer.add_string buf (VLQ.encode_int state.col_no);
  (* Encode boolean flags as single byte *)
  let flags = 
    (if state.in_math then 0x01 else 0) lor
    (if state.in_comment then 0x02 else 0) lor
    (if state.in_verbatim then 0x04 else 0) in
  Buffer.add_char buf (char_of_int flags);
  (* Encode mode stack length and contents *)
  Buffer.add_string buf (VLQ.encode_int (List.length state.mode_stack));
  List.iter (fun m -> Buffer.add_char buf (mode_to_byte m)) state.mode_stack;
  Buffer.contents buf

(** Decode lexer state from binary format *)
let decode_state s =
  try
    let pos = ref 0 in
    (* Decode line_no *)
    let line_no, new_pos = VLQ.decode_int s !pos in
    pos := new_pos;
    (* Decode col_no *)
    let col_no, new_pos = VLQ.decode_int s !pos in
    pos := new_pos;
    (* Decode flags *)
    if !pos >= String.length s then raise Exit;
    let flags = int_of_char s.[!pos] in
    incr pos;
    let in_math = (flags land 0x01) <> 0 in
    let in_comment = (flags land 0x02) <> 0 in
    let in_verbatim = (flags land 0x04) <> 0 in
    (* Decode mode stack *)
    let stack_len, new_pos = VLQ.decode_int s !pos in
    pos := new_pos;
    let mode_stack = ref [] in
    for _ = 1 to stack_len do
      if !pos >= String.length s then raise Exit;
      match byte_to_mode s.[!pos] with
      | Some m -> 
          mode_stack := m :: !mode_stack;
          incr pos
      | None -> raise Exit
    done;
    Some {
      line_no;
      col_no;
      in_math;
      in_comment;
      in_verbatim;
      mode_stack = List.rev !mode_stack;
    }
  with _ -> None

(** Calculate size of encoded state *)
let encoded_state_size state =
  String.length (encode_state state)

(** Fast hash of state for comparison *)
let hash_state state =
  let h = ref 0 in
  h := (!h * 31 + state.line_no) land 0x7FFFFFFF;
  h := (!h * 31 + state.col_no) land 0x7FFFFFFF;
  h := (!h * 31 + if state.in_math then 1 else 0) land 0x7FFFFFFF;
  h := (!h * 31 + if state.in_comment then 1 else 0) land 0x7FFFFFFF;
  h := (!h * 31 + if state.in_verbatim then 1 else 0) land 0x7FFFFFFF;
  h := (!h * 31 + List.length state.mode_stack) land 0x7FFFFFFF;
  !h

(** Test roundtrip property *)
let test_roundtrip () =
  let states = [
    init_state;
    { init_state with line_no = 42; col_no = 17 };
    { init_state with in_math = true; mode_stack = [MMath] };
    { init_state with line_no = 100000; col_no = 80; in_comment = true };
  ] in
  List.for_all (fun st ->
    match decode_state (encode_state st) with
    | Some st' -> st = st'
    | None -> false
  ) states