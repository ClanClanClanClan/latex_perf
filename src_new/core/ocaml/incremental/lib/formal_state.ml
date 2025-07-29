(* formal_state.ml - Formal lexer state matching master plans *)

(* 
   This module implements the formal lexer_state type and state codec
   as specified in the master plans MASTER_INCREMENTAL_LEXER_PLAN_1.md
   and MASTER_INCREMENTAL_LEXER_PLAN_2.md, providing the foundation
   for formal verification and mathematical correctness proofs.
*)

(** Formal lexer state representation matching Coq specification *)
type lexer_state = {
  in_comment   : bool;
  in_verbatim  : bool;
  math_mode    : bool;
  brace_depth  : int;
  line         : int;
  column       : int;
}

(** Initial state matching Coq init_state *)
let init_state = {
  in_comment = false;
  in_verbatim = false;
  math_mode = false;
  brace_depth = 0;
  line = 1;
  column = 1;
}

(** State codec functions (OCaml version of StateCodec.v) *)

let encode_bool (b : bool) : int = if b then 1 else 0

let encode_state (st : lexer_state) : int list =
  [ encode_bool st.in_comment;
    encode_bool st.in_verbatim;
    encode_bool st.math_mode;
    st.brace_depth;
    st.line;
    st.column ]

let decode_state (l : int list) : lexer_state option =
  match l with
  | [c; v; m; d; ln; col] ->
      Some {
        in_comment = (c = 1);
        in_verbatim = (v = 1);
        math_mode = (m = 1);
        brace_depth = d;
        line = ln;
        column = col;
      }
  | _ -> None

(** Codec correctness validation (roundtrip property) *)
let roundtrip_test (st : lexer_state) : bool =
  match decode_state (encode_state st) with
  | Some decoded -> decoded = st
  | None -> false

(** State validation functions *)
let validate_state (st : lexer_state) : bool =
  st.brace_depth >= 0 &&
  st.line >= 1 &&
  st.column >= 1 &&
  not (st.in_comment && st.in_verbatim) (* Cannot be in both modes *)

let validate_state_chain (states : lexer_state list) : bool =
  List.for_all validate_state states

(** State comparison for convergence detection *)
let state_equivalent (st1 : lexer_state) (st2 : lexer_state) : bool =
  st1.in_comment = st2.in_comment &&
  st1.in_verbatim = st2.in_verbatim &&
  st1.math_mode = st2.math_mode &&
  st1.brace_depth = st2.brace_depth
  (* Note: line and column are not compared for convergence *)

(** State transition functions *)
let enter_comment (st : lexer_state) : lexer_state =
  if st.in_verbatim then st
  else { st with in_comment = true }

let exit_comment (st : lexer_state) : lexer_state =
  { st with in_comment = false }

let enter_verbatim (st : lexer_state) : lexer_state =
  { st with in_verbatim = true; in_comment = false }

let exit_verbatim (st : lexer_state) : lexer_state =
  { st with in_verbatim = false }

let toggle_math_mode (st : lexer_state) : lexer_state =
  if st.in_verbatim || st.in_comment then st
  else { st with math_mode = not st.math_mode }

let enter_brace (st : lexer_state) : lexer_state =
  if st.in_verbatim || st.in_comment then st
  else { st with brace_depth = st.brace_depth + 1 }

let exit_brace (st : lexer_state) : lexer_state =
  if st.in_verbatim || st.in_comment then st
  else { st with brace_depth = max 0 (st.brace_depth - 1) }

let advance_position (st : lexer_state) (char : char) : lexer_state =
  if char = '\n' then
    { st with line = st.line + 1; column = 1 }
  else
    { st with column = st.column + 1 }

(** State serialization for checkpoint persistence *)
let serialize_state (st : lexer_state) : string =
  let encoded = encode_state st in
  String.concat "," (List.map string_of_int encoded)

let deserialize_state (s : string) : lexer_state option =
  try
    let parts = String.split_on_char ',' s in
    let encoded = List.map int_of_string parts in
    decode_state encoded
  with
  | _ -> None

(** Checkpoint integrity validation *)
type checkpoint = {
  cp_line : int;
  cp_offset : int;
  cp_state : lexer_state;
}

let checkpoint_integrity (cp : checkpoint) : bool =
  validate_state cp.cp_state &&
  cp.cp_line >= 0 &&
  cp.cp_offset >= 0

(** Debug utilities *)
let string_of_state (st : lexer_state) : string =
  Printf.sprintf 
    "{ comment=%b, verbatim=%b, math=%b, brace=%d, line=%d, col=%d }"
    st.in_comment st.in_verbatim st.math_mode 
    st.brace_depth st.line st.column

let print_state (st : lexer_state) : unit =
  Printf.printf "%s\n" (string_of_state st)

(** Self-test for codec correctness *)
let run_codec_tests () : bool =
  let test_states = [
    init_state;
    { init_state with in_comment = true };
    { init_state with in_verbatim = true };
    { init_state with math_mode = true };
    { init_state with brace_depth = 5 };
    { init_state with line = 100; column = 50 };
    {
      in_comment = false;
      in_verbatim = false;
      math_mode = true;
      brace_depth = 3;
      line = 42;
      column = 17;
    };
  ] in
  
  List.for_all roundtrip_test test_states

(** Integration with existing deep_state.ml interface *)
module DeepStateCompat = struct
  type deep_lexer_state = lexer_state
  
  let init_deep_state = init_state
  
  let state_stabilized = state_equivalent
  
  let estimate_affected_distance (st1 : lexer_state) (st2 : lexer_state) : int =
    let base_distance = if state_equivalent st1 st2 then 0 else 10 in
    let brace_penalty = abs (st1.brace_depth - st2.brace_depth) * 2 in
    let mode_penalty = 
      (if st1.in_verbatim <> st2.in_verbatim then 20 else 0) +
      (if st1.math_mode <> st2.math_mode then 5 else 0) in
    base_distance + brace_penalty + mode_penalty
  
  let hash_deep_state (st : lexer_state) : int64 =
    let components = encode_state st in
    List.fold_left (fun acc x -> 
      Int64.add (Int64.mul acc 31L) (Int64.of_int x)
    ) 0L components
end