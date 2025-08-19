(* Hot SoA lanes only - as specified in the plan *)
open Bigarray

type hot = {
  (* token kind as uint8; codepoint or ASCII byte as uint32 if applicable *)
  kinds : (int, int8_unsigned_elt, c_layout) Array1.t;
  codes : (int32, int32_elt, c_layout) Array1.t;
  offs  : (int32, int32_elt, c_layout) Array1.t;  (* byte offset *)
  mutable len : int;
}

let make_hot ~capacity = {
  kinds = Array1.create Int8_unsigned C_layout capacity;
  codes = Array1.create Int32 C_layout capacity;
  offs  = Array1.create Int32 C_layout capacity;
  len = 0;
}

(* Issues pool - no per-issue allocation *)
module Issues_pool = struct
  type issue_code = 
    | AsciiQuote 
    | DoubleHyphen 
    | Ellipsis 
    | Tab 
    | MultiSpace

  let code_to_int = function
    | AsciiQuote -> 1
    | DoubleHyphen -> 2
    | Ellipsis -> 3
    | Tab -> 4
    | MultiSpace -> 5

  type t = {
    offs  : (int32, int32_elt, c_layout) Array1.t;
    codes : (int, int16_signed_elt, c_layout) Array1.t;
    mutable len : int;
    cap : int;
  }

  let make ~capacity = {
    offs = Array1.create Int32 C_layout capacity;
    codes = Array1.create Int16_signed C_layout capacity;
    len = 0; 
    cap = capacity;
  }

  let[@inline] push t off code =
    if t.len < t.cap then (
      Array1.unsafe_set t.offs t.len (Int32.of_int off);
      Array1.unsafe_set t.codes t.len (code_to_int code);
      t.len <- t.len + 1
    )
  
  let clear t = t.len <- 0
end

(* Fused fill + validate - exact implementation from the plan *)
let validate_during_fill (src : bytes) (hot : hot) =
  let n = Bytes.length src in
  let issues = Issues_pool.make ~capacity:65536 () in
  let i = ref 0 in
  let in_space_run = ref false in
  let space_run_start = ref 0 in
  
  while !i < n do
    let c = int_of_char (Bytes.unsafe_get src !i) in
    
    (* Write hot SoA once *)
    let kind_other = 12 in (* Other catcode *)
    Array1.unsafe_set hot.kinds hot.len kind_other;
    Array1.unsafe_set hot.codes hot.len (Int32.of_int c);
    Array1.unsafe_set hot.offs hot.len (Int32.of_int !i);
    hot.len <- hot.len + 1;

    (* Fused validators on ASCII fast-path *)
    if c = 34 then 
      Issues_pool.push issues !i Issues_pool.AsciiQuote;  (* " *)
    
    if c = 45 && !i+1 < n && int_of_char (Bytes.unsafe_get src (!i+1)) = 45 then
      Issues_pool.push issues !i Issues_pool.DoubleHyphen;  (* -- *)
    
    if c = 46 && !i+2 < n then begin  (* ... *)
      if Bytes.unsafe_get src (!i+1) = '.' && Bytes.unsafe_get src (!i+2) = '.' then
        Issues_pool.push issues !i Issues_pool.Ellipsis
    end;
    
    if c = 9 then 
      Issues_pool.push issues !i Issues_pool.Tab;  (* \t *)

    (* Multiple spaces run *)
    if c = 32 then (
      if not !in_space_run then (
        in_space_run := true; 
        space_run_start := !i
      )
    ) else if !in_space_run then (
      if !i - !space_run_start > 1 then 
        Issues_pool.push issues !space_run_start Issues_pool.MultiSpace;
      in_space_run := false
    );

    incr i
  done;
  
  (* Close trailing space run *)
  if !in_space_run && n - !space_run_start > 1 then 
    Issues_pool.push issues !space_run_start Issues_pool.MultiSpace;
  
  issues