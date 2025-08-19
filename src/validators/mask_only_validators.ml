(* MASK-ONLY VALIDATORS - Following Expert's Exact Plan *)
(* Achieves <1ms by reading ONLY 8-bit interest mask, not 32-bit kinds/codes *)

open Bigarray

(* 8-bit interest mask type *)
type u8 = (int, int8_unsigned_elt, c_layout) Array1.t

(* Issue storage - off-heap for zero GC *)
type issues = {
  pos: (int32, int32_elt, c_layout) Array1.t;         (* token indices *)
  code: (int, int16_unsigned_elt, c_layout) Array1.t; (* rule IDs *)
  mutable count: int;
}

(* Create issue buffer *)
let create_issues capacity = {
  pos = Array1.create int32 c_layout capacity;
  code = Array1.create int16_unsigned c_layout capacity;
  count = 0;
}

(* Record issue *)
let record_issue issues pos code =
  let cnt = issues.count in
  Array1.unsafe_set issues.pos cnt (Int32.of_int pos);
  Array1.unsafe_set issues.code cnt code;
  issues.count <- succ cnt;;

(* Interest bit layout:
   bit 0 (1):  quote (")
   bit 1 (2):  hyphen (-)
   bit 2 (4):  period (.)
   bit 3 (8):  tab (\t)
   bit 4 (16): left brace ({)
   bit 5 (32): right brace (})
*)

(* Rule codes *)
let rule_quote = 1
let rule_endash = 2    (* -- *)
let rule_emdash = 3    (* --- *)
let rule_ellipsis = 5  (* ... *)
let rule_tab = 6
let rule_unmatched_close = 7
let rule_unclosed_open = 8

(* VALIDATOR 1: ASCII quotes - simplest possible loop *)
let validate_quotes (interest: u8) n (iss: issues) =
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 1) <> 0 then 
      record_issue iss i rule_quote
  done

(* VALIDATOR 2: Hyphen runs with smart skipping *)
let validate_hyphen_runs (interest: u8) n (iss: issues) =
  let i = ref 0 in
  while !i < n do
    let m = Array1.unsafe_get interest !i in
    if (m land 2) = 0 then 
      incr i  (* Not a hyphen, continue *)
    else begin
      (* Found hyphen - count the run *)
      let j = ref (!i + 1) in
      while !j < n && ((Array1.unsafe_get interest !j) land 2) <> 0 do
        incr j
      done;
      let run_length = !j - !i in
      (* Flag at start of run based on length *)
      if run_length = 2 then 
        record_issue iss !i rule_endash
      else if run_length >= 3 then 
        record_issue iss !i rule_emdash;
      (* KEY: Skip entire run, don't re-scan these bytes *)
      i := !j
    end
  done

(* VALIDATOR 3: Ellipsis detection with run skipping *)
let validate_ellipsis (interest: u8) n (iss: issues) =
  let i = ref 0 in
  while !i < n do
    let m = Array1.unsafe_get interest !i in
    if (m land 4) = 0 then 
      incr i  (* Not a period *)
    else begin
      (* Found period - count the run *)
      let j = ref (!i + 1) in
      while !j < n && ((Array1.unsafe_get interest !j) land 4) <> 0 do
        incr j
      done;
      let run_length = !j - !i in
      if run_length >= 3 then 
        record_issue iss !i rule_ellipsis;
      (* Skip entire run *)
      i := !j
    end
  done

(* VALIDATOR 4: Tabs - simple like quotes *)
let validate_tabs (interest: u8) n (iss: issues) =
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 8) <> 0 then 
      record_issue iss i rule_tab
  done

(* VALIDATOR 5: Brace balance with stack *)
let validate_braces (interest: u8) n (iss: issues) =
  (* Pre-allocated stack - no allocation in loop *)
  let stack = Array.make 65536 0 in
  let sp = ref 0 in
  
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 16) <> 0 then begin
      (* Left brace - push *)
      stack.(!sp) <- i;
      incr sp
    end else if (m land 32) <> 0 then begin
      (* Right brace - pop or error *)
      if !sp = 0 then 
        record_issue iss i rule_unmatched_close
      else 
        decr sp
    end
  done;
  
  (* Any remaining open braces are unclosed *)
  while !sp > 0 do
    decr sp;
    record_issue iss stack.(!sp) rule_unclosed_open
  done

(* MAIN DRIVER: 4 passes over 0.26MB total *)
let validate_all (interest: u8) n =
  let issues = create_issues 65536 in
  
  (* Each pass reads only 276KB *)
  validate_quotes interest n issues;
  validate_hyphen_runs interest n issues;  (* Run-skipping *)
  validate_ellipsis interest n issues;     (* Run-skipping *)
  validate_tabs interest n issues;
  validate_braces interest n issues;
  
  issues

(* CRITICAL FOR L0 INTEGRATION: Interest mask lookup table *)
let create_interest_lut () =
  let lut = Bytes.create 256 in
  (* Initialize all to 0 *)
  Bytes.fill lut 0 256 '\000';
  (* Set specific bits for characters of interest *)
  Bytes.set lut 34 '\001';   (* " → bit 0 *)
  Bytes.set lut 45 '\002';   (* - → bit 1 *)
  Bytes.set lut 46 '\004';   (* . → bit 2 *)
  Bytes.set lut 9  '\008';   (* \t → bit 3 *)
  Bytes.set lut 123 '\016';  (* { → bit 4 *)
  Bytes.set lut 125 '\032';  (* } → bit 5 *)
  lut;;

(* Global LUT - created once at startup *)
let interest_lut = create_interest_lut ();;

(* Function to be called from L0 lexer for each token *)
let compute_interest_mask ~is_char ~ascii_code =
  if is_char && ascii_code < 128 then
    Char.code (Bytes.unsafe_get interest_lut ascii_code)
  else
    0;;

(* BENCHMARK HARNESS *)
let bench_mask_only interest_array n =
  (* Warmup *)
  for _ = 1 to 20 do
    ignore (validate_all interest_array n)
  done;
  
  (* Measure *)
  let times = ref [] in
  for _ = 1 to 200 do
    let t0 = Unix.gettimeofday () in
    let issues = validate_all interest_array n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times;
    ignore issues.count
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 197 in  (* 99th percentile of 200 *)
  let p95 = List.nth sorted 189 in
  let p50 = List.nth sorted 99 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 200.0 in
  
  Printf.printf "Mask-only validator performance (%d tokens):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  Printf.printf "  Memory read: %.3fMB (mask only)\n" (float n /. 1_000_000.0);
  
  if p99 < 1.0 then
    Printf.printf "✅ SUCCESS: <1ms validation achieved!\n"
  else
    Printf.printf "⚠️ %.3fms - investigate stray memory reads\n" p99;
  
  p99

(* TEST: Create synthetic interest mask for testing *)
let create_test_interest_mask n =
  let interest = Array1.create int8_unsigned c_layout n in
  (* Fill with realistic pattern:
     ~1% quotes, ~2% hyphens, ~3% periods, ~1% tabs, ~0.5% each brace *)
  for i = 0 to n - 1 do
    let mask = 
      match i mod 100 with
      | 0 -> 1        (* quote *)
      | 1 | 2 -> 2    (* hyphen *)
      | 3 | 4 | 5 -> 4 (* period *)
      | 6 -> 8        (* tab *)
      | 7 -> 16       (* { *)
      | 8 -> 32       (* } *)
      | _ -> 0        (* nothing *)
    in
    Array1.unsafe_set interest i mask
  done;
  interest

(* Integration point for L0 *)
module L0_Integration = struct
  (* This is what L0 should call for each token during lexing *)
  let[@inline] write_interest_mask interest_array index ~token_kind ~ascii_code =
    let is_char = (token_kind = 12) in  (* KIND_OTHER = 12 from your code *)
    let mask = compute_interest_mask ~is_char ~ascii_code in
    Array1.unsafe_set interest_array index mask
  
  (* L0 should allocate this at start *)
  let allocate_interest_mask n =
    Array1.create int8_unsigned c_layout n
end