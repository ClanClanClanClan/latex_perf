(* CLEAN MASK-ONLY VALIDATORS - Simplified syntax *)
open Bigarray

type u8 = (int, int8_unsigned_elt, c_layout) Array1.t

type issues = {
  pos: (int32, int32_elt, c_layout) Array1.t;
  code: (int, int16_unsigned_elt, c_layout) Array1.t;
  mutable count: int;
}

let create_issues capacity = {
  pos = Array1.create int32 c_layout capacity;
  code = Array1.create int16_unsigned c_layout capacity;
  count = 0;
}

let record_issue issues pos code =
  let c = issues.count in
  Array1.unsafe_set issues.pos c (Int32.of_int pos);
  Array1.unsafe_set issues.code c code;
  issues.count <- c + 1

(* Rule codes *)
let rule_quote = 1
let rule_endash = 2
let rule_emdash = 3
let rule_ellipsis = 5
let rule_tab = 6
let rule_unmatched = 7
let rule_unclosed = 8

(* Validate quotes - bit 0 *)
let validate_quotes interest n issues =
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 1) <> 0 then 
      record_issue issues i rule_quote
  done

(* Validate hyphens - bit 1 with run detection *)
let validate_hyphens interest n issues =
  let i = ref 0 in
  while !i < n do
    let m = Array1.unsafe_get interest !i in
    if (m land 2) = 0 then 
      incr i
    else begin
      let start = !i in
      let j = ref (!i + 1) in
      while !j < n && ((Array1.unsafe_get interest !j) land 2) <> 0 do
        incr j
      done;
      let len = !j - start in
      if len = 2 then record_issue issues start rule_endash
      else if len >= 3 then record_issue issues start rule_emdash;
      i := !j
    end
  done

(* Validate periods - bit 2 with run detection *)
let validate_periods interest n issues =
  let i = ref 0 in
  while !i < n do
    let m = Array1.unsafe_get interest !i in
    if (m land 4) = 0 then 
      incr i
    else begin
      let start = !i in
      let j = ref (!i + 1) in
      while !j < n && ((Array1.unsafe_get interest !j) land 4) <> 0 do
        incr j
      done;
      let len = !j - start in
      if len >= 3 then record_issue issues start rule_ellipsis;
      i := !j
    end
  done

(* Validate tabs - bit 3 *)
let validate_tabs interest n issues =
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 8) <> 0 then 
      record_issue issues i rule_tab
  done

(* Validate braces - bits 4 and 5 *)
let validate_braces interest n issues =
  let stack = Array.make 65536 0 in
  let sp = ref 0 in
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    if (m land 16) <> 0 then begin
      stack.(!sp) <- i;
      incr sp
    end else if (m land 32) <> 0 then begin
      if !sp = 0 then 
        record_issue issues i rule_unmatched
      else 
        decr sp
    end
  done;
  for j = 0 to !sp - 1 do
    record_issue issues stack.(j) rule_unclosed
  done

(* Main validation driver *)
let validate_all interest n =
  let issues = create_issues 65536 in
  validate_quotes interest n issues;
  validate_hyphens interest n issues;
  validate_periods interest n issues;
  validate_tabs interest n issues;
  validate_braces interest n issues;
  issues

(* Create test interest mask *)
let create_test_mask n =
  let interest = Array1.create int8_unsigned c_layout n in
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

(* Benchmark function *)
let bench n =
  let interest = create_test_mask n in
  
  (* Warmup *)
  for _ = 1 to 20 do
    ignore (validate_all interest n)
  done;
  
  (* Measure *)
  let times = ref [] in
  for _ = 1 to 200 do
    let t0 = Unix.gettimeofday () in
    let _ = validate_all interest n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 197 in
  let p95 = List.nth sorted 189 in
  let p50 = List.nth sorted 99 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 200.0 in
  
  Printf.printf "Mask-only validator (%d tokens):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  Printf.printf "  Memory: %.3fMB\n" (float n /. 1_000_000.0);
  
  if p99 < 1.0 then
    Printf.printf "✅ <1ms achieved!\n"
  else
    Printf.printf "⚠️ %.3fms\n" p99;
  
  p99