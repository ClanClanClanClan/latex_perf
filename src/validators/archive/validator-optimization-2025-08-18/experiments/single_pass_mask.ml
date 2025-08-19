(* SINGLE-PASS MASK VALIDATOR - Correct Implementation *)
(* Read mask array ONCE, check all conditions in one loop *)

open Bigarray

type u8 = (int, int8_unsigned_elt, c_layout) Array1.t

type issues = {
  pos: (int32, int32_elt, c_layout) Array1.t;
  code: (int, int16_unsigned_elt, c_layout) Array1.t;
  mutable count: int;
}

type validator_state = {
  (* Issue tracking *)
  issues: issues;
  
  (* Hyphen run tracking *)
  mutable hyphen_start: int;
  mutable hyphen_count: int;
  
  (* Period run tracking *)
  mutable period_start: int;
  mutable period_count: int;
  
  (* Brace stack *)
  brace_stack: int array;
  mutable brace_sp: int;
}

let create_state () = {
  issues = {
    pos = Array1.create int32 c_layout 65536;
    code = Array1.create int16_unsigned c_layout 65536;
    count = 0;
  };
  hyphen_start = -1;
  hyphen_count = 0;
  period_start = -1;
  period_count = 0;
  brace_stack = Array.make 65536 0;
  brace_sp = 0;
}

(* Rule codes *)
let rule_quote = 1
let rule_endash = 2
let rule_emdash = 3
let rule_ellipsis = 5
let rule_tab = 6
let rule_unmatched = 7
let rule_unclosed = 8

let[@inline] record_issue state pos code =
  let c = state.issues.count in
  Array1.unsafe_set state.issues.pos c (Int32.of_int pos);
  Array1.unsafe_set state.issues.code c code;
  state.issues.count <- c + 1

(* Process end of hyphen run *)
let[@inline] end_hyphen_run state i =
  if state.hyphen_count = 2 then
    record_issue state state.hyphen_start rule_endash
  else if state.hyphen_count >= 3 then
    record_issue state state.hyphen_start rule_emdash;
  state.hyphen_count <- 0;
  state.hyphen_start <- -1

(* Process end of period run *)
let[@inline] end_period_run state i =
  if state.period_count >= 3 then
    record_issue state state.period_start rule_ellipsis;
  state.period_count <- 0;
  state.period_start <- -1

(* SINGLE PASS - The key optimization *)
let validate_single_pass interest n =
  let state = create_state () in
  
  (* ONE loop over the mask array *)
  for i = 0 to n - 1 do
    let m = Array1.unsafe_get interest i in
    
    (* Early exit for common case (93% of positions) *)
    if m <> 0 then begin
      
      (* Quote check - bit 0 *)
      if (m land 1) <> 0 then
        record_issue state i rule_quote;
      
      (* Hyphen tracking - bit 1 *)
      if (m land 2) <> 0 then begin
        if state.hyphen_count = 0 then
          state.hyphen_start <- i;
        state.hyphen_count <- state.hyphen_count + 1
      end else if state.hyphen_count > 0 then
        end_hyphen_run state i;
      
      (* Period tracking - bit 2 *)
      if (m land 4) <> 0 then begin
        if state.period_count = 0 then
          state.period_start <- i;
        state.period_count <- state.period_count + 1
      end else if state.period_count > 0 then
        end_period_run state i;
      
      (* Tab check - bit 3 *)
      if (m land 8) <> 0 then
        record_issue state i rule_tab;
      
      (* Left brace - bit 4 *)
      if (m land 16) <> 0 then begin
        state.brace_stack.(state.brace_sp) <- i;
        state.brace_sp <- state.brace_sp + 1
      end;
      
      (* Right brace - bit 5 *)
      if (m land 32) <> 0 then begin
        if state.brace_sp = 0 then
          record_issue state i rule_unmatched
        else
          state.brace_sp <- state.brace_sp - 1
      end
      
    end else begin
      (* m = 0, but need to check for run endings *)
      if state.hyphen_count > 0 then end_hyphen_run state i;
      if state.period_count > 0 then end_period_run state i
    end
  done;
  
  (* Handle any trailing runs *)
  if state.hyphen_count > 0 then end_hyphen_run state n;
  if state.period_count > 0 then end_period_run state n;
  
  (* Handle unclosed braces *)
  for j = 0 to state.brace_sp - 1 do
    record_issue state state.brace_stack.(j) rule_unclosed
  done;
  
  state.issues

(* Create test mask - same as before *)
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
      | _ -> 0        (* nothing - 93% *)
    in
    Array1.unsafe_set interest i mask
  done;
  interest

(* Benchmark the CORRECT single-pass implementation *)
let bench_single_pass n =
  let interest = create_test_mask n in
  
  (* Warmup *)
  for _ = 1 to 20 do
    ignore (validate_single_pass interest n)
  done;
  
  (* Measure *)
  let times = ref [] in
  for _ = 1 to 200 do
    let t0 = Unix.gettimeofday () in
    let _ = validate_single_pass interest n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 197 in
  let p95 = List.nth sorted 189 in
  let p50 = List.nth sorted 99 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 200.0 in
  
  Printf.printf "SINGLE-PASS mask validator (%d tokens):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  Printf.printf "  Memory: %.3fMB (ONE pass)\n" (float n /. 1_000_000.0);
  
  if p99 < 1.0 then
    Printf.printf "✅ SUCCESS: <1ms achieved with single pass!\n"
  else if p99 < 2.0 then
    Printf.printf "⚠️ Close: %.3fms (better than sparse 3.2ms)\n" p99
  else
    Printf.printf "❌ Still slow: %.3fms\n" p99;
  
  p99