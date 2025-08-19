(* L0 FUSED VALIDATORS - PATH A: <1ms without FFI *)
(* Validators integrated directly into L0 lexer loop *)

open Bigarray

(* Pre-allocated issue tracking *)
type issue_tracker = {
  positions: (int, int_elt, c_layout) Array1.t;
  rule_ids: (int, int8_unsigned_elt, c_layout) Array1.t;
  mutable count: int;
}

let create_tracker capacity = {
  positions = Array1.create int c_layout capacity;
  rule_ids = Array1.create int8_unsigned c_layout capacity;
  count = 0;
}

(* Rule IDs as int8 *)
let rule_quote = 1
let rule_double_hyphen = 2
let rule_triple_hyphen = 3
let rule_ellipsis = 5
let rule_tab = 6
let rule_trailing_space = 7
let rule_unmatched_brace = 101

(* Inline validator state *)
type validator_state = {
  mutable brace_depth: int;
  mutable last_was_hyphen: bool;
  mutable hyphen_count: int;
  mutable last_was_period: bool;
  mutable period_count: int;
  mutable last_was_space: bool;
  tracker: issue_tracker;
}

let create_validator_state () = {
  brace_depth = 0;
  last_was_hyphen = false;
  hyphen_count = 0;
  last_was_period = false;
  period_count = 0;
  last_was_space = false;
  tracker = create_tracker 65536;
}

(* CRITICAL: This function gets INLINED into L0's hot loop *)
let[@inline always] check_byte state byte position =
  let t = state.tracker in
  
  (* Quote check - immediate *)
  if byte = 34 then begin (* ASCII double-quote *)
    Array1.unsafe_set t.positions t.count position;
    Array1.unsafe_set t.rule_ids t.count rule_quote;
    t.count <- t.count + 1
  end;
  
  (* Hyphen sequence detection *)
  if byte = 45 then begin (* hyphen *)
    if state.last_was_hyphen then begin
      state.hyphen_count <- state.hyphen_count + 1;
      if state.hyphen_count = 2 then begin
        (* Double hyphen *)
        Array1.unsafe_set t.positions t.count (position - 1);
        Array1.unsafe_set t.rule_ids t.count rule_double_hyphen;
        t.count <- t.count + 1
      end else if state.hyphen_count = 3 then begin
        (* Triple hyphen *)
        Array1.unsafe_set t.positions t.count (position - 2);
        Array1.unsafe_set t.rule_ids t.count rule_triple_hyphen;
        t.count <- t.count + 1
      end
    end else begin
      state.last_was_hyphen <- true;
      state.hyphen_count <- 1
    end
  end else begin
    state.last_was_hyphen <- false;
    state.hyphen_count <- 0
  end;
  
  (* Period/ellipsis detection *)
  if byte = 46 then begin (* period *)
    if state.last_was_period then begin
      state.period_count <- state.period_count + 1;
      if state.period_count = 3 then begin
        Array1.unsafe_set t.positions t.count (position - 2);
        Array1.unsafe_set t.rule_ids t.count rule_ellipsis;
        t.count <- t.count + 1
      end
    end else begin
      state.last_was_period <- true;
      state.period_count <- 1
    end
  end else begin
    state.last_was_period <- false;
    state.period_count <- 0
  end;
  
  (* Tab check *)
  if byte = 9 then begin
    Array1.unsafe_set t.positions t.count position;
    Array1.unsafe_set t.rule_ids t.count rule_tab;
    t.count <- t.count + 1
  end;
  
  (* Brace tracking *)
  if byte = 123 then (* left brace *)
    state.brace_depth <- state.brace_depth + 1
  else if byte = 125 then begin (* right brace *)
    if state.brace_depth = 0 then begin
      (* Unmatched closing brace *)
      Array1.unsafe_set t.positions t.count position;
      Array1.unsafe_set t.rule_ids t.count rule_unmatched_brace;
      t.count <- t.count + 1
    end else
      state.brace_depth <- state.brace_depth - 1
  end;
  
  (* Space tracking for trailing space detection *)
  if byte = 32 || byte = 9 then
    state.last_was_space <- true
  else if byte = 10 || byte = 13 then begin
    (* Newline - check for trailing space *)
    if state.last_was_space then begin
      Array1.unsafe_set t.positions t.count (position - 1);
      Array1.unsafe_set t.rule_ids t.count rule_trailing_space;
      t.count <- t.count + 1
    end;
    state.last_was_space <- false
  end else
    state.last_was_space <- false

(* Simulated L0 integration - this would be IN the L0 loop *)
let lex_with_validation bytes n =
  let state = create_validator_state () in
  
  (* This loop represents L0's main loop *)
  for i = 0 to n - 1 do
    let byte = Char.code bytes.[i] in
    
    (* L0 does its normal tokenization work here *)
    (* ... *)
    
    (* Fused validation - happens while byte is hot in L1 cache *)
    check_byte state byte i
  done;
  
  (* Check for unclosed braces at end *)
  if state.brace_depth > 0 then
    for _ = 1 to state.brace_depth do
      Array1.unsafe_set state.tracker.positions state.tracker.count 0;
      Array1.unsafe_set state.tracker.rule_ids state.tracker.count rule_unmatched_brace;
      state.tracker.count <- state.tracker.count + 1
    done;
  
  state.tracker

(* Benchmark the fused approach *)
let bench_fused input_bytes =
  let n = String.length input_bytes in
  
  (* Warm up *)
  for _ = 1 to 10 do
    ignore (lex_with_validation input_bytes n)
  done;
  
  (* Benchmark *)
  let times = ref [] in
  for _ = 1 to 100 do
    let t0 = Unix.gettimeofday () in
    let tracker = lex_with_validation input_bytes n in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 98 in
  let p95 = List.nth sorted 94 in
  let p50 = List.nth sorted 49 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 100.0 in
  
  Printf.printf "L0-fused validator (%d bytes):\n" n;
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  
  let scale = 1_100_000.0 /. float n in
  Printf.printf "\nEstimated for 1.1MB document:\n";
  Printf.printf "  P99: %.3fms incremental cost\n" (p99 *. scale);
  
  if p99 *. scale < 1.0 then
    Printf.printf "✅ SUCCESS: <1ms incremental validation cost!\n"
  else
    Printf.printf "⚠️ Consider C microkernel for further optimization\n";
  
  let final_result = (p99 *. scale) in
  (let _ = lex_with_validation input_bytes n in ()); (* Prevent unused var warning *)
  final_result

(* HOW TO INTEGRATE WITH REAL L0:
   
   In your actual L0 lexer (lexer_v25.ml or similar):
   
   1. Add validator_state to the lexer state
   2. Call check_byte inline in the main loop where you process each byte
   3. Return the issue tracker along with tokens
   
   Example integration point:
   
   let lex_document input =
     let state = create_lexer_state () in
     let val_state = create_validator_state () in  (* ADD THIS *)
     
     while not (is_eof state) do
       let byte = get_next_byte state in
       
       (* Normal lexer work *)
       match state.mode with
       | ... -> ...
       
       (* Fused validation - nearly free! *)
       check_byte val_state byte state.position;  (* ADD THIS *)
       
       advance state
     done;
     
     (state.tokens, val_state.tracker)  (* Return both *)
*)