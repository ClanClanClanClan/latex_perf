(* PRODUCTION SINGLE-PASS VALIDATOR - Optimized for <1.2ms performance *)

open Validator_types

(* Record issue with maximum performance *)
let[@inline always] record_issue state position rule_code =
  let cnt = state.issues.count in
  Array1.unsafe_set state.issues.positions cnt (Int32.of_int position);
  Array1.unsafe_set state.issues.rule_codes cnt rule_code;
  state.issues.count <- cnt + 1

(* End hyphen run processing *)
let[@inline] end_hyphen_run state position =
  match state.hyphen_count with
  | 2 -> record_issue state state.hyphen_start Rules.endash
  | n when n >= 3 -> record_issue state state.hyphen_start Rules.emdash
  | _ -> ();
  state.hyphen_count <- 0;
  state.hyphen_start <- -1

(* End period run processing *)
let[@inline] end_period_run state position =
  if state.period_count >= 3 then
    record_issue state state.period_start Rules.ellipsis;
  state.period_count <- 0;
  state.period_start <- -1

(* CORE ALGORITHM: Single-pass validation with maximum optimization *)
let validate_single_pass interest_mask n_tokens =
  let state = create_validator_state 65536 in
  let early_exits = ref 0 in
  
  (* CRITICAL: Single pass over interest mask *)
  for i = 0 to n_tokens - 1 do
    let mask = Array1.unsafe_get interest_mask i in
    
    (* OPTIMIZATION: Early exit for 93% of positions *)
    if mask = 0 then
      incr early_exits
    else begin
      (* Check all conditions in order of frequency *)
      
      (* Hyphen tracking (most complex) - bit 1 *)
      if (mask land InterestBits.hyphen) <> 0 then begin
        if state.hyphen_count = 0 then state.hyphen_start <- i;
        state.hyphen_count <- state.hyphen_count + 1
      end else if state.hyphen_count > 0 then
        end_hyphen_run state i;
      
      (* Period tracking - bit 2 *)
      if (mask land InterestBits.period) <> 0 then begin
        if state.period_count = 0 then state.period_start <- i;
        state.period_count <- state.period_count + 1
      end else if state.period_count > 0 then
        end_period_run state i;
      
      (* Quote check (simplest) - bit 0 *)
      if (mask land InterestBits.quote) <> 0 then
        record_issue state i Rules.quote;
      
      (* Tab check - bit 3 *)
      if (mask land InterestBits.tab) <> 0 then
        record_issue state i Rules.tab;
      
      (* Brace tracking - bits 4,5 *)
      if (mask land InterestBits.left_brace) <> 0 then begin
        state.brace_stack.(state.brace_sp) <- i;
        state.brace_sp <- state.brace_sp + 1
      end else if (mask land InterestBits.right_brace) <> 0 then begin
        if state.brace_sp = 0 then
          record_issue state i Rules.unmatched_close
        else
          state.brace_sp <- state.brace_sp - 1
      end
    end
  done;
  
  (* Handle trailing runs *)
  if state.hyphen_count > 0 then end_hyphen_run state n_tokens;
  if state.period_count > 0 then end_period_run state n_tokens;
  
  (* Handle unclosed braces *)
  while state.brace_sp > 0 do
    state.brace_sp <- state.brace_sp - 1;
    record_issue state state.brace_stack.(state.brace_sp) Rules.unclosed_open
  done;
  
  (* Return results with performance stats *)
  let early_exit_rate = float !early_exits /. float n_tokens *. 100.0 in
  (state.issues, early_exit_rate)

(* High-level validation interface *)
let validate interest_mask n_tokens =
  let (issues, _) = validate_single_pass interest_mask n_tokens in
  issues

(* Performance validation with timing *)
let validate_with_timing interest_mask n_tokens =
  let t0 = Unix.gettimeofday () in
  let (issues, early_exit_rate) = validate_single_pass interest_mask n_tokens in
  let t1 = Unix.gettimeofday () in
  
  let stats = {
    validation_time_ms = (t1 -. t0) *. 1000.0;
    tokens_processed = n_tokens;
    issues_found = issues.count;
    early_exit_rate;
  } in
  
  (issues, stats)

(* Extract issues as array for external consumption *)
let extract_issues issues =
  let positions = Array.make issues.count 0 in
  let rules = Array.make issues.count 0 in
  
  for i = 0 to issues.count - 1 do
    positions.(i) <- Int32.to_int (Array1.unsafe_get issues.positions i);
    rules.(i) <- Array1.unsafe_get issues.rule_codes i
  done;
  
  (positions, rules)