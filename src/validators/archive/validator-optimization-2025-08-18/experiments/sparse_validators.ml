(* TRACK 3: SPARSE CANDIDATE LISTS - O(k) VALIDATION *)
(* Expert: "If candidate density is modest, this alone pushes <1ms in OCaml" *)

open Bigarray

(* Sparse candidate storage *)
type candidates = {
  (* Quote positions *)
  quotes: (int, int_elt, c_layout) Array1.t;
  mutable quote_count: int;
  
  (* Hyphen positions *)
  hyphens: (int, int_elt, c_layout) Array1.t;
  mutable hyphen_count: int;
  
  (* Period positions *)
  periods: (int, int_elt, c_layout) Array1.t;
  mutable period_count: int;
  
  (* Tab positions *)
  tabs: (int, int_elt, c_layout) Array1.t;
  mutable tab_count: int;
  
  (* Brace positions *)
  left_braces: (int, int_elt, c_layout) Array1.t;
  mutable left_brace_count: int;
  right_braces: (int, int_elt, c_layout) Array1.t;
  mutable right_brace_count: int;
}

(* Issue tracking *)
type issue_buffer = {
  positions: (int, int_elt, c_layout) Array1.t;
  rule_ids: (int, int8_unsigned_elt, c_layout) Array1.t;
  mutable count: int;
}

let create_candidates capacity = {
  quotes = Array1.create int c_layout capacity;
  quote_count = 0;
  hyphens = Array1.create int c_layout capacity;
  hyphen_count = 0;
  periods = Array1.create int c_layout capacity;
  period_count = 0;
  tabs = Array1.create int c_layout capacity;
  tab_count = 0;
  left_braces = Array1.create int c_layout capacity;
  left_brace_count = 0;
  right_braces = Array1.create int c_layout capacity;
  right_brace_count = 0;
}

let create_issue_buffer capacity = {
  positions = Array1.create int c_layout capacity;
  rule_ids = Array1.create int8_unsigned c_layout capacity;
  count = 0;
}

(* Rule IDs *)
let rule_quote = 1
let rule_double_hyphen = 2
let rule_triple_hyphen = 3
let rule_ellipsis = 5
let rule_tab = 6
let rule_unmatched_brace = 101

(* CRITICAL: Build candidate lists during tokenization - O(n) once *)
let build_candidates_from_tokens tokens =
  let n = List.length tokens in
  let candidates = create_candidates (n / 10) in (* Estimate 10% are interesting *)
  
  List.iteri (fun i tok ->
    let open Validator_core_fixed in
    match tok.token with
    | TChar (uc, Other) ->
        let code = Uchar.to_int uc in
        if code = 34 then begin (* Quote *)
          Array1.unsafe_set candidates.quotes candidates.quote_count i;
          candidates.quote_count <- candidates.quote_count + 1
        end else if code = 45 then begin (* Hyphen *)
          Array1.unsafe_set candidates.hyphens candidates.hyphen_count i;
          candidates.hyphen_count <- candidates.hyphen_count + 1
        end else if code = 46 then begin (* Period *)
          Array1.unsafe_set candidates.periods candidates.period_count i;
          candidates.period_count <- candidates.period_count + 1
        end
    | TChar (uc, Space) ->
        let code = Uchar.to_int uc in
        if code = 9 then begin (* Tab *)
          Array1.unsafe_set candidates.tabs candidates.tab_count i;
          candidates.tab_count <- candidates.tab_count + 1
        end
    | TChar (uc, BeginGroup) ->
        Array1.unsafe_set candidates.left_braces candidates.left_brace_count i;
        candidates.left_brace_count <- candidates.left_brace_count + 1
    | TChar (uc, EndGroup) ->
        Array1.unsafe_set candidates.right_braces candidates.right_brace_count i;
        candidates.right_brace_count <- candidates.right_brace_count + 1
    | _ -> ()
  ) tokens;
  
  candidates

(* SPARSE VALIDATORS: O(k) not O(n) *)

(* Quote validator: O(quote_count) *)
let[@inline] validate_quotes candidates issues =
  for i = 0 to candidates.quote_count - 1 do
    let pos = Array1.unsafe_get candidates.quotes i in
    Array1.unsafe_set issues.positions issues.count pos;
    Array1.unsafe_set issues.rule_ids issues.count rule_quote;
    issues.count <- issues.count + 1
  done

(* Hyphen validator: O(hyphen_count) *)
let[@inline] validate_hyphens candidates issues =
  (* Check for consecutive hyphens *)
  for i = 0 to candidates.hyphen_count - 2 do
    let pos1 = Array1.unsafe_get candidates.hyphens i in
    let pos2 = Array1.unsafe_get candidates.hyphens (i + 1) in
    
    if pos2 = pos1 + 1 then begin
      (* Double hyphen found *)
      if i + 2 < candidates.hyphen_count then begin
        let pos3 = Array1.unsafe_get candidates.hyphens (i + 2) in
        if pos3 = pos2 + 1 then begin
          (* Triple hyphen *)
          Array1.unsafe_set issues.positions issues.count pos1;
          Array1.unsafe_set issues.rule_ids issues.count rule_triple_hyphen;
          issues.count <- issues.count + 1
        end else begin
          (* Just double hyphen *)
          Array1.unsafe_set issues.positions issues.count pos1;
          Array1.unsafe_set issues.rule_ids issues.count rule_double_hyphen;
          issues.count <- issues.count + 1
        end
      end else begin
        (* Double hyphen at end *)
        Array1.unsafe_set issues.positions issues.count pos1;
        Array1.unsafe_set issues.rule_ids issues.count rule_double_hyphen;
        issues.count <- issues.count + 1
      end
    end
  done

(* Period validator: O(period_count) *)
let[@inline] validate_periods candidates issues =
  (* Check for three consecutive periods *)
  for i = 0 to candidates.period_count - 3 do
    let pos1 = Array1.unsafe_get candidates.periods i in
    let pos2 = Array1.unsafe_get candidates.periods (i + 1) in
    let pos3 = Array1.unsafe_get candidates.periods (i + 2) in
    
    if pos2 = pos1 + 1 && pos3 = pos2 + 1 then begin
      (* Ellipsis found *)
      Array1.unsafe_set issues.positions issues.count pos1;
      Array1.unsafe_set issues.rule_ids issues.count rule_ellipsis;
      issues.count <- issues.count + 1
    end
  done

(* Tab validator: O(tab_count) *)
let[@inline] validate_tabs candidates issues =
  for i = 0 to candidates.tab_count - 1 do
    let pos = Array1.unsafe_get candidates.tabs i in
    Array1.unsafe_set issues.positions issues.count pos;
    Array1.unsafe_set issues.rule_ids issues.count rule_tab;
    issues.count <- issues.count + 1
  done

(* Brace validator: O(brace_count) *)
let[@inline] validate_braces candidates issues =
  let depth = ref 0 in
  let all_positions = ref [] in
  
  (* Collect all brace positions *)
  for i = 0 to candidates.left_brace_count - 1 do
    let pos = Array1.unsafe_get candidates.left_braces i in
    all_positions := (pos, true) :: !all_positions
  done;
  for i = 0 to candidates.right_brace_count - 1 do
    let pos = Array1.unsafe_get candidates.right_braces i in
    all_positions := (pos, false) :: !all_positions
  done;
  
  (* Sort by position *)
  let sorted = List.sort (fun (p1, _) (p2, _) -> compare p1 p2) !all_positions in
  
  (* Check balance *)
  List.iter (fun (pos, is_left) ->
    if is_left then
      incr depth
    else begin
      if !depth = 0 then begin
        (* Unmatched right brace *)
        Array1.unsafe_set issues.positions issues.count pos;
        Array1.unsafe_set issues.rule_ids issues.count rule_unmatched_brace;
        issues.count <- issues.count + 1
      end else
        decr depth
    end
  ) sorted;
  
  (* Report unclosed left braces *)
  if !depth > 0 then begin
    (* Find unclosed positions - simplified *)
    for _ = 1 to !depth do
      Array1.unsafe_set issues.positions issues.count 0;
      Array1.unsafe_set issues.rule_ids issues.count rule_unmatched_brace;
      issues.count <- issues.count + 1
    done
  end

(* MAIN SPARSE VALIDATION: O(k) total where k = sum of all candidate counts *)
let validate_sparse candidates =
  let issues = create_issue_buffer 65536 in
  
  validate_quotes candidates issues;
  validate_hyphens candidates issues;
  validate_periods candidates issues;
  validate_tabs candidates issues;
  validate_braces candidates issues;
  
  issues

(* Benchmark function *)
let bench_sparse tokens =
  let n = List.length tokens in
  
  (* Build candidates once - O(n) *)
  let t0 = Unix.gettimeofday () in
  let candidates = build_candidates_from_tokens tokens in
  let t1 = Unix.gettimeofday () in
  let build_time = (t1 -. t0) *. 1000.0 in
  
  (* Print candidate density *)
  Printf.printf "Candidate density analysis (%d tokens):\n" n;
  Printf.printf "  Quotes:      %d (%.1f%%)\n" candidates.quote_count 
    (100.0 *. float candidates.quote_count /. float n);
  Printf.printf "  Hyphens:     %d (%.1f%%)\n" candidates.hyphen_count
    (100.0 *. float candidates.hyphen_count /. float n);
  Printf.printf "  Periods:     %d (%.1f%%)\n" candidates.period_count
    (100.0 *. float candidates.period_count /. float n);
  Printf.printf "  Tabs:        %d (%.1f%%)\n" candidates.tab_count
    (100.0 *. float candidates.tab_count /. float n);
  Printf.printf "  Build time:  %.3fms\n" build_time;
  
  let total_candidates = candidates.quote_count + candidates.hyphen_count + 
                        candidates.period_count + candidates.tab_count in
  Printf.printf "  Total candidates: %d (%.1f%% of tokens)\n" total_candidates
    (100.0 *. float total_candidates /. float n);
  
  (* Warm up *)
  for _ = 1 to 10 do
    ignore (validate_sparse candidates)
  done;
  
  (* Benchmark validation only - O(k) *)
  let times = ref [] in
  for _ = 1 to 100 do
    let t0 = Unix.gettimeofday () in
    let issues = validate_sparse candidates in
    let t1 = Unix.gettimeofday () in
    times := (t1 -. t0) *. 1000.0 :: !times
  done;
  
  let sorted = List.sort compare !times in
  let p99 = List.nth sorted 98 in
  let p95 = List.nth sorted 94 in
  let p50 = List.nth sorted 49 in
  let mean = (List.fold_left (+.) 0.0 sorted) /. 100.0 in
  
  Printf.printf "\nSparse validation performance:\n";
  Printf.printf "  Mean: %.3fms\n" mean;
  Printf.printf "  P50:  %.3fms\n" p50;
  Printf.printf "  P95:  %.3fms\n" p95;
  Printf.printf "  P99:  %.3fms\n" p99;
  
  let scale = 276000.0 /. float n in
  Printf.printf "\nEstimated for 276K tokens:\n";
  Printf.printf "  P99: %.3fms\n" (p99 *. scale);
  
  let final_result = p99 *. scale in
  if final_result < 1.0 then
    Printf.printf "✅ SUCCESS: <1ms sparse validation achieved!\n"
  else
    Printf.printf "⚠️ %.3fms - close but not quite <1ms\n" final_result;
  
  Printf.printf "\nTotal with build: %.3fms + %.3fms = %.3fms\n" 
    (build_time *. scale) final_result ((build_time +. p99) *. scale);
  
  final_result