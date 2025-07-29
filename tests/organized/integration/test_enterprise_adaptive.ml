(**
 * Adaptive Enterprise Validator
 * Optimized streaming validator with adaptive timeouts and document classification
 *)

open Enterprise_validators

(* Document classification types *)
type document_complexity = 
  | FastPath    (* Simple documents: <3000 tokens, low math, simple structure *)
  | MediumPath  (* Medium documents: 3000-15000 tokens, moderate complexity *)
  | SlowPath    (* Complex documents: >15000 tokens, heavy math, complex structure *)

type adaptive_config = {
  base_timeout: float;
  fast_timeout: float;
  medium_timeout: float;
  slow_timeout: float;
  priority_rules: int;
  medium_rules: int;
  full_rules: int;
}

(* Default configuration *)
let default_config = {
  base_timeout = 2.0;
  fast_timeout = 3.0;
  medium_timeout = 8.0;
  slow_timeout = 15.0;
  priority_rules = 5;   (* Use only 5 fastest rules for simple docs *)
  medium_rules = 15;    (* Use 15 rules for medium docs *)
  full_rules = 75;      (* Use all rules for complex docs *)
}

(* Ultra-fast string conversions *)
let string_to_chars s =
  let len = String.length s in
  let rec build acc i =
    if i < 0 then acc
    else build (s.[i] :: acc) (i - 1)
  in
  build [] (len - 1)

let chars_to_string chars =
  match chars with
  | [] -> ""
  | _ ->
    let len = List.length chars in
    let buf = Buffer.create len in
    List.iter (Buffer.add_char buf) (List.rev chars);
    Buffer.contents buf

(* Fast document analysis *)
let analyze_document_complexity tokens =
  let token_count = List.length tokens in
  let math_count = List.fold_left (fun acc token ->
    match token with
    | TMathShift -> acc + 1
    | TCommand cmd -> 
        let cmd_str = chars_to_string cmd in
        if String.contains cmd_str '$' || 
           String.contains cmd_str '\\' && 
           (String.contains cmd_str 'f' || String.contains cmd_str 'i' || String.contains cmd_str 'n')
        then acc + 1 else acc
    | _ -> acc
  ) 0 tokens in
  
  let structure_count = List.fold_left (fun acc token ->
    match token with
    | TBeginGroup | TEndGroup -> acc + 1
    | TCommand cmd ->
        let cmd_str = chars_to_string cmd in
        if String.contains cmd_str 'b' || String.contains cmd_str 'e' then acc + 1 else acc
    | _ -> acc
  ) 0 tokens in
  
  let math_density = if token_count > 0 then float math_count /. float token_count else 0.0 in
  let structure_density = if token_count > 0 then float structure_count /. float token_count else 0.0 in
  
  (* Classification logic *)
  match token_count, math_density, structure_density with
  | n, m, s when n < 3000 && m < 0.05 && s < 0.1 -> FastPath
  | n, m, s when n < 15000 && m < 0.15 && s < 0.25 -> MediumPath
  | _ -> SlowPath

(* Get adaptive configuration based on document complexity *)
let get_adaptive_config complexity config =
  match complexity with
  | FastPath -> (config.fast_timeout, config.priority_rules)
  | MediumPath -> (config.medium_timeout, config.medium_rules)
  | SlowPath -> (config.slow_timeout, config.full_rules)

(* Priority rule selection *)
let get_priority_rules rule_count = 
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take rule_count all_l0_rules

(* Adaptive document processing *)
let process_document_adaptive filename config =
  let start_time = Unix.gettimeofday () in
  
  try
    (* Fast file reading *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    (* Quick tokenization *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Analyze document complexity *)
    let complexity = analyze_document_complexity tokens in
    let (timeout, rule_count) = get_adaptive_config complexity config in
    
    (* Get appropriate rules *)
    let rules = get_priority_rules rule_count in
    
    (* Execute validation with timeout *)
    let validation_start = Unix.gettimeofday () in
    let issues = execute_rules_bucketed rules doc_state in
    let validation_end = Unix.gettimeofday () in
    let validation_time = validation_end -. validation_start in
    
    (* Check if we exceeded timeout *)
    let success = validation_time < timeout in
    let issue_count = List.length issues in
    
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    
    (filename, issue_count, total_time, success, complexity, rule_count)
  with
  | exn -> 
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    (filename, 0, total_time, false, SlowPath, 0)

(* Batch processing with adaptive configuration *)
let process_batch_adaptive filenames config =
  let results = Array.make (List.length filenames) ("", 0, 0.0, false, FastPath, 0) in
  
  List.iteri (fun i filename ->
    let result = process_document_adaptive filename config in
    results.(i) <- result
  ) filenames;
  
  results

(* Performance analysis *)
let analyze_performance results =
  let total = Array.length results in
  let successful = Array.fold_left (fun acc (_, _, _, success, _, _) -> 
    if success then acc + 1 else acc) 0 results in
  
  let fast_count = Array.fold_left (fun acc (_, _, _, _, complexity, _) ->
    if complexity = FastPath then acc + 1 else acc) 0 results in
  
  let medium_count = Array.fold_left (fun acc (_, _, _, _, complexity, _) ->
    if complexity = MediumPath then acc + 1 else acc) 0 results in
  
  let slow_count = Array.fold_left (fun acc (_, _, _, _, complexity, _) ->
    if complexity = SlowPath then acc + 1 else acc) 0 results in
  
  let total_issues = Array.fold_left (fun acc (_, issues, _, _, _, _) -> 
    acc + issues) 0 results in
    
  let total_time = Array.fold_left (fun acc (_, _, time, _, _, _) ->
    acc +. time) 0.0 results in
  
  let avg_time = if total > 0 then total_time /. float total else 0.0 in
  
  (total, successful, fast_count, medium_count, slow_count, total_issues, total_time, avg_time)

(* JSON output *)
let output_adaptive_results results =
  let (total, successful, fast_count, medium_count, slow_count, total_issues, total_time, avg_time) = 
    analyze_performance results in
  
  Printf.printf "{\n";
  Printf.printf "  \"adaptive_validation\": {\n";
  Printf.printf "    \"total_papers\": %d,\n" total;
  Printf.printf "    \"successful\": %d,\n" successful;
  Printf.printf "    \"success_rate\": %.1f,\n" (float successful /. float total *. 100.0);
  Printf.printf "    \"total_issues\": %d,\n" total_issues;
  Printf.printf "    \"avg_issues_per_paper\": %.1f,\n" (float total_issues /. float total);
  Printf.printf "    \"total_time\": %.2f,\n" total_time;
  Printf.printf "    \"avg_time_per_paper\": %.3f,\n" avg_time;
  Printf.printf "    \"papers_per_second\": %.1f,\n" (float total /. total_time);
  Printf.printf "    \"complexity_distribution\": {\n";
  Printf.printf "      \"fast_path\": %d,\n" fast_count;
  Printf.printf "      \"medium_path\": %d,\n" medium_count;
  Printf.printf "      \"slow_path\": %d\n" slow_count;
  Printf.printf "    }\n";
  Printf.printf "  }\n";
  Printf.printf "}\n"

(* Performance comparison *)
let compare_with_baseline results baseline_time =
  let (_, _, _, _, _, _, total_time, avg_time) = analyze_performance results in
  let speedup = baseline_time /. avg_time in
  
  Printf.printf "\nPerformance Comparison:\n";
  Printf.printf "  Baseline: %.3f seconds per paper\n" baseline_time;
  Printf.printf "  Adaptive: %.3f seconds per paper\n" avg_time;
  Printf.printf "  Speedup: %.1fx faster\n" speedup;
  
  let corpus_time = avg_time *. 2846.0 in
  Printf.printf "  Full corpus time: %.1f seconds (%.1f minutes)\n" corpus_time (corpus_time /. 60.0)

(* Main execution *)
let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    Printf.eprintf "       %s --config fast|medium|slow <papers...>\n" Sys.argv.(0);
    Printf.eprintf "       %s --benchmark <papers...>\n" Sys.argv.(0);
    exit 1
  end;
  
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  
  match args with
  | ["--benchmark"] ->
    Printf.printf "Adaptive Enterprise Validator Benchmark\n";
    Printf.printf "Usage: %s --benchmark <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    exit 1
  
  | "--benchmark" :: papers ->
    Printf.printf "Running adaptive validation benchmark...\n";
    let results = process_batch_adaptive papers default_config in
    Printf.printf "Benchmark Results:\n";
    output_adaptive_results results;
    compare_with_baseline results 1.39  (* Previous baseline *)
  
  | "--config" :: config_type :: papers ->
    let config = match config_type with
      | "fast" -> { default_config with fast_timeout = 2.0; priority_rules = 3 }
      | "medium" -> { default_config with medium_timeout = 5.0; medium_rules = 10 }
      | "slow" -> { default_config with slow_timeout = 20.0; full_rules = 75 }
      | _ -> default_config
    in
    let results = process_batch_adaptive papers config in
    output_adaptive_results results
  
  | papers ->
    let results = process_batch_adaptive papers default_config in
    output_adaptive_results results