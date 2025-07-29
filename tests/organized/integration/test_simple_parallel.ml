(**
 * Simple Parallel Validator Implementation
 * Uses existing enterprise validators with domain-based parallelism
 *)

open Enterprise_validators

(* String conversion utilities *)
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

(* Split rules into chunks for parallel processing *)
let split_rules_into_chunks rules num_chunks =
  let total_rules = List.length rules in
  let chunk_size = max 1 (total_rules / num_chunks) in
  
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  
  let rec drop n lst =
    match n, lst with
    | 0, _ -> lst
    | _, [] -> []
    | n, _ :: xs -> drop (n-1) xs
  in
  
  let rec create_chunks rules chunk_size acc =
    if rules = [] then List.rev acc
    else
      let chunk = take chunk_size rules in
      let remaining = drop chunk_size rules in
      create_chunks remaining chunk_size (chunk :: acc)
  in
  
  create_chunks rules chunk_size []

(* Execute a chunk of rules on a document *)
let execute_rule_chunk rules doc_state =
  execute_rules_bucketed rules doc_state

(* Parallel execution with domains *)
let execute_parallel_with_domains filename num_domains =
  let start_time = Unix.gettimeofday () in
  
  try
    (* Read file *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    (* Tokenize and create document state *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Get rules (use first 20 for testing) *)
    let rec take n lst =
      match n, lst with
      | 0, _ -> []
      | _, [] -> []
      | n, x :: xs -> x :: take (n-1) xs
    in
    let rules = take 20 all_l0_rules in
    
    (* Split rules into chunks *)
    let rule_chunks = split_rules_into_chunks rules num_domains in
    
    (* Execute each chunk in parallel using domains *)
    let domain_promises = List.map (fun chunk ->
      Domain.spawn (fun () ->
        execute_rule_chunk chunk doc_state
      )
    ) rule_chunks in
    
    (* Wait for all domains to complete and combine results *)
    let chunk_results = List.map Domain.join domain_promises in
    let all_issues = List.flatten chunk_results in
    let issue_count = List.length all_issues in
    
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    
    (filename, issue_count, total_time, true, num_domains, List.length rules)
  with
  | exn -> 
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    (filename, 0, total_time, false, num_domains, 0)

(* Sequential execution for comparison *)
let execute_sequential filename =
  let start_time = Unix.gettimeofday () in
  
  try
    (* Read file *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    (* Tokenize and create document state *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Get rules (use first 20 for testing) *)
    let rec take n lst =
      match n, lst with
      | 0, _ -> []
      | _, [] -> []
      | n, x :: xs -> x :: take (n-1) xs
    in
    let rules = take 20 all_l0_rules in
    
    (* Execute sequentially *)
    let all_issues = execute_rules_bucketed rules doc_state in
    let issue_count = List.length all_issues in
    
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    
    (filename, issue_count, total_time, true, 1, List.length rules)
  with
  | exn -> 
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    (filename, 0, total_time, false, 1, 0)

(* Benchmark parallel vs sequential *)
let benchmark_parallel_vs_sequential filename =
  Printf.printf "Benchmarking parallel vs sequential execution for %s\\n" filename;
  
  (* Sequential baseline *)
  let (_, seq_issues, seq_time, seq_success, _, seq_rules) = 
    execute_sequential filename in
  
  Printf.printf "Sequential: %.3fs, %d issues, %d rules, success: %b\\n" 
    seq_time seq_issues seq_rules seq_success;
  
  if not seq_success then begin
    Printf.printf "Sequential execution failed, skipping parallel tests\\n";
    exit 1
  end;
  
  (* Test different domain counts *)
  let domain_counts = [2; 4; 8] in
  List.iter (fun domains ->
    let (_, par_issues, par_time, par_success, _, par_rules) = 
      execute_parallel_with_domains filename domains in
    let speedup = if par_time > 0.0 then seq_time /. par_time else 0.0 in
    Printf.printf "Parallel (%d domains): %.3fs, %d issues, %d rules, success: %b, speedup: %.1fx\\n"
      domains par_time par_issues par_rules par_success speedup;
    
    (* Verify issue counts match *)
    if par_success && seq_issues <> par_issues then
      Printf.printf "  WARNING: Issue count mismatch! Sequential: %d, Parallel: %d\\n"
        seq_issues par_issues
  ) domain_counts

(* Batch parallel processing *)
let batch_process_parallel filenames num_domains =
  Printf.printf "Processing %d files with %d domains...\\n" 
    (List.length filenames) num_domains;
  
  let results = List.map (fun filename ->
    execute_parallel_with_domains filename num_domains
  ) filenames in
  
  (* Analyze results *)
  let total = List.length results in
  let successful = List.fold_left (fun acc (_, _, _, success, _, _) -> 
    if success then acc + 1 else acc) 0 results in
  let total_issues = List.fold_left (fun acc (_, issues, _, _, _, _) -> 
    acc + issues) 0 results in
  let total_time = List.fold_left (fun acc (_, _, time, _, _, _) ->
    acc +. time) 0.0 results in
  let avg_time = if total > 0 then total_time /. float total else 0.0 in
  
  Printf.printf "Results:\\n";
  Printf.printf "  Total papers: %d\\n" total;
  Printf.printf "  Successful: %d (%.1f%%)\\n" successful (float successful /. float total *. 100.0);
  Printf.printf "  Total issues: %d\\n" total_issues;
  Printf.printf "  Average issues per paper: %.1f\\n" (float total_issues /. float total);
  Printf.printf "  Total time: %.2f seconds\\n" total_time;
  Printf.printf "  Average time per paper: %.3f seconds\\n" avg_time;
  Printf.printf "  Papers per second: %.1f\\n" (float total /. total_time);
  Printf.printf "  Domains used: %d\\n" num_domains

(* Main execution *)
let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\\n" Sys.argv.(0);
    Printf.eprintf "       %s --benchmark <paper.tex>\\n" Sys.argv.(0);
    Printf.eprintf "       %s --domains <count> <papers...>\\n" Sys.argv.(0);
    exit 1
  end;
  
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  
  match args with
  | ["--benchmark"; paper] ->
    benchmark_parallel_vs_sequential paper
  
  | "--domains" :: domain_str :: papers ->
    let domain_count = int_of_string domain_str in
    batch_process_parallel papers domain_count
  
  | papers ->
    let default_domains = min 4 (max 2 (List.length papers)) in
    batch_process_parallel papers default_domains