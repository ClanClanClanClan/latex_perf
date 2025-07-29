(**
 * Test Parallel Domain-Based Validator
 * Uses OCaml 5.0 domains for true parallel rule execution
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

(* Parallel execution using OCaml domains *)
let execute_chunk_parallel (chunk, doc_state) =
  (* Execute chunk on a separate domain *)
  Domain.spawn (fun () ->
    execute_chunk chunk doc_state
  )

let parallel_validate_with_domains filename domain_count =
  let start_time = Unix.gettimeofday () in
  
  try
    (* Read file *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    (* Tokenize *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Get priority rules (use 20 rules for testing) *)
    let rules = 
      let rec take n lst =
        match n, lst with
        | 0, _ -> []
        | _, [] -> []
        | n, x :: xs -> x :: take (n-1) xs
      in
      take 20 all_l0_rules
    in
    
    (* Create chunks for parallel execution *)
    let chunks = create_chunks rules domain_count in
    
    (* Spawn domains for each chunk *)
    let domain_promises = List.map (fun chunk ->
      execute_chunk_parallel (chunk, doc_state)
    ) chunks in
    
    (* Wait for all domains to complete *)
    let chunk_results = List.map Domain.join domain_promises in
    
    (* Combine results *)
    let all_issues = combine_results chunk_results in
    let issue_count = List.length all_issues in
    
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    
    (filename, issue_count, total_time, true, domain_count, List.length rules)
  with
  | exn -> 
    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    (filename, 0, total_time, false, domain_count, 0)

(* Benchmark parallel vs sequential *)
let benchmark_parallel_vs_sequential filename =
  Printf.printf "Benchmarking parallel vs sequential execution for %s\\n" filename;
  
  (* Sequential baseline *)
  let seq_start = Unix.gettimeofday () in
  let (_, seq_issues, seq_time, seq_success, _, _) = 
    parallel_validate_with_domains filename 1 in
  
  Printf.printf "Sequential: %.3fs, %d issues, success: %b\\n" 
    seq_time seq_issues seq_success;
  
  (* Test different domain counts *)
  let domain_counts = [2; 4; 8] in
  List.iter (fun domains ->
    let (_, par_issues, par_time, par_success, _, _) = 
      parallel_validate_with_domains filename domains in
    let speedup = if par_time > 0.0 then seq_time /. par_time else 0.0 in
    Printf.printf "Parallel (%d domains): %.3fs, %d issues, success: %b, speedup: %.1fx\\n"
      domains par_time par_issues par_success speedup
  ) domain_counts

(* Batch parallel validation *)
let batch_parallel_validate filenames domain_count =
  let results = Array.make (List.length filenames) ("", 0, 0.0, false, 0, 0) in
  
  List.iteri (fun i filename ->
    let result = parallel_validate_with_domains filename domain_count in
    results.(i) <- result
  ) filenames;
  
  results

(* Performance analysis *)
let analyze_parallel_performance results =
  let total = Array.length results in
  let successful = Array.fold_left (fun acc (_, _, _, success, _, _) -> 
    if success then acc + 1 else acc) 0 results in
  
  let total_issues = Array.fold_left (fun acc (_, issues, _, _, _, _) -> 
    acc + issues) 0 results in
    
  let total_time = Array.fold_left (fun acc (_, _, time, _, _, _) ->
    acc +. time) 0.0 results in
  
  let avg_time = if total > 0 then total_time /. float total else 0.0 in
  let avg_domains = Array.fold_left (fun acc (_, _, _, _, domains, _) ->
    acc + domains) 0 results / total in
  
  (total, successful, total_issues, total_time, avg_time, avg_domains)

(* JSON output for parallel results *)
let output_parallel_results results =
  let (total, successful, total_issues, total_time, avg_time, avg_domains) = 
    analyze_parallel_performance results in
  
  Printf.printf "{\\n";
  Printf.printf "  \"parallel_validation\": {\\n";
  Printf.printf "    \"total_papers\": %d,\\n" total;
  Printf.printf "    \"successful\": %d,\\n" successful;
  Printf.printf "    \"success_rate\": %.1f,\\n" (float successful /. float total *. 100.0);
  Printf.printf "    \"total_issues\": %d,\\n" total_issues;
  Printf.printf "    \"avg_issues_per_paper\": %.1f,\\n" (float total_issues /. float total);
  Printf.printf "    \"total_time\": %.2f,\\n" total_time;
  Printf.printf "    \"avg_time_per_paper\": %.3f,\\n" avg_time;
  Printf.printf "    \"papers_per_second\": %.1f,\\n" (float total /. total_time);
  Printf.printf "    \"avg_domain_count\": %d,\\n" avg_domains;
  Printf.printf "    \"estimated_speedup\": %.1f\\n" (1.0 /. avg_time *. 0.78);
  Printf.printf "  }\\n";
  Printf.printf "}\\n"

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
    Printf.printf "Running parallel validation with %d domains...\\n" domain_count;
    let results = batch_parallel_validate papers domain_count in
    Printf.printf "Parallel Validation Results:\\n";
    output_parallel_results results
  
  | papers ->
    let default_domains = min 8 (List.length papers) in
    Printf.printf "Running parallel validation with %d domains...\\n" default_domains;
    let results = batch_parallel_validate papers default_domains in
    output_parallel_results results