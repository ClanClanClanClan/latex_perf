(**
 * Document-Parallel Enterprise Validator
 * Correct implementation that parallelizes document processing
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

(* Get priority rules for performance *)
let get_priority_rules count =
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take count all_l0_rules

(* Process a single document - this is what we parallelize *)
let process_document_sequential filename all_rules =
  try
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Use all rules on each document *)
    let issues = execute_rules_bucketed all_rules doc_state in
    (filename, List.length issues, true)
  with
  | exn -> (filename, 0, false)

(* Split documents into chunks for parallel processing *)
let chunk_documents documents num_chunks =
  let total = List.length documents in
  let chunk_size = max 1 (total / num_chunks) in
  
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
  
  let rec create_chunks docs acc =
    if docs = [] then List.rev acc
    else
      let chunk = take chunk_size docs in
      let remaining = drop chunk_size docs in
      create_chunks remaining (chunk :: acc)
  in
  
  create_chunks documents []

(* Process a chunk of documents *)
let process_document_chunk documents all_rules =
  List.map (fun doc -> process_document_sequential doc all_rules) documents

(* Parallel document processing with domains *)
let process_documents_parallel documents num_domains =
  let start_time = Unix.gettimeofday () in
  
  (* Get rules to use - limit to 20 for performance *)
  let all_rules = get_priority_rules 20 in
  
  (* Split documents into chunks *)
  let doc_chunks = chunk_documents documents num_domains in
  
  (* Process each chunk in parallel *)
  let domain_promises = List.map (fun chunk ->
    Domain.spawn (fun () ->
      process_document_chunk chunk all_rules
    )
  ) doc_chunks in
  
  (* Wait for all domains and combine results *)
  let chunk_results = List.map Domain.join domain_promises in
  let all_results = List.flatten chunk_results in
  
  let end_time = Unix.gettimeofday () in
  let total_time = end_time -. start_time in
  
  (* Analyze results *)
  let total = List.length all_results in
  let successful = List.fold_left (fun acc (_, _, success) ->
    if success then acc + 1 else acc) 0 all_results in
  let total_issues = List.fold_left (fun acc (_, issues, _) ->
    acc + issues) 0 all_results in
  
  (total, successful, total_issues, total_time, num_domains)

(* Sequential baseline for comparison *)
let process_documents_sequential documents =
  let start_time = Unix.gettimeofday () in
  
  let all_rules = get_priority_rules 20 in
  let results = List.map (fun doc -> 
    process_document_sequential doc all_rules
  ) documents in
  
  let end_time = Unix.gettimeofday () in
  let total_time = end_time -. start_time in
  
  (* Analyze results *)
  let total = List.length results in
  let successful = List.fold_left (fun acc (_, _, success) ->
    if success then acc + 1 else acc) 0 results in
  let total_issues = List.fold_left (fun acc (_, issues, _) ->
    acc + issues) 0 results in
  
  (total, successful, total_issues, total_time, 1)

(* Benchmark parallel vs sequential *)
let benchmark_document_parallel documents =
  Printf.printf "=== Document-Parallel Validator Benchmark ===\n";
  Printf.printf "Testing with %d documents\n\n" (List.length documents);
  
  (* Sequential baseline *)
  Printf.printf "Running sequential baseline...\n";
  let (seq_total, seq_success, seq_issues, seq_time, _) = 
    process_documents_sequential documents in
  
  Printf.printf "Sequential Results:\n";
  Printf.printf "  Papers: %d, Successful: %d (%.1f%%)\n" 
    seq_total seq_success (float seq_success /. float seq_total *. 100.0);
  Printf.printf "  Total issues: %d\n" seq_issues;
  Printf.printf "  Time: %.3f seconds\n" seq_time;
  Printf.printf "  Papers/second: %.1f\n\n" (float seq_total /. seq_time);
  
  (* Test different domain counts *)
  let domain_counts = [2; 4; 8] in
  let domain_counts = List.filter (fun d -> d <= List.length documents) domain_counts in
  
  List.iter (fun domains ->
    Printf.printf "Running parallel with %d domains...\n" domains;
    let (par_total, par_success, par_issues, par_time, _) = 
      process_documents_parallel documents domains in
    
    let speedup = if par_time > 0.0 then seq_time /. par_time else 0.0 in
    
    Printf.printf "Parallel Results (%d domains):\n" domains;
    Printf.printf "  Papers: %d, Successful: %d (%.1f%%)\n" 
      par_total par_success (float par_success /. float par_total *. 100.0);
    Printf.printf "  Total issues: %d\n" par_issues;
    Printf.printf "  Time: %.3f seconds\n" par_time;
    Printf.printf "  Papers/second: %.1f\n" (float par_total /. par_time);
    Printf.printf "  Speedup: %.2fx\n\n" speedup;
    
    (* Verify correctness *)
    if par_issues <> seq_issues then
      Printf.printf "  WARNING: Issue count mismatch! Sequential: %d, Parallel: %d\n\n"
        seq_issues par_issues
  ) domain_counts

(* Find LaTeX files in directory *)
let find_tex_files dir max_files =
  let files = ref [] in
  let count = ref 0 in
  
  let rec scan_dir path =
    if !count >= max_files then ()
    else
      let entries = Sys.readdir path in
      Array.iter (fun entry ->
        if !count >= max_files then ()
        else
          let full_path = Filename.concat path entry in
          if Sys.is_directory full_path then
            scan_dir full_path
          else if Filename.check_suffix entry ".tex" then begin
            files := full_path :: !files;
            incr count
          end
      ) entries
  in
  
  (try scan_dir dir with 
   | Sys_error msg -> Printf.eprintf "Error scanning directory %s: %s\n" dir msg
   | exn -> Printf.eprintf "Unexpected error scanning directory %s: %s\n" dir (Printexc.to_string exn));
  List.rev !files

(* Output results in JSON format *)
let output_json_results total successful issues time domains =
  Printf.printf "{\n";
  Printf.printf "  \"document_parallel_validation\": {\n";
  Printf.printf "    \"total_papers\": %d,\n" total;
  Printf.printf "    \"successful\": %d,\n" successful;
  Printf.printf "    \"success_rate\": %.1f,\n" (float successful /. float total *. 100.0);
  Printf.printf "    \"total_issues\": %d,\n" issues;
  Printf.printf "    \"avg_issues_per_paper\": %.1f,\n" (float issues /. float total);
  Printf.printf "    \"total_time\": %.2f,\n" time;
  Printf.printf "    \"avg_time_per_paper\": %.3f,\n" (time /. float total);
  Printf.printf "    \"papers_per_second\": %.1f,\n" (float total /. time);
  Printf.printf "    \"domains_used\": %d,\n" domains;
  Printf.printf "    \"rules_used\": 20\n";
  Printf.printf "  }\n";
  Printf.printf "}\n"

(* Main execution *)
let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    Printf.eprintf "       %s --benchmark <papers...>\n" Sys.argv.(0);
    Printf.eprintf "       %s --corpus <directory> <max_files>\n" Sys.argv.(0);
    Printf.eprintf "       %s --domains <count> <papers...>\n" Sys.argv.(0);
    exit 1
  end;
  
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  
  match args with
  | "--benchmark" :: papers when papers <> [] ->
    benchmark_document_parallel papers
  
  | "--corpus" :: dir :: max_str :: [] ->
    let max_files = int_of_string max_str in
    Printf.printf "Finding up to %d .tex files in %s...\n" max_files dir;
    let papers = find_tex_files dir max_files in
    Printf.printf "Found %d papers\n\n" (List.length papers);
    if papers <> [] then
      benchmark_document_parallel papers
    else
      Printf.printf "No .tex files found\n"
  
  | "--domains" :: domain_str :: papers when papers <> [] ->
    let domains = int_of_string domain_str in
    let (total, successful, issues, time, _) = 
      process_documents_parallel papers domains in
    output_json_results total successful issues time domains
  
  | papers when papers <> [] ->
    (* Default: use optimal domain count *)
    let domains = min 8 (max 2 (List.length papers / 2)) in
    let (total, successful, issues, time, _) = 
      process_documents_parallel papers domains in
    output_json_results total successful issues time domains
  
  | _ ->
    Printf.eprintf "Invalid arguments\n";
    exit 1