(**
 * Rule Performance Profiler
 * Identifies which rules are causing performance bottlenecks
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

(* Profile a single rule on a document *)
let profile_single_rule rule doc_state =
  let start_time = Unix.gettimeofday () in
  let issues = 
    try
      execute_rule rule doc_state
    with
    | exn -> []
  in
  let end_time = Unix.gettimeofday () in
  let elapsed = end_time -. start_time in
  (chars_to_string rule.id, elapsed, List.length issues)

(* Profile all rules on a single document *)
let profile_rules_on_document filename =
  try
    (* Read file *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = 
      if len > 50000 then
        really_input_string ic 50000  (* Limit to 50KB for profiling *)
      else
        really_input_string ic len
    in
    close_in ic;
    
    (* Create document state *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Profile each rule *)
    let results = List.map (fun rule ->
      profile_single_rule rule doc_state
    ) all_l0_rules in
    
    (* Sort by time (slowest first) *)
    let sorted = List.sort (fun (_, t1, _) (_, t2, _) ->
      compare t2 t1
    ) results in
    
    Some (filename, sorted, len)
  with
  | exn -> None

(* Aggregate profiling results *)
type rule_stats = {
  rule_id: string;
  total_time: float;
  avg_time: float;
  max_time: float;
  min_time: float;
  total_issues: int;
  execution_count: int;
}

let create_stats_table () = Hashtbl.create 100

let update_stats stats_table rule_id time issues =
  let stats = 
    try Hashtbl.find stats_table rule_id
    with Not_found -> {
      rule_id = rule_id;
      total_time = 0.0;
      avg_time = 0.0;
      max_time = 0.0;
      min_time = 999999.0;
      total_issues = 0;
      execution_count = 0;
    }
  in
  let new_stats = {
    rule_id = rule_id;
    total_time = stats.total_time +. time;
    avg_time = 0.0;  (* Will calculate later *)
    max_time = max stats.max_time time;
    min_time = min stats.min_time time;
    total_issues = stats.total_issues + issues;
    execution_count = stats.execution_count + 1;
  } in
  Hashtbl.replace stats_table rule_id new_stats

(* Profile multiple documents *)
let profile_corpus documents =
  let stats_table = create_stats_table () in
  let successful_docs = ref 0 in
  let total_bytes = ref 0 in
  
  Printf.printf "Profiling %d documents...\n\n" (List.length documents);
  
  List.iteri (fun i doc ->
    Printf.printf "\rProcessing document %d/%d..." (i + 1) (List.length documents);
    flush stdout;
    
    match profile_rules_on_document doc with
    | Some (filename, results, bytes) ->
        incr successful_docs;
        total_bytes := !total_bytes + bytes;
        List.iter (fun (rule_id, time, issues) ->
          update_stats stats_table rule_id time issues
        ) results
    | None -> ()
  ) documents;
  
  Printf.printf "\n\nProcessed %d/%d documents successfully\n" 
    !successful_docs (List.length documents);
  Printf.printf "Total bytes processed: %d\n\n" !total_bytes;
  
  (* Calculate averages and convert to list *)
  let final_stats = Hashtbl.fold (fun _ stats acc ->
    let avg_time = stats.total_time /. float stats.execution_count in
    { stats with avg_time = avg_time } :: acc
  ) stats_table [] in
  
  (* Sort by total time (slowest first) *)
  List.sort (fun s1 s2 -> compare s2.total_time s1.total_time) final_stats

(* Output profiling results *)
let output_profiling_results stats =
  Printf.printf "Rule Performance Profile\n";
  Printf.printf "========================\n\n";
  
  Printf.printf "%-12s %10s %10s %10s %10s %8s %8s\n"
    "Rule ID" "Total (s)" "Avg (ms)" "Max (ms)" "Min (ms)" "Issues" "Calls";
  Printf.printf "%s\n" (String.make 80 '-');
  
  List.iter (fun s ->
    Printf.printf "%-12s %10.3f %10.1f %10.1f %10.1f %8d %8d\n"
      s.rule_id
      s.total_time
      (s.avg_time *. 1000.0)
      (s.max_time *. 1000.0)
      (s.min_time *. 1000.0)
      s.total_issues
      s.execution_count
  ) stats;
  
  Printf.printf "\n";
  
  (* Summary statistics *)
  let total_time = List.fold_left (fun acc s -> acc +. s.total_time) 0.0 stats in
  let total_issues = List.fold_left (fun acc s -> acc + s.total_issues) 0 stats in
  
  Printf.printf "Summary:\n";
  Printf.printf "--------\n";
  Printf.printf "Total execution time: %.3f seconds\n" total_time;
  Printf.printf "Total issues found: %d\n" total_issues;
  Printf.printf "Number of rules: %d\n" (List.length stats);
  
  (* Identify problematic rules *)
  Printf.printf "\nSlowest Rules (>100ms average):\n";
  Printf.printf "--------------------------------\n";
  List.iter (fun s ->
    if s.avg_time > 0.1 then
      Printf.printf "%s: %.1fms average (%.3fs total)\n" 
        s.rule_id (s.avg_time *. 1000.0) s.total_time
  ) stats;
  
  Printf.printf "\nFastest Rules (<1ms average):\n";
  Printf.printf "------------------------------\n";
  let fast_rules = List.filter (fun s -> s.avg_time < 0.001) stats in
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  List.iter (fun s ->
    Printf.printf "%s: %.2fms average\n" s.rule_id (s.avg_time *. 1000.0)
  ) (take 10 fast_rules)

(* Find tex files *)
let find_tex_files dir max_files =
  let files = ref [] in
  let count = ref 0 in
  
  let rec scan_dir path =
    if !count >= max_files then ()
    else
      try
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
      with _ -> ()
  in
  
  scan_dir dir;
  List.rev !files

(* Main execution *)
let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    Printf.eprintf "       %s --corpus <directory> <count>\n" Sys.argv.(0);
    exit 1
  end;
  
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  
  let documents = match args with
  | "--corpus" :: dir :: count_str :: [] ->
      let max_files = int_of_string count_str in
      Printf.printf "Searching for up to %d .tex files in %s...\n" max_files dir;
      let papers = find_tex_files dir max_files in
      Printf.printf "Found %d papers\n\n" (List.length papers);
      papers
  | docs -> docs
  in
  
  if documents = [] then
    Printf.printf "No documents to profile\n"
  else
    let stats = profile_corpus documents in
    output_profiling_results stats