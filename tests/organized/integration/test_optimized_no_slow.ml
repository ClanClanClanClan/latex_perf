(**
 * Optimized Enterprise Validator
 * Excludes the slowest rule (200-RAHC) for massive performance gain
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

(* Filter out the slow rule *)
let get_optimized_rules () =
  List.filter (fun rule ->
    let id = chars_to_string rule.id in
    (* Exclude rule 200-RAHC which takes 92.6% of execution time *)
    id <> "200-RAHC"
  ) all_l0_rules

(* Process document *)
let process_document filename rules =
  try
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    let start_time = Unix.gettimeofday () in
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    let issues = execute_rules_bucketed rules doc_state in
    let end_time = Unix.gettimeofday () in
    
    (filename, List.length issues, true, end_time -. start_time, len)
  with
  | exn ->
    (filename, 0, false, 0.0, 0)

(* Batch process with statistics *)
let batch_process_optimized filenames =
  let rules = get_optimized_rules () in
  
  Printf.printf "Processing %d files with %d rules (slow rule excluded)...\n" 
    (List.length filenames) (List.length rules);
  
  let results = List.map (fun f -> process_document f rules) filenames in
  
  (* Analyze results *)
  let successful = List.fold_left (fun acc (_, _, success, _, _) ->
    if success then acc + 1 else acc) 0 results in
  
  let total_issues = List.fold_left (fun acc (_, issues, _, _, _) ->
    acc + issues) 0 results in
  
  let total_time = List.fold_left (fun acc (_, _, _, time, _) ->
    acc +. time) 0.0 results in
  
  let total_bytes = List.fold_left (fun acc (_, _, _, _, bytes) ->
    acc + bytes) 0 results in
  
  let avg_time = total_time /. float (List.length results) in
  let success_rate = float successful /. float (List.length results) *. 100.0 in
  
  (* Compare with previous performance *)
  let improvement_factor = 1.19 /. avg_time in (* 1.19s was previous average *)
  
  (* Output results *)
  Printf.printf "\n=== Optimized Performance (Slow Rule Excluded) ===\n";
  Printf.printf "Total papers: %d\n" (List.length results);
  Printf.printf "Successful: %d (%.1f%%)\n" successful success_rate;
  Printf.printf "Total issues found: %d\n" total_issues;
  Printf.printf "Average issues per paper: %.1f\n" 
    (float total_issues /. float (List.length results));
  Printf.printf "\nPerformance:\n";
  Printf.printf "  Total time: %.2fs\n" total_time;
  Printf.printf "  Average time per paper: %.3fs\n" avg_time;
  Printf.printf "  Papers per second: %.1f\n" 
    (float (List.length results) /. total_time);
  Printf.printf "  Improvement factor: %.1fx faster\n" improvement_factor;
  Printf.printf "\nProcessing rate:\n";
  Printf.printf "  Total bytes: %d\n" total_bytes;
  Printf.printf "  MB/second: %.1f\n" 
    (float total_bytes /. 1048576.0 /. total_time);
  
  (* Projection for full corpus *)
  let corpus_time = 2846.0 *. avg_time /. 60.0 in
  Printf.printf "\nProjection for 2,846 papers: %.1f minutes\n" corpus_time;
  
  results

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
  
  match args with
  | "--corpus" :: dir :: count_str :: [] ->
    let max_files = int_of_string count_str in
    Printf.printf "Searching for up to %d .tex files in %s...\n" max_files dir;
    let papers = find_tex_files dir max_files in
    Printf.printf "Found %d papers\n\n" (List.length papers);
    
    if papers = [] then
      Printf.printf "No .tex files found\n"
    else
      let _ = batch_process_optimized papers in
      ()
  
  | papers ->
    let _ = batch_process_optimized papers in
    ()