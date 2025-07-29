(* Real corpus test runner for extracted validators *)

#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "latex_processor.ml";;
#use "validator_runner.ml";;

(* Stats tracking *)
type corpus_stats = {
  mutable files_processed : int;
  mutable total_issues : int;
  mutable issues_by_rule : (string, int) Hashtbl.t;
  mutable processing_time : float;
  mutable errors : int;
}

(* Create initial stats *)
let create_stats () = {
  files_processed = 0;
  total_issues = 0;
  issues_by_rule = Hashtbl.create 20;
  processing_time = 0.0;
  errors = 0;
}

(* Helper to convert string to char list *)
let string_to_chars s =
  let rec explode i acc =
    if i < 0 then acc
    else explode (i - 1) (s.[i] :: acc)
  in
  explode (String.length s - 1) []

(* Helper to convert char list to string *)
let chars_to_string chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Process a single LaTeX file *)
let process_file stats filepath =
  try
    (* Read file content *)
    let ic = open_in filepath in
    let content = 
      try really_input_string ic (in_channel_length ic)
      with _ -> close_in ic; "" in
    close_in ic;
    
    let start_time = Sys.time () in
    
    (* Lex the content *)
    let tokens = lex_string (string_to_chars content) in
    
    (* Create document state *)
    let doc = {
      tokens = tokens;
      expanded_tokens = Some tokens; (* Simplified - no expansion *)
      ast = None;
      semantics = None;
      filename = string_to_chars (Filename.basename filepath);
      doc_layer = L1_Expanded;
    } in
    
    (* Run validators *)
    let issues = run_all_validators doc in
    
    let elapsed = Sys.time () -. start_time in
    
    (* Update stats *)
    stats.files_processed <- stats.files_processed + 1;
    stats.total_issues <- stats.total_issues + List.length issues;
    stats.processing_time <- stats.processing_time +. elapsed;
    
    (* Count issues by rule *)
    List.iter (fun issue ->
      let rule_id = chars_to_string issue.rule_id in
      let count = 
        try Hashtbl.find stats.issues_by_rule rule_id
        with Not_found -> 0 in
      Hashtbl.replace stats.issues_by_rule rule_id (count + 1)
    ) issues;
    
    (* Progress output *)
    if stats.files_processed mod 100 = 0 then
      Printf.printf "  Processed %d files...\r%!" stats.files_processed
      
  with e ->
    stats.errors <- stats.errors + 1;
    if stats.errors <= 10 then
      Printf.eprintf "Error processing %s: %s\n" filepath (Printexc.to_string e)

(* Find all .tex files in directory *)
let rec find_tex_files dir =
  let files = ref [] in
  let rec scan_dir path =
    try
      let entries = Sys.readdir path in
      Array.iter (fun entry ->
        let full_path = Filename.concat path entry in
        if Sys.is_directory full_path then
          scan_dir full_path
        else if Filename.check_suffix entry ".tex" then
          files := full_path :: !files
      ) entries
    with _ -> ()
  in
  scan_dir dir;
  !files

(* Main corpus runner *)
let run_corpus_test corpus_path =
  Printf.printf "🚀 REAL CORPUS VALIDATION TEST\n";
  Printf.printf "==============================\n\n";
  
  let stats = create_stats () in
  
  (* Find all .tex files *)
  Printf.printf "📂 Scanning corpus directory: %s\n" corpus_path;
  let tex_files = find_tex_files corpus_path in
  let total_files = List.length tex_files in
  Printf.printf "📄 Found %d LaTeX files\n\n" total_files;
  
  if total_files = 0 then begin
    Printf.printf "❌ No .tex files found in corpus!\n";
    exit 1
  end;
  
  (* Process files *)
  Printf.printf "🔍 Running validators...\n";
  List.iter (process_file stats) tex_files;
  Printf.printf "\n\n";
  
  (* Display results *)
  Printf.printf "📊 RESULTS\n";
  Printf.printf "==========\n\n";
  Printf.printf "Files processed: %d\n" stats.files_processed;
  Printf.printf "Total issues found: %d\n" stats.total_issues;
  Printf.printf "Processing errors: %d\n" stats.errors;
  Printf.printf "Total time: %.2fs\n" stats.processing_time;
  Printf.printf "Avg time per file: %.2fms\n" 
    (stats.processing_time *. 1000.0 /. float_of_int stats.files_processed);
  
  Printf.printf "\n📈 Issues by rule:\n";
  let rules = Hashtbl.fold (fun k v acc -> (k, v) :: acc) stats.issues_by_rule [] in
  let sorted_rules = List.sort (fun (_, a) (_, b) -> compare b a) rules in
  List.iter (fun (rule, count) ->
    Printf.printf "  %s: %d\n" rule count
  ) sorted_rules;
  
  Printf.printf "\n✅ Corpus validation complete!\n"

(* Entry point *)
let () =
  let corpus_path = 
    if Array.length Sys.argv > 1 then
      Sys.argv.(1)
    else
      "corpus" (* Default corpus directory *)
  in
  run_corpus_test corpus_path