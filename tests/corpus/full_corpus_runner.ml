(* Full corpus runner with performance metrics *)

#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Helper functions *)
let s2c s = 
  let rec explode i acc =
    if i < 0 then acc else explode (i - 1) (s.[i] :: acc)
  in explode (String.length s - 1) []

let c2s chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Simple but fast tokenizer *)
let tokenize_fast content =
  let tokens = ref [] in
  let i = ref 0 in
  let len = String.length content in
  
  while !i < len do
    match content.[!i] with
    | '\\' ->
        let j = ref (!i + 1) in
        while !j < len && 
              let c = content.[!j] in
              (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') do
          incr j
        done;
        if !j > !i + 1 then begin
          let cmd = String.sub content (!i + 1) (!j - !i - 1) in
          tokens := TCommand (s2c cmd) :: !tokens;
          i := !j
        end else begin
          incr i
        end
    | '{' -> tokens := TBeginGroup :: !tokens; incr i
    | '}' -> tokens := TEndGroup :: !tokens; incr i
    | '$' -> tokens := TMathShift :: !tokens; incr i
    | '^' -> tokens := TSuperscript :: !tokens; incr i
    | '_' -> tokens := TSubscript :: !tokens; incr i
    | '\n' -> tokens := TNewline :: !tokens; incr i
    | ' ' | '\t' -> tokens := TSpace :: !tokens; incr i
    | _ -> 
        let j = ref (!i + 1) in
        while !j < len && 
              let c = content.[!j] in
              c <> '\\' && c <> '{' && c <> '}' && c <> '$' && 
              c <> '^' && c <> '_' && c <> '\n' && c <> ' ' && c <> '\t' do
          incr j
        done;
        let text = String.sub content !i (!j - !i) in
        tokens := TText (s2c text) :: !tokens;
        i := !j
  done;
  
  List.rev !tokens

(* Find all .tex files recursively *)
let find_all_tex_files root =
  let files = ref [] in
  let rec walk dir =
    try
      let entries = Sys.readdir dir in
      Array.iter (fun entry ->
        let path = Filename.concat dir entry in
        try
          if Sys.is_directory path then
            walk path
          else if Filename.check_suffix entry ".tex" then
            files := path :: !files
        with _ -> ()
      ) entries
    with _ -> ()
  in
  walk root;
  !files

(* Process a single file *)
let process_tex_file file =
  try
    let ic = open_in file in
    let size = in_channel_length ic in
    if size > 1_000_000 then begin
      (* Skip very large files *)
      close_in ic;
      (0, 0.0, Some "File too large")
    end else begin
      let content = really_input_string ic size in
      close_in ic;
      
      let start = Sys.time () in
      let tokens = tokenize_fast content in
      
      let doc = {
        tokens = tokens;
        expanded_tokens = Some tokens;
        ast = None;
        semantics = None;
        filename = s2c (Filename.basename file);
        doc_layer = L1_Expanded;
      } in
      
      let issues = run_all_validators doc in
      let elapsed = Sys.time () -. start in
      
      (List.length issues, elapsed, None)
    end
  with e ->
    (0, 0.0, Some (Printexc.to_string e))

(* Main runner *)
let run_full_corpus corpus_path max_files =
  Printf.printf "🚀 FULL CORPUS VALIDATION\n";
  Printf.printf "========================\n\n";
  
  (* Find files *)
  Printf.printf "📂 Scanning %s...\n" corpus_path;
  let all_files = find_all_tex_files corpus_path in
  let total_found = List.length all_files in
  Printf.printf "📄 Found %d .tex files\n" total_found;
  
  (* Limit files if requested *)
  let files_to_process = 
    match max_files with
    | Some n when n < total_found -> 
        Printf.printf "🎯 Processing first %d files\n" n;
        let rec take n = function
          | [] -> []
          | _ when n <= 0 -> []
          | h::t -> h :: take (n-1) t
        in take n all_files
    | _ -> all_files
  in
  
  Printf.printf "\n🔍 Running validators...\n";
  
  (* Stats *)
  let processed = ref 0 in
  let total_issues = ref 0 in
  let total_time = ref 0.0 in
  let errors = ref 0 in
  let issues_by_rule = Hashtbl.create 20 in
  
  (* Process files *)
  List.iter (fun file ->
    incr processed;
    if !processed mod 100 = 0 then
      Printf.printf "  Progress: %d/%d files...\r%!" !processed (List.length files_to_process);
    
    match process_tex_file file with
    | (count, time, None) ->
        total_issues := !total_issues + count;
        total_time := !total_time +. time
    | (_, _, Some err) ->
        incr errors;
        if !errors <= 5 then
          Printf.eprintf "\nError in %s: %s\n" (Filename.basename file) err
  ) files_to_process;
  
  Printf.printf "\n\n📊 RESULTS\n";
  Printf.printf "==========\n\n";
  Printf.printf "Files processed: %d\n" !processed;
  Printf.printf "Total issues: %d\n" !total_issues;
  Printf.printf "Files with errors: %d\n" !errors;
  Printf.printf "Total time: %.2fs\n" !total_time;
  Printf.printf "Avg time/file: %.2fms\n" (!total_time *. 1000.0 /. float_of_int !processed);
  Printf.printf "Issues/file: %.1f\n" (float_of_int !total_issues /. float_of_int !processed);
  
  (* Performance check *)
  let avg_ms = !total_time *. 1000.0 /. float_of_int !processed in
  if avg_ms < 42.0 then
    Printf.printf "\n✅ PERFORMANCE: Meeting 42ms SLA (%.2fms avg)\n" avg_ms
  else
    Printf.printf "\n⚠️  PERFORMANCE: Exceeding 42ms SLA (%.2fms avg)\n" avg_ms;
    
  Printf.printf "\n🎉 Corpus validation complete!\n"

(* Entry point *)
let () =
  let corpus_path = "corpus" in
  let max_files = 
    if Array.length Sys.argv > 1 then
      Some (int_of_string Sys.argv.(1))
    else
      Some 1000 (* Default to 1000 files for testing *)
  in
  run_full_corpus corpus_path max_files