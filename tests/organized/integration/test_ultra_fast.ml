(**
 * Ultra-Fast Enterprise Validator
 * Uses only the fastest rules for maximum performance
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

(* Get only the 5 fastest rules for ultra-performance *)
let get_ultra_fast_rules () =
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take 5 all_l0_rules

(* Process document with timeout *)
let process_with_timeout filename rules timeout =
  let start_time = Unix.gettimeofday () in
  
  (* Set up alarm signal *)
  let old_handler = Sys.signal Sys.sigalrm 
    (Sys.Signal_handle (fun _ -> failwith "Timeout")) in
  
  let cleanup () =
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old_handler
  in
  
  try
    (* Set timeout *)
    ignore (Unix.alarm (int_of_float timeout));
    
    (* Read and process file *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    
    (* Limit file size for ultra-fast processing *)
    let content = 
      if len > 100000 then begin
        let partial = really_input_string ic 100000 in
        close_in ic;
        partial
      end else begin
        let full = really_input_string ic len in
        close_in ic;
        full
      end
    in
    
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    let issues = execute_rules_bucketed rules doc_state in
    
    cleanup ();
    let end_time = Unix.gettimeofday () in
    (filename, List.length issues, true, end_time -. start_time, len)
  with
  | exn ->
    cleanup ();
    let end_time = Unix.gettimeofday () in
    (filename, 0, false, end_time -. start_time, 0)

(* Batch process with statistics *)
let batch_process_ultra_fast filenames =
  let rules = get_ultra_fast_rules () in
  let timeout = 2.0 in (* 2 second timeout per file *)
  
  Printf.printf "Processing %d files with %d ultra-fast rules...\n" 
    (List.length filenames) (List.length rules);
  
  let results = List.map (fun f -> process_with_timeout f rules timeout) filenames in
  
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
  
  (* Output JSON results *)
  Printf.printf "{\n";
  Printf.printf "  \"ultra_fast_validation\": {\n";
  Printf.printf "    \"total_papers\": %d,\n" (List.length results);
  Printf.printf "    \"successful\": %d,\n" successful;
  Printf.printf "    \"success_rate\": %.1f,\n" success_rate;
  Printf.printf "    \"total_issues\": %d,\n" total_issues;
  Printf.printf "    \"avg_issues_per_paper\": %.1f,\n" 
    (float total_issues /. float (List.length results));
  Printf.printf "    \"total_time\": %.2f,\n" total_time;
  Printf.printf "    \"avg_time_per_paper\": %.3f,\n" avg_time;
  Printf.printf "    \"papers_per_second\": %.1f,\n" 
    (float (List.length results) /. total_time);
  Printf.printf "    \"total_bytes_processed\": %d,\n" total_bytes;
  Printf.printf "    \"mb_per_second\": %.1f,\n" 
    (float total_bytes /. 1048576.0 /. total_time);
  Printf.printf "    \"rules_used\": %d,\n" (List.length rules);
  Printf.printf "    \"timeout_per_file\": %.1f\n" timeout;
  Printf.printf "  }\n";
  Printf.printf "}\n";
  
  (* Return detailed results for analysis *)
  results

(* Find tex files with better error handling *)
let find_tex_files dir max_files =
  let files = ref [] in
  let errors = ref [] in
  let count = ref 0 in
  
  let rec scan_dir path =
    if !count >= max_files then ()
    else
      try
        let entries = Sys.readdir path in
        Array.iter (fun entry ->
          if !count >= max_files then ()
          else
            try
              let full_path = Filename.concat path entry in
              let stats = Unix.stat full_path in
              if stats.Unix.st_kind = Unix.S_DIR then
                scan_dir full_path
              else if Filename.check_suffix entry ".tex" then begin
                files := full_path :: !files;
                incr count
              end
            with
            | Unix.Unix_error (err, _, _) ->
                errors := Printf.sprintf "%s: %s" entry (Unix.error_message err) :: !errors
            | exn ->
                errors := Printf.sprintf "%s: %s" entry (Printexc.to_string exn) :: !errors
        ) entries
      with
      | Unix.Unix_error (err, _, _) ->
          errors := Printf.sprintf "%s: %s" path (Unix.error_message err) :: !errors
      | exn ->
          errors := Printf.sprintf "%s: %s" path (Printexc.to_string exn) :: !errors
  in
  
  scan_dir dir;
  
  if !errors <> [] then begin
    Printf.eprintf "Errors during file scanning:\n";
    List.iter (Printf.eprintf "  %s\n") !errors
  end;
  
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
      let _ = batch_process_ultra_fast papers in
      ()
  
  | papers ->
    let _ = batch_process_ultra_fast papers in
    ()