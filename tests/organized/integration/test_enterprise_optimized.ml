(**
 * High-Performance Enterprise Validator
 * Optimized for 2,846 paper corpus validation
 *)

open Enterprise_validators

(* Efficient string/char list conversions *)
let string_to_char_list_fast s =
  let len = String.length s in
  let rec loop acc i =
    if i < 0 then acc
    else loop (s.[i] :: acc) (i - 1)
  in
  loop [] (len - 1)

let char_list_to_string_fast chars =
  let len = List.length chars in
  let bytes = Bytes.create len in
  let rec loop i = function
    | [] -> ()
    | c :: rest ->
      Bytes.set bytes i c;
      loop (i + 1) rest
  in
  loop 0 chars;
  Bytes.to_string bytes

(* Batch processing for multiple papers *)
let process_papers_batch papers =
  let results = ref [] in
  List.iter (fun paper_path ->
    try
      let content = 
        let ic = open_in paper_path in
        let content = really_input_string ic (in_channel_length ic) in
        close_in ic;
        content
      in
      
      (* Fast conversions *)
      let char_list = string_to_char_list_fast content in
      let filename_chars = string_to_char_list_fast paper_path in
      
      (* Single tokenization *)
      let tokens = lex char_list in
      let doc_state = create_doc_state tokens filename_chars in
      
      (* Efficient rule execution *)
      let issues = validate_document tokens filename_chars all_l0_rules in
      
      (* Minimal JSON creation *)
      let json_issues = List.map (fun issue -> 
        Printf.sprintf "{\"rule_id\":\"%s\",\"severity\":\"%s\"}" 
          (char_list_to_string_fast issue.rule_id)
          (match issue.issue_severity with
            | Error -> "error"
            | Warning -> "warning" 
            | Info -> "info")
      ) issues in
      
      results := (paper_path, json_issues, List.length issues) :: !results
    with
    | exn -> 
      results := (paper_path, [], -1) :: !results
  ) papers;
  List.rev !results

(* High-performance main function *)
let validate_papers_fast paper_paths =
  let start_time = Unix.gettimeofday () in
  let results = process_papers_batch paper_paths in
  let end_time = Unix.gettimeofday () in
  
  let total_papers = List.length results in
  let successful = List.length (List.filter (fun (_, _, count) -> count >= 0) results) in
  let total_issues = List.fold_left (fun acc (_, _, count) -> acc + max 0 count) 0 results in
  let processing_time = end_time -. start_time in
  
  (* Efficient JSON output *)
  Printf.printf "{\n";
  Printf.printf "  \"total_papers\": %d,\n" total_papers;
  Printf.printf "  \"successful_validations\": %d,\n" successful;
  Printf.printf "  \"total_issues\": %d,\n" total_issues;
  Printf.printf "  \"processing_time\": %.3f,\n" processing_time;
  Printf.printf "  \"avg_time_per_paper\": %.3f,\n" (processing_time /. float total_papers);
  Printf.printf "  \"papers_per_second\": %.1f,\n" (float total_papers /. processing_time);
  Printf.printf "  \"results\": [\n";
  
  let rec print_results = function
    | [] -> ()
    | [(path, issues, count)] ->
      Printf.printf "    {\"paper\": \"%s\", \"issues\": %d, \"status\": \"%s\"}\n"
        path count (if count >= 0 then "success" else "failed")
    | (path, issues, count) :: rest ->
      Printf.printf "    {\"paper\": \"%s\", \"issues\": %d, \"status\": \"%s\"},\n"
        path count (if count >= 0 then "success" else "failed");
      print_results rest
  in
  print_results results;
  Printf.printf "  ]\n}\n"

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    exit 1
  end;
  
  let papers = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  validate_papers_fast papers