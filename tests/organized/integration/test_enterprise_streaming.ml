(**
 * Streaming Enterprise Validator
 * Processes papers in streaming batches for maximum throughput
 *)

open Enterprise_validators

(* Get first 10 rules from all_l0_rules for speed *)
let get_priority_rules () = 
  let rec take n lst =
    match n, lst with
    | 0, _ -> []
    | _, [] -> []
    | n, x :: xs -> x :: take (n-1) xs
  in
  take 10 all_l0_rules

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

(* Streaming paper processor *)
let process_paper_stream filename =
  try
    (* Fast file reading *)
    let ic = open_in filename in
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    
    (* Efficient tokenization *)
    let tokens = lex (string_to_chars content) in
    let doc_state = create_doc_state tokens (string_to_chars filename) in
    
    (* Fast rule execution - only high priority *)
    let priority_rules = get_priority_rules () in
    let issues = execute_rules_bucketed priority_rules doc_state in
    
    (* Minimal issue counting *)
    let issue_count = List.length issues in
    (filename, issue_count, 0.0, true)
  with
  | exn -> (filename, 0, 0.0, false)

(* Batch streaming processor *)
let process_batch_stream filenames =
  let results = Array.make (List.length filenames) ("", 0, 0.0, false) in
  let start_time = Unix.gettimeofday () in
  
  List.iteri (fun i filename ->
    let (name, issues, time, success) = process_paper_stream filename in
    results.(i) <- (name, issues, Unix.gettimeofday () -. start_time, success)
  ) filenames;
  
  results

(* Ultra-fast JSON output *)
let output_results_fast results =
  let total = Array.length results in
  let successful = Array.fold_left (fun acc (_, _, _, success) -> 
    if success then acc + 1 else acc) 0 results in
  let total_issues = Array.fold_left (fun acc (_, issues, _, _) -> 
    acc + issues) 0 results in
  let total_time = if total > 0 then 
    let (_, _, last_time, _) = results.(total - 1) in last_time
  else 0.0 in
  
  Printf.printf "{\"total\":%d,\"successful\":%d,\"issues\":%d,\"time\":%.3f,\"rate\":%.1f}\n"
    total successful total_issues total_time 
    (if total_time > 0.0 then float total /. total_time else 0.0)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <paper1.tex> [paper2.tex] ...\n" Sys.argv.(0);
    exit 1
  end;
  
  let papers = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  let results = process_batch_stream papers in
  output_results_fast results