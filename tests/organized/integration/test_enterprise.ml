(**
 * Enterprise Validator Test Program
 * Tests a single paper against all 75 L0 rules
 *)

open Enterprise_validators

let read_file filename =
  let ic = open_in filename in
  let rec loop acc =
    try
      let line = input_line ic in
      loop (line :: acc)
    with End_of_file ->
      close_in ic;
      List.rev acc
  in
  loop []

let string_to_char_list s =
  let rec loop acc i =
    if i < 0 then acc
    else loop (s.[i] :: acc) (i - 1)
  in
  loop [] (String.length s - 1)

let char_list_to_string chars =
  let len = List.length chars in
  let s = Bytes.create len in
  let rec loop i = function
    | [] -> ()
    | c :: rest ->
      Bytes.set s i c;
      loop (i + 1) rest
  in
  loop 0 chars;
  Bytes.to_string s

let validate_paper_file filename =
  try
    let lines = read_file filename in
    let content = String.concat "\n" lines in
    let char_list = string_to_char_list content in
    let tokens = lex char_list in
    let filename_char_list = string_to_char_list filename in
    let doc_state = create_doc_state tokens filename_char_list in
    let issues = validate_document tokens filename_char_list all_l0_rules in
    
    (* Convert issues to JSON format *)
    let json_issues = List.map (fun issue -> 
      Printf.sprintf "{\"rule_id\": \"%s\", \"message\": \"%s\", \"severity\": \"%s\"}" 
        (char_list_to_string issue.rule_id) 
        (char_list_to_string issue.message) 
        (match issue.issue_severity with
          | Warning -> "warning"
          | Error -> "error"
          | Info -> "info"
        )
    ) issues in
    
    let json_output = "[" ^ String.concat ", " json_issues ^ "]" in
    print_endline json_output;
    0
  with
  | Sys_error msg -> 
    Printf.eprintf "Error reading file: %s\n" msg;
    1
  | exn -> 
    Printf.eprintf "Error validating file: %s\n" (Printexc.to_string exn);
    1

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <tex_file>\n" Sys.argv.(0);
    exit 1
  end;
  
  let filename = Sys.argv.(1) in
  exit (validate_paper_file filename)