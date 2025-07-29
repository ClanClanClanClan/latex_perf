(* CARC Parser Module - Simple YAML Rule Parser *)
(* Parsing rules_unified.yaml into AST using basic string processing *)

open Ast

exception Parse_error of string

let extract_field line field_name =
  if String.contains line ':' then
    let parts = String.split_on_char ':' line in
    match parts with
    | key :: value_parts ->
        let key_clean = String.trim key in
        (* Handle both "field_name:" and "- field_name:" formats *)
        let key_matches = 
          key_clean = field_name || 
          key_clean = ("- " ^ field_name) in
        if key_matches then
          let value = String.concat ":" value_parts in
          let value_clean = String.trim value in
          (* Remove quotes if present *)
          if String.length value_clean >= 2 && 
             value_clean.[0] = '"' && 
             value_clean.[String.length value_clean - 1] = '"' then
            String.sub value_clean 1 (String.length value_clean - 2)
          else if value_clean = "null" then
            ""
          else
            value_clean
        else
          ""
    | _ -> ""
  else
    ""

let parse_rule_block lines =
  let id = ref "" in
  let description = ref "" in
  let precondition = ref "L0_Lexer" in
  let severity = ref "Info" in
  let maturity = ref "Draft" in
  let owner = ref "unknown" in
  let fix = ref None in
  
  List.iter (fun line ->
    let line_clean = String.trim line in
    if line_clean <> "" && not (String.length line_clean > 0 && line_clean.[0] = '#') then (
      let id_val = extract_field line_clean "id" in
      if id_val <> "" then id := id_val;
      
      let desc_val = extract_field line_clean "description" in
      if desc_val <> "" then description := desc_val;
      
      let precond_val = extract_field line_clean "precondition" in
      if precond_val <> "" then precondition := precond_val;
      
      let sev_val = extract_field line_clean "default_severity" in
      if sev_val <> "" then severity := sev_val;
      
      let mat_val = extract_field line_clean "maturity" in
      if mat_val <> "" then maturity := mat_val;
      
      let owner_val = extract_field line_clean "owner" in
      if owner_val <> "" then owner := owner_val;
      
      let fix_val = extract_field line_clean "fix" in
      if fix_val <> "" && fix_val <> "null" then fix := Some fix_val;
    )
  ) lines;
  
  if !id = "" then
    None
  else
    try
      Some {
        id = !id;
        description = !description;
        precondition = precondition_of_string !precondition;
        default_severity = severity_of_string !severity;
        maturity = maturity_of_string !maturity;
        owner = !owner;
        fix = !fix;
        classification = None;
        confidence = None;
        pattern_analysis = [];
      }
    with
    | Failure msg -> 
        Printf.eprintf "Warning: Failed to parse rule %s: %s\n" !id msg;
        None

let parse_rules_file filename =
  try
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    let lines = String.split_on_char '\n' content in
    let rec parse_rules acc current_rule_lines = function
      | [] -> 
          if current_rule_lines <> [] then
            match parse_rule_block (List.rev current_rule_lines) with
            | Some rule -> rule :: acc
            | None -> acc
          else acc
      | line :: rest ->
          let line_clean = String.trim line in
          if String.length line_clean >= 2 && String.sub line_clean 0 2 = "- " then
            (* Start of new rule *)
            let acc' = 
              if current_rule_lines <> [] then
                match parse_rule_block (List.rev current_rule_lines) with
                | Some rule -> rule :: acc
                | None -> acc
              else acc
            in
            parse_rules acc' [line] rest
          else
            (* Continue current rule *)
            parse_rules acc (line :: current_rule_lines) rest
    in
    
    let rules = parse_rules [] [] lines in
    List.rev rules
    
  with
  | Sys_error msg -> 
      raise (Parse_error ("File error: " ^ msg))
  | e -> 
      raise (Parse_error ("Unexpected error: " ^ Printexc.to_string e))

let validate_rules rules =
  let ids = List.map (fun r -> r.id) rules in
  let unique_ids = List.sort_uniq String.compare ids in
  
  if List.length ids <> List.length unique_ids then (
    Printf.eprintf "Warning: Found duplicate rule IDs\n";
    let duplicates = 
      List.filter (fun id ->
        List.length (List.filter (String.equal id) ids) > 1
      ) unique_ids
    in
    List.iter (fun id -> Printf.eprintf "  Duplicate ID: %s\n" id) duplicates
  );
  
  (* Validate required fields *)
  List.iter (fun rule ->
    if rule.id = "" then
      Printf.eprintf "Warning: Rule with empty ID found\n";
    if rule.description = "" then
      Printf.eprintf "Warning: Rule %s has empty description\n" rule.id;
  ) rules;
  
  Printf.printf "Validation complete: %d rules loaded\n" (List.length rules);
  rules